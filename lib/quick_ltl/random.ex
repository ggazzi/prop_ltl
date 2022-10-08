defmodule QuickLTL.Random do
  import PropCheck
  import PropCheck.BasicTypes
  alias QuickLTL.Syntax

  defmodule Env do
    @var_kinds [:boolean]
    defstruct @var_kinds

    def new() do
      struct(
        __MODULE__,
        for kind <- @var_kinds do
          {kind, MapSet.new()}
        end
      )
    end

    def add_binders(env, binders) do
      for {kind, name, _binder} <- binders, reduce: env do
        env -> %{env | kind => MapSet.put(Map.get(env, kind), name)}
      end
    end

    def has_var?(env, kind) do
      not Enum.empty?(Map.get(env, kind))
    end

    def var(env, kind) do
      elements(Map.get(env, kind) |> Enum.to_list())
    end

    def vars(env, kind) do
      Map.get(env, kind)
    end

    def vars(env) do
      for kind <- @var_kinds, reduce: MapSet.new() do
        acc -> MapSet.union(acc, Map.get(env, kind))
      end
    end

    def global() do
      noshrink(
        frequency([
          {1, exactly(new())},
          {9,
           let vars_boolean <- shrink_list(Enum.map(?p..?t, &List.to_atom([&1]))) do
             %__MODULE__{boolean: MapSet.new(vars_boolean)}
           end}
        ])
      )
    end

    def state(env) do
      generators = %{boolean: boolean()}

      assignments =
        for kind <- @var_kinds, var <- Env.vars(env, kind) do
          {var, generators[kind]}
        end

      let state <- assignments do
        Map.new(state)
      end
    end

    def trace(env) do
      sized(size, resize(size + 20, non_empty(list(state(env)))))
    end
  end

  defdelegate state(env), to: Env
  defdelegate trace(env), to: Env

  def proposition(global_env) do
    # We expose a lazy wrapper to ensure that parameters are available for generation
    let ast <- lazy(sized(size, prop(size, global_env))) do
      %QuickLTL{ast: ast}
    end
  end

  @spec collect_metric(PropCheck.test(), term, number(), integer()) :: :proper.test()
  def collect_metric(property, label, metric, bucket_size) do
    bucket =
      if metric == :infinity do
        :infinity
      else
        bucket_start = trunc(metric / bucket_size) * bucket_size
        bucket_start..(bucket_start + bucket_size)
      end

    collect(property, {label, bucket})
  end

  defp prop(0, env), do: atomic_prop(0, env)

  defp prop(size, env) do
    frequency([
      # Atomic
      {1, atomic_prop(size, env)},

      # Logical connectives
      {2,
       lazy(
         let_shrink [p <- prop(size - 1, env)] do
           {:not, p}
         end
       )},
      {4,
       lazy(
         let_shrink [p1 <- prop(div(size, 2), env), p2 <- prop(div(size, 2), env)] do
           {elements([:and, :or, :implies]), p1, p2}
         end
       )},

      # Temporal connectives
      {2,
       lazy(
         let_shrink [p <- prop(size - 1, env)] do
           oneof([{:next, :weak, p}, {:next, :strong, p}, {:always, p}, {:eventually, p}])
         end
       )},
      {2,
       lazy(
         let_shrink [p1 <- prop(div(size, 2), env), p2 <- prop(div(size, 2), env)] do
           {:until, elements([:weak, :strong]), p1, p2}
         end
       )},

      # Binders
      {1, lazy(prop_let(size, env))}
    ])
  end

  defp prop_let(size, outer_env) do
    let num_binders <- noshrink(choose(1, max(1, min(10, size)))) do
      body_size = div(size, 2)
      binder_size = div(body_size, num_binders)

      let [
        binders_all <-
          noshrink(Enum.map(1..num_binders, fn _ -> binder(binder_size, outer_env) end)),
        binders <- non_empty(shrink_list(^binders_all)),
        body <- noshrink(prop(body_size, Env.add_binders(outer_env, ^binders)))
      ] do
        {:let, Enum.map(binders, fn {_, var, binder} -> {var, binder} end), body}
      end
    end
  end

  defp binder(size, env) do
    {:boolean, var_name(), native_expr_boolean(size, env, allow_boolean_constants: true)}
  end

  def var_name() do
    mid_char = oneof([?_, choose(?a, ?z), choose(?A, ?Z), choose(?0, ?9)])

    let [fst <- choose(?a, ?z), rest <- list(mid_char)] do
      List.to_atom([fst | rest])
    end
  end

  defp atomic_prop(size, env) do
    noshrink(
      oneof(
        [
          boolean(),
          native_expr_boolean(size, env)
        ]
        |> Enum.filter(&(nil != &1))
      )
    )
  end

  defp native_expr_boolean(size, env, opts \\ []) do
    case native_expr_boolean_ast(size, env, opts) do
      nil ->
        nil

      ast_gen ->
        let ast <- ast_gen do
          native_expr =
            ast |> Syntax.compile_native_expr(make_custom_env()) |> Code.eval_quoted() |> elem(0)

          {:expr, native_expr}
        end
    end
  end

  defp native_expr_boolean_ast(_size, env, opts) do
    var =
      if Env.has_var?(env, :boolean) do
        let var_name <- Env.var(env, :boolean) do
          Macro.var(var_name, :__TEST__)
        end
      end

    const =
      if opts[:allow_boolean_constants] do
        boolean()
      end

    case [var, const] |> Enum.filter(&(nil != &1)) do
      [] -> nil
      options -> oneof(options)
    end
  end

  def make_custom_env do
    __ENV__
  end
end
