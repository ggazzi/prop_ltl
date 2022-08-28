defmodule QuickLTL.Syntax do
  @moduledoc """
  Syntax of the QuickLTL logic built on top of the Elixir syntax.

  In this library, we implement a dialect of the QuickLTL logic on top of
  Elixir syntax. We provide the appropriate datatypes as well as functions
  converting to and from Elixir quotes.
  """
  @typedoc """
  A proposition in QuickLTL.
  """

  @type t ::
          boolean()
          | atomic
          | {:let, Keyword.t(binder), t}
          | {:not, t}
          | {:and, t, t}
          | {:or, t, t}
          | {:implies, t, t}
          | {:next, :weak | :strong, t}
          | {:always, t}
          | {:eventually, t}
          | {:until, t, t}
          | {:weak_until, t, t}

  @typedoc """
  An atomic proposition.
  Must correspond to an Elixir expression that evaluates to a boolean.
  """
  @type atomic :: {:expr, native_expr(boolean())}

  @typedoc """
  Embedding of a native Elixir expression into the QuickLTL syntax.

  Contains the quoted Elixir syntax for the purposes of pretty-printing,
  as well as a compiled evaluation function.
  """
  @type native_expr(t) :: {(QuickLTL.state(), QuickLTL.env() -> t), Macro.input()}

  @type binder :: {:expr, native_expr(term)} | {:val, term}

  @typedoc """
  A QuickLTL proposition where temporal operators are guarded by the next operator.
  """
  @type guarded ::
          boolean()
          | atomic
          | {:let, Keyword.t(binder), guarded}
          | {:not, guarded}
          | {:and, guarded, guarded}
          | {:or, guarded, guarded}
          | {:implies, guarded, guarded}
          | {:next, :weak | :strong, t}

  @spec compile_proposition(Macro.input(), Macro.Env.t()) :: Macro.output()
  @doc """
  Transform a quoted QuickLTL proposition into its AST.

  For more information of the expected syntax, see `QuickLTL.prop/1`.
  """
  def compile_proposition(true, _) do
    true
  end

  def compile_proposition(false, _) do
    false
  end

  def compile_proposition([do: prop], macro_env) do
    compile_proposition(prop, macro_env)
  end

  def compile_proposition({:__block__, _, [prop]}, macro_env) do
    compile_proposition(prop, macro_env)
  end

  def compile_proposition({:not, _opts, [prop]}, macro_env) do
    quote do: {:not, unquote(compile_proposition(prop, macro_env))}
  end

  def compile_proposition({:and, _opts, [prop1, prop2]}, macro_env) do
    quote do
      {:and, unquote(compile_proposition(prop1, macro_env)),
       unquote(compile_proposition(prop2, macro_env))}
    end
  end

  def compile_proposition({:or, _opts, [prop1, prop2]}, macro_env) do
    quote do
      {:or, unquote(compile_proposition(prop1, macro_env)),
       unquote(compile_proposition(prop2, macro_env))}
    end
  end

  def compile_proposition({:if, _opts, [prop1, [do: prop2]]}, macro_env) do
    quote do
      {:implies, unquote(compile_proposition(prop1, macro_env)),
       unquote(compile_proposition(prop2, macro_env))}
    end
  end

  def compile_proposition({:next_weak, _opts, [prop]}, macro_env) do
    quote do: {:next, :weak, unquote(compile_proposition(prop, macro_env))}
  end

  def compile_proposition({:next_strong, _opts, [prop]}, macro_env) do
    quote do: {:next, :strong, unquote(compile_proposition(prop, macro_env))}
  end

  def compile_proposition({:always, _opts, [prop]}, macro_env) do
    quote do: {:always, unquote(compile_proposition(prop, macro_env))}
  end

  def compile_proposition({:eventually, _opts, [prop]}, macro_env) do
    quote do: {:eventually, unquote(compile_proposition(prop, macro_env))}
  end

  def compile_proposition({:until, _opts, [prop1, prop2]}, macro_env) do
    quote do
      {:until, unquote(compile_proposition(prop1, macro_env)),
       unquote(compile_proposition(prop2, macro_env))}
    end
  end

  def compile_proposition({:weak_until, _opts, [prop1, prop2]}, macro_env) do
    quote do
      {:weak_until, unquote(compile_proposition(prop1, macro_env)),
       unquote(compile_proposition(prop2, macro_env))}
    end
  end

  def compile_proposition({:_, _, context} = wildcard, _macro_env) when is_atom(context) do
    wildcard
  end

  def compile_proposition({:^, _, _} = pin, _macro_env) do
    pin
  end

  def compile_proposition({:&, _, [ast]}, _macro_env) do
    ast
  end

  def compile_proposition({:let, _, [{:=, _, [{name, _, context}, expr]}]}, macro_env)
      when is_atom(name) and is_atom(context) do
    quote do
      # TODO: remove
      {:let, unquote(compile_binders([{name, expr}], macro_env)), :illegal}
    end
  end

  def compile_proposition({:let, _, [binders, [do: expr]]}, macro_env) do
    quote do
      {:let, unquote(compile_binders(binders, macro_env)),
       unquote(compile_proposition(expr, macro_env))}
    end
  end

  def compile_proposition({:let, meta, [args]}, macro_env) do
    {expr, binders} = Keyword.pop(args, :do)
    compile_proposition({:let, meta, [binders, [do: expr]]}, macro_env)
  end

  def compile_proposition(expr, macro_env) do
    quote do: {:expr, unquote(compile_native_expr(expr, macro_env))}
  end

  defp compile_binders(binders, macro_env) do
    for {name, expr} <- binders do
      binder =
        case expr do
          {:&, _, [raw_expr]} -> raw_expr
          {:^, _, [_]} = pin -> pin
          {:_, _, context} when is_atom(context) -> expr
          _ -> {:expr, compile_native_expr(expr, macro_env)}
        end

      quote do: {unquote(name), unquote(binder)}
    end
  end

  @spec compile_native_expr(Macro.input(), Macro.Env.t()) :: Macro.output()
  @doc """
  Produce an evaluator for an Elixir expression used as part of a proposition.

  This expression is to be interpreted in a logical `t:env/0` that is put
  on top of the usual Elixir variable scope.  That is, any free variables
  of the expression should be looked up at evaluation time.
  """
  defp compile_native_expr(expr, macro_env) do
    expr = Macro.expand(expr, macro_env)

    evaluator =
      if macro_env.context == :match do
        quote do: _
      else
        outer_vars = Macro.Env.vars(macro_env)
        state_var = Macro.unique_var(:state, __MODULE__)
        env_var = Macro.unique_var(:env, __MODULE__)

        lookups =
          for {name, _, _} = var <- collect_vars(expr),
              var_context(var) not in outer_vars do
            quote do
              unquote(var) =
                Map.get_lazy(unquote(env_var), unquote(name), fn ->
                  Map.get(unquote(state_var), unquote(name))
                end)
            end
          end

        quote do
          fn unquote(state_var), unquote(env_var) ->
            unquote_splicing(lookups)
            unquote(expr)
          end
        end
      end

    quote do: {unquote(evaluator), unquote(Macro.escape(expr))}
  end

  @spec collect_vars(Macro.output()) :: MapSet.t()
  defp collect_vars(ast) do
    Macro.prewalk(ast, MapSet.new(), fn
      {skip, _, [_]}, acc when skip in [:^, :@] ->
        {:ok, acc}

      {:_, _, context}, acc when is_atom(context) ->
        {:ok, acc}

      {name, _, context} = var, acc when is_atom(name) and is_atom(context) ->
        {:ok, MapSet.put(acc, var)}

      node, acc ->
        {node, acc}
    end)
    |> elem(1)
  end

  defp var_context({name, meta, context}) do
    {name, meta[:counter] || context}
  end
end
