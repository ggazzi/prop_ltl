defmodule QuickLTL.Syntax do
  @moduledoc """
  Syntax of the QuickLTL logic built on top of the Elixir syntax.

  In this library, we implement a dialect of the QuickLTL logic on top of
  Elixir syntax. This module provides the appropriate datatypes as well as functions
  converting to and from Elixir quotes.

  __NOTE:__ the internal representation of propositions is __unstable__
  and should therefore __not__ be manipulated directly by users of this library.
  """

  @typedoc """
  A proposition in QuickLTL.
  """
  @type t ::
          boolean()
          | {:expr, native_expr(boolean())}
          | {:let, Keyword.t(binder), t}
          | {:recv, native_recv}
          | {:recv, native_recv, t}
          | {:if_recv, native_recv, t}
          | {:not, t}
          | {:and, t, t}
          | {:or, t, t}
          | {:implies, t, t}
          | {:next, :weak | :strong, t}
          | {:always, t}
          | {:eventually, t}
          | {:until, :weak | :strong, t, t}

  @typedoc """
  Embedding of a native Elixir expression into the QuickLTL syntax.

  Contains the quoted Elixir syntax for the purposes of pretty-printing,
  as well as a compiled evaluation function.
  """
  @type native_expr(t) :: {(QuickLTL.state(), QuickLTL.env() -> t), Macro.input()}

  @typedoc """
  Embedding of a native Elixir `receive`-block into the QuickLTL syntax.

  Contains the quoted Elixir pattern for the purposes of pretty-printing,
  as well as a compiled evaluation function.
  """
  @type native_recv ::
          {(QuickLTL.state(), QuickLTL.env() -> {:received, keyword} | :not_received),
           Macro.input()}

  @type binder :: {:expr, native_expr(term)} | {:val, term}

  @typedoc """
  A QuickLTL proposition where temporal operators are guarded by the next operator.
  """
  @type guarded ::
          boolean()
          | {:expr, native_expr(boolean)}
          | {:let, Keyword.t(binder), guarded}
          | {:recv, native_recv}
          | {:recv, native_recv, guarded}
          | {:if_recv, native_recv, guarded}
          | {:not, guarded}
          | {:and, guarded, guarded}
          | {:or, guarded, guarded}
          | {:implies, guarded, guarded}
          | {:next, :weak | :strong, t}

  def atomic?(%QuickLTL{ast: ast}), do: atomic?(ast)
  def atomic?(p) when is_boolean(p), do: true
  def atomic?({:expr, {eval, ast}}), do: is_function(eval, 2) and Macro.validate(ast) == :ok
  def atomic?({:recv, {eval, ast}}), do: is_function(eval, 2) and Macro.validate(ast) == :ok
  def atomic(_), do: false

  def guarded?(%QuickLTL{ast: ast}), do: guarded?(ast)
  def guarded?({:let, _binders, p}), do: guarded?(p)

  def guarded?({recv, {eval, ast}, p}) when recv in [:recv, :if_recv] do
    is_function(eval, 2) and Macro.validate(ast) == :ok and guarded?(p)
  end

  def guarded?({:not, p}), do: guarded?(p)
  def guarded?({op, p1, p2}) when op in [:and, :or, :implies], do: guarded?(p1) and guarded?(p2)
  def guarded?({:next, s, p}) when s in [:weak, :strong], do: valid?(p)
  def guarded?(p), do: atomic?(p)

  def valid?(%QuickLTL{ast: ast}), do: valid?(ast)
  def valid?({:let, _binders, p}), do: valid?(p)

  def valid?({recv, {eval, ast}, p}) when recv in [:recv, :if_recv] do
    is_function(eval, 2) and Macro.validate(ast) == :ok and valid?(p)
  end

  def valid?({op, p}) when op in [:not, :always, :eventually], do: valid?(p)

  def valid?({op, p1, p2}) when op in [:and, :or, :implies],
    do: valid?(p1) and valid?(p2)

  def valid?({:next, s, p}) when s in [:weak, :strong], do: valid?(p)

  def valid?({:until, s, p1, p2}) when s in [:weak, :strong],
    do: valid?(p1) and valid?(p2)

  def valid?(p), do: atomic?(p)

  @spec proposition_to_quoted(t) :: Macro.output()
  def proposition_to_quoted(true), do: true
  def proposition_to_quoted(false), do: false

  def proposition_to_quoted({:expr, {_fun, src}}), do: src

  def proposition_to_quoted({:let, binders, p}) do
    quote do
      let unquote(binders |> Enum.map(&binder_to_quoted/1)) do
        unquote(proposition_to_quoted(p))
      end
    end
  end

  def proposition_to_quoted({:recv, {_fn, src}}) do
    quote do: recv(unquote(src))
  end

  def proposition_to_quoted({:recv, {_fn, src}, expr}) do
    quote do
      recv(unquote(src)) do
        unquote(proposition_to_quoted(expr))
      end
    end
  end

  def proposition_to_quoted({:if_recv, {_fn, src}, expr}) do
    quote do
      if recv(unquote(src)) do
        unquote(proposition_to_quoted(expr))
      end
    end
  end

  def proposition_to_quoted({:not, p}) do
    quote do: not unquote(proposition_to_quoted(p))
  end

  def proposition_to_quoted({:and, p1, p2}) do
    quote do: unquote(proposition_to_quoted(p1)) and unquote(proposition_to_quoted(p2))
  end

  def proposition_to_quoted({:or, p1, p2}) do
    quote do: unquote(proposition_to_quoted(p1)) or unquote(proposition_to_quoted(p2))
  end

  def proposition_to_quoted({:implies, p1, p2}) do
    quote do
      if unquote(proposition_to_quoted(p1)), do: unquote(proposition_to_quoted(p2))
    end
  end

  def proposition_to_quoted({:next, strength, p}) do
    operator = :"next_#{strength}"
    quote do: unquote(operator)(unquote(proposition_to_quoted(p)))
  end

  def proposition_to_quoted({operator, p}) when operator in [:always, :eventually] do
    quote do: unquote(operator)(unquote(proposition_to_quoted(p)))
  end

  def proposition_to_quoted({:until, strength, p1, p2}) do
    quote do
      unquote(:"until_#{strength}")(
        unquote(proposition_to_quoted(p1)),
        unquote(proposition_to_quoted(p2))
      )
    end
  end

  defp binder_to_quoted({name, {:expr, {_fun, src}}}) do
    {name, src}
  end

  defp binder_to_quoted({name, {:val, x}}) do
    val = quote do: &{:val, unquote(Macro.escape(x))}
    {name, val}
  end

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

  def compile_proposition({:if, _opts, [{:recv, _opts, args}, [do: prop]]}, macro_env) do
    [pattern] = args

    quote do
      {:if_recv, unquote(compile_native_recv(pattern, macro_env)),
       unquote(compile_proposition(prop, macro_env))}
    end
  end

  def compile_proposition({:if, _opts, [prop1, [do: prop2]]}, macro_env) do
    quote do
      {:implies, unquote(compile_proposition(prop1, macro_env)),
       unquote(compile_proposition(prop2, macro_env))}
    end
  end

  def compile_proposition({:if, _opts, [_, [do: _, else: _]]}, macro_env) do
    raise CompileError,
      file: macro_env.file,
      line: macro_env.line,
      description: "Illegal 'else'-block within QuickLTL expression"
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

  def compile_proposition({:until_strong, _opts, [prop1, prop2]}, macro_env) do
    quote do
      {:until, :strong, unquote(compile_proposition(prop1, macro_env)),
       unquote(compile_proposition(prop2, macro_env))}
    end
  end

  def compile_proposition({:until_weak, _opts, [prop1, prop2]}, macro_env) do
    quote do
      {:until, :weak, unquote(compile_proposition(prop1, macro_env)),
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

  def compile_proposition({:recv, _, [pattern, [do: expr]]}, macro_env) do
    quote do
      {:recv, unquote(compile_native_recv(pattern, macro_env)),
       unquote(compile_proposition(expr, macro_env))}
    end
  end

  def compile_proposition({:recv, _, [pattern]}, macro_env) do
    {:recv, compile_native_recv(pattern, macro_env)}
  end

  def compile_proposition(expr, macro_env) do
    quote do: {:expr, unquote(compile_native_expr(expr, macro_env))}
  end

  def compile_binders(binders, macro_env) do
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
  def compile_native_expr(expr, macro_env) do
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
                  Map.fetch!(unquote(state_var), unquote(name))
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

  @spec compile_native_recv(Macro.input(), Macro.Env.t()) :: Macro.output()
  @doc """
  Produce an evaluator for an Elixir recv-pattern used as part of a proposition.

  This expression is to be interpreted in a logical `t:env/0` that is put
  on top of the usual Elixir variable scope.  That is, any free variables
  of the expression should be looked up at evaluation time.
  """
  def compile_native_recv(pattern, macro_env) do
    pattern = Macro.expand(pattern, macro_env)

    evaluator =
      if macro_env.context == :match do
        quote do: _
      else
        outer_vars = Macro.Env.vars(macro_env)
        state_var = Macro.unique_var(:state, __MODULE__)
        env_var = Macro.unique_var(:env, __MODULE__)

        lookups =
          for {name, _, _} = var <- collect_pins(pattern),
              var_context(var) not in outer_vars do
            quote do
              unquote(var) =
                Map.get_lazy(unquote(env_var), unquote(name), fn ->
                  Map.fetch!(unquote(state_var), unquote(name))
                end)
            end
          end

        captures =
          for {name, _, _} = var <- collect_vars(pattern),
              not match?([?_ | _], Atom.to_charlist(name)) do
            {name, var}
          end

        quote do
          fn unquote(state_var), unquote(env_var) ->
            unquote_splicing(lookups)

            receive do
              unquote(pattern) ->
                {:received, unquote(captures)}
            after
              0 -> :not_received
            end
          end
        end
      end

    quote do: {unquote(evaluator), unquote(Macro.escape(pattern))}
  end

  @spec collect_vars(Macro.output()) :: MapSet.t()
  def collect_vars(ast) do
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

  @spec collect_pins(Macro.output()) :: MapSet.t()
  defp collect_pins(ast) do
    Macro.prewalk(ast, MapSet.new(), fn
      {:^, _, [{name, _, context} = var]}, acc when is_atom(name) and is_atom(context) ->
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
