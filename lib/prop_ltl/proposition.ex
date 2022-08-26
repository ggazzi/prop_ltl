defmodule PropLTL.Proposition do
  @moduledoc """
  Propositions in a variant of linear temporal logic (LTL) for property-based testing.

  Heavily based on [Quickstrom](https://quickstrom.io) and on
  the [paper](https://dl.acm.org/doi/10.1145/3519939.3523728)
  describing the theory behind it.

  Propositions should be written in Elixir-like syntax using the macro `prop/1`.
  Pattern matching propositions should also be done using this macro, with the option `pattern: true`.

  Temporal logic is useful for specifying systems whose state changes over time.
  One execution of such a system is abstracted as a *trace*: a sequence of states and events.
  A proposition in temporal logic will then describe which sequences of states are acceptable.
  """

  @typedoc """
  A proposition in a variant of linear temporal logic.
  """
  @type prop ::
          boolean()
          | atomic
          | {:not, prop}
          | {:and, prop, prop}
          | {:or, prop, prop}
          | {:implies, prop, prop}
          | {:next, :weak | :strong, prop}
          | {:always, prop}
          | {:eventually, prop}
          | {:until, prop, prop}
          | {:weak_until, prop, prop}

  @typedoc """
  An atomic proposition in a variant of linear temporal logic.
  """
  @type atomic ::
          {:expr, (env -> boolean()), Macro.output()}
          | {:let, atom, (env -> term), Macro.output()}
  # TODO: add an atomic proposition for receiving messages
  # | {:recv, (state -> state | false)}

  @typedoc """
  A guarded proposition in a variant of linear temporal logic.

  Guarded propositions will have all temporal operators inside
  at least one level of the `next` operator.
  They are useful so we can easily `step/2` the evaluation of
  the proposition for the current state of the system.
  """
  @type guarded_prop ::
          boolean()
          | atomic
          | {:not, guarded_prop}
          | {:and, guarded_prop, guarded_prop}
          | {:or, guarded_prop, guarded_prop}
          | {:implies, guarded_prop, guarded_prop}
          | {:next, :weak | :strong, prop}

  @typedoc """
  Logical environment under which a proposition can be evaluated.

  Provides values for any logical variables, which can be determined
  with the `atomic` proposition `(let x = value)`.
  """
  @type env :: %{atom => term}

  @spec simplify(prop) :: prop
  @doc """
  Simplify a proposition using some common equivalences.

  Essentially, this will push negation as deep as possible into the expression,
  then simplify around `true` and `false` subexpressions.

  ## Examples

  After all atomic propositions are evaluated to either `true` or `false`,
  simplify will always reduce to a single boolean value.

      iex> simplify prop(
      ...>   if true or not false, do: false
      ...> )
      false

      iex> simplify prop true or (if not false, do: false)
      true

  This works even for propositions containing temporal operators!

      iex> simplify prop(
      ...>   next_weak(false) or next_strong(false)
      ...>   or always(false) or eventually(false)
      ...>   or until(false, true) or weak_until(false, false)
      ...>)
      prop do next_weak(false) or always(false) end

      iex> simplify prop(
      ...>   next_weak(true) and next_strong(true)
      ...>   and always(true) and eventually(true)
      ...>   and until(true, false) and weak_until(true, false)
      ...> )
      prop do next_strong(true) and eventually(true) end

  In any case, it will distribute negation into all other operators, eliminating trivial
  atomic propositions as much as possible.

      iex> simplify prop not (always do
      ...>   if true, do: weak_until(false, true)
      ...> end)
      prop eventually(until(true, false))

      iex> p = simplify prop not (always do
      ...>   if x == 1, do: eventually(x == 2)
      ...> end)
      iex> match?(
      ...>   prop do eventually(_ and always(not _)) end,
      ...>   p)
      true
  """
  def simplify({:and, p, q}) do
    case {simplify(p), simplify(q)} do
      {true, q} -> q
      {p, true} -> p
      {false, _q} -> false
      {_p, false} -> false
      {p, q} -> {:and, p, q}
    end
  end

  def simplify({:or, p, q}) do
    case {simplify(p), simplify(q)} do
      {true, _q} -> true
      {_p, true} -> true
      {false, q} -> q
      {p, false} -> p
      {p, q} -> {:or, p, q}
    end
  end

  def simplify({:implies, p, q}) do
    case {simplify(p), simplify(q)} do
      {true, q} -> q
      {_p, true} -> true
      {false, _q} -> true
      {p, false} -> simplify({:not, p})
      {p, q} -> {:implies, p, q}
    end
  end

  def simplify({:not, {:and, p, q}}), do: simplify({:or, {:not, p}, {:not, q}})
  def simplify({:not, {:or, p, q}}), do: simplify({:and, {:not, p}, {:not, q}})
  def simplify({:not, {:implies, p, q}}), do: simplify({:and, p, {:not, q}})
  def simplify({:not, {:next, :weak, p}}), do: simplify({:next, :strong, {:not, p}})
  def simplify({:not, {:next, :strong, p}}), do: simplify({:next, :weak, {:not, p}})
  def simplify({:not, {:always, p}}), do: simplify({:eventually, {:not, p}})
  def simplify({:not, {:eventually, p}}), do: simplify({:always, {:not, p}})

  def simplify({:not, {:until, p, q}}),
    do: {:weak_until, simplify({:not, p}), simplify({:not, q})}

  def simplify({:not, {:weak_until, p, q}}),
    do: {:until, simplify({:not, p}), simplify({:not, q})}

  def simplify({:not, p}) do
    case simplify(p) do
      true -> false
      false -> true
      other -> {:not, other}
    end
  end

  def simplify({:next, kind, p}) do
    case {kind, simplify(p)} do
      {:weak, true} -> true
      {:strong, false} -> false
      {_, other} -> {:next, kind, other}
    end
  end

  def simplify({:always, p}) do
    case simplify(p) do
      true -> true
      other -> {:always, other}
    end
  end

  def simplify({:eventually, p}) do
    case simplify(p) do
      false -> false
      other -> {:eventually, other}
    end
  end

  def simplify({:until, p, q}) do
    case {simplify(p), simplify(q)} do
      {true, _} -> true
      {false, _} -> false
      {other, false} -> other
      {other, true} -> {:eventually, other}
      {other1, other2} -> {:until, other1, other2}
    end
  end

  def simplify({:weak_until, p, q}) do
    case {simplify(p), simplify(q)} do
      {true, _} -> true
      {_, true} -> true
      {other, false} -> other
      {false, other} -> {:always, other}
      {other1, other2} -> {:weak_until, other1, other2}
    end
  end

  def simplify(prop), do: prop

  @spec unfold(prop) :: guarded_prop
  @doc """
  Rewrites the proposition so that the outermost temporal operator is always `next`.

  Use the well-known temporal equivalences to rewrite the given proposition.
  The result is easier to evaluate stepwise (as in `step/2` and `conclude/2`).

  ## Examples

  Rewrites temporal operators to ensure that the outermost such operator is always `next`.

      iex> match?(
      ...>   prop do (&e1) or next_strong(eventually(&{:expr, _, _} = e2)) end when e1 == e2,
      ...>   unfold(prop do eventually(state.x > 0) end)
      ...> )
      true

      iex> match?(
      ...>   prop do (&e1) or next_strong(eventually(&{:let, :x, _, _} = e2)) end when e1 == e2,
      ...>   unfold(prop do eventually(let x = state.x) end)
      ...> )
      true

  Rewrites only the outermost temporal operators, even if they are nested inside
  propositional operators.

      iex> unfold prop always(if false, do: eventually(true))
      prop do
        ( if false, do: true or next_strong(eventually(true)) )
        and next_weak(always(if false, do: eventually true))
      end

  """
  def unfold({:next, _, _} = p), do: p
  def unfold({:always, p}), do: {:and, unfold(p), {:next, :weak, {:always, p}}}
  def unfold({:eventually, p}), do: {:or, unfold(p), {:next, :strong, {:eventually, p}}}

  def unfold({:until, p, q}) do
    {:or, unfold(p), {:and, unfold(q), {:next, :strong, {:until, p, q}}}}
  end

  def unfold({:weak_until, p, q}) do
    {:or, unfold(p), {:and, unfold(q), {:next, :weak, {:until, p, q}}}}
  end

  def unfold(true), do: true
  def unfold(false), do: false
  def unfold({:expr, _, _} = p), do: p
  def unfold({:let, _, _, _} = p), do: p

  def unfold({:not, p}), do: {:not, unfold(p)}
  def unfold({:and, p, q}), do: {:and, unfold(p), unfold(q)}
  def unfold({:or, p, q}), do: {:or, unfold(p), unfold(q)}
  def unfold({:implies, p, q}), do: {:implies, unfold(p), unfold(q)}

  @spec step(guarded_prop, env) :: {guarded_prop, env}
  @doc """
  Evaluate the guarded proposition at the current state.

  Any atomic propositions that are outside temporal operators will be evaluated
  at the given logical `t:env/0`.

  The outermost occurrences of the `next` operator will be removed and replaced
  by their children.

  ## Examples

  Unguarded boolean expressions will be evaluated at the current environment.

      iex> p = prop do (x < 0 or x > 0) and next_weak(x == 0) end
      iex> {q, _env} = step(p, %{x: 1})
      iex> match?(
      ...>   prop do (false or true) and &{:expr, _, _} end,
      ...>   q)
      true

  A common pattern is using let-and to bind variables for future use.

      iex> p = prop do (let x = 1) and x == 1 end
      iex> {q, env} = step(p, %{})
      iex> env
      %{x: 1}
      iex> q
      prop do true and true end

  Here the syntactical order is important, since it will determine
  the execution order of the assignments.

      iex> p = prop (x == 1) and (let x = 1)
      iex> {q, env} = step(p, %{})
      iex> env
      %{x: 1}
      iex> q
      prop false and true

  Note also that if-let will not always work as intended!
  If the variable was already bound, the implication will always evaluate to true!

      iex> p = prop do (let x = 1) and if (let x = 2), do: next_weak(x == 3) end
      iex> {q, env} = step(p, %{})
      iex> env
      %{x: 1}
      iex> match?(
      ...>    prop do true and if false, do: &{:expr, _, _} end,
      ...>    q)
      true

  The next operators will be simply removed.

      iex> p = prop do (let x = state.x) and next_weak(state.x == x) end
      iex> {q, env} = step(p, %{state: %{x: 1}})
      iex> match?(
      ...>   prop do true and &{:expr, _, _} end,
      ...>   q)
      true
      iex> {r, env} = step(q, env)
      iex> r
      prop do true and true end

      iex> p = prop do (let x = state.x) and next_strong(state.x == x + 1) end
      iex> {q, env} = step(p, %{state: %{x: 1}})
      iex> match?(
      ...>   prop do true and &{:expr, _, _} end,
      ...>   q)
      true
      iex> {r, env} = step(q, env)
      iex> r
      prop do true and false end

  """
  def step(true, env), do: {true, env}
  def step(false, env), do: {false, env}

  def step({:next, _, p}, env), do: {p, env}

  def step({:expr, eval, _src}, env) do
    {if eval.(env) do
       true
     else
       false
     end, env}
  end

  def step({:let, var, eval, _src}, env) do
    Map.get_and_update(env, var, fn
      nil -> {true, eval.(env)}
      val -> {false, val}
    end)
  end

  def step({:not, p}, env) do
    {p, env} = step(p, env)
    {{:not, p}, env}
  end

  def step({:and, p, q}, env) do
    {p, env} = step(p, env)
    {q, env} = step(q, env)
    {{:and, p, q}, env}
  end

  def step({:or, p, q}, env) do
    {p, env} = step(p, env)
    {q, env} = step(q, env)
    {{:or, p, q}, env}
  end

  def step({:implies, p, q}, env) do
    {p, env} = step(p, env)
    {q, env} = step(q, env)
    {{:implies, p, q}, env}
  end

  @spec conclude(guarded_prop, env) :: {guarded_prop, env}
  @doc """
  Evaluate the guarded proposition at the end of a trace.

  This is analogous to `step/2`, but assumes no states will follow the current one.
  Thus, it will evaluate any `next` operators to `true` or `false` if they were
  weak or strong, respectively.

  ## Examples

  Unguarded boolean expressions will be evaluated at the current environment.

      iex> p = prop do x < 0 or x > 0 end
      iex> {q, _env} = conclude(p, %{x: 1})
      iex> q
      prop do false or true end

  A common pattern is using let-and to bind variables for future use.

      iex> p = prop do (let x = 1) and x == 1 end
      iex> {q, env} = conclude(p, %{})
      iex> env
      %{x: 1}
      iex> q
      prop do true and true end

  Here the syntactical order is important, since it will determine
  the execution order of the assignments.

      iex> p = prop do x == 1 and (let x = 1) end
      iex> {q, env} = conclude(p, %{})
      iex> env
      %{x: 1}
      iex> q
      prop do false and true end

  Note also that if-let will not always work as intended!
  If the variable was already bound, the implication will always evaluate to true!

      iex> p = prop do (let x = 1) and if (let x = 2), do: next_strong(x == 3) end
      iex> {q, env} = conclude(p, %{})
      iex> env
      %{x: 1}
      iex> q
      prop do true and if false, do: false end

  The weak next operator will always conclude as true.

      # iex> p = prop do (let x = state.x) and next_weak(state.x == x + 1) end
      # iex> {q, env} = conclude(p, %{state: %{x: 1}})
      # iex> env
      # %{state: %{x: 1}, x: 1}
      # iex> q
      # prop do if true and true end

  The strong next operator will always conclude as false.

      iex> p = prop do (let x = state.x) and next_strong(state.x == x + 1) end
      iex> {q, env} = conclude(p, %{state: %{x: 1}})
      iex> env
      %{state: %{x: 1}, x: 1}
      iex> q
      prop do true and false end

  """
  def conclude(true, env), do: {true, env}
  def conclude(false, env), do: {false, env}

  def conclude({:next, :weak, _}, env), do: {true, env}
  def conclude({:next, :strong, _}, env), do: {false, env}

  def conclude({:expr, eval, _ast}, env), do: {eval.(env), env}

  def conclude({:let, var, eval, _src}, env) do
    Map.get_and_update(env, var, fn
      nil -> {true, eval.(env)}
      val -> {false, val}
    end)
  end

  def conclude({:not, p}, env) do
    {p, env} = conclude(p, env)
    {{:not, p}, env}
  end

  def conclude({:and, p, q}, env) do
    {p, env} = conclude(p, env)
    {q, env} = conclude(q, env)
    {{:and, p, q}, env}
  end

  def conclude({:or, p, q}, env) do
    {p, env} = conclude(p, env)
    {q, env} = conclude(q, env)
    {{:or, p, q}, env}
  end

  def conclude({:implies, p, q}, env) do
    {p, env} = conclude(p, env)
    {q, env} = conclude(q, env)
    {{:implies, p, q}, env}
  end

  @doc """
  Macro for writing temporal propositions with Elixir-like syntax.

  FIXME: properly document the syntax

  ## Examples

  These examples show the internal representation of propositions,
  which is unstable and subject to change!

      iex> prop do
      ...>   if true or not false, do: true
      ...> end
      {:implies, {:or, true, {:not, false}}, :true}

      iex> p = prop always not state.x == 2
      iex> match?(
      ...>   {:always, {:expr, fn1, _}}
      ...>     when is_function(fn1),
      ...>   p
      ...> )
      true

      iex> p = prop always not (state.x == 2)
      iex> match?(
      ...>   {:always, {:not, {:expr, fn1, _}}}
      ...>     when is_function(fn1),
      ...>   p
      ...> )
      true

      iex> p = prop do
      ...>   always do
      ...>     if (let orig = state.x), do: until(state.x > orig, state.x == orig)
      ...>   end
      ...> end
      iex> match?(
      ...>   {:always,
      ...>     {:implies,
      ...>       {:let, :orig, fn1, _},
      ...>       {:until,
      ...>         {:expr, fn2, _},
      ...>         {:expr, fn3, _}
      ...>       }
      ...>     }
      ...>   } when is_function(fn1) and is_function(fn2) and is_function(fn3),
      ...>   p)
      true

      This macro can also be used as part of a pattern.

      iex> x = true
      iex> match?(prop(not _ and ^x), prop(not true and true))
      true
      iex> match?(prop(not _ and ^x), prop(not true and false))
      false

      The prefix operator `&` works like an `unquote` for props.

      iex> prop do (&{:not, prop do true and false end}) or false end
      prop not (true and false) or false

      iex> match?(
      ...>   prop do always (&{:expr, _, _}) and true end,
      ...>   prop do always (x == 2) and true end
      ...> )
      true

  """
  defmacro prop(arg) do
    compile_proposition(arg, __CALLER__)
  end

  @spec compile_proposition(Macro.input(), Macro.Env.t()) :: prop
  @doc """
  Transform an Elixir AST into the corresponding proposition.

  For more information of the expected syntax, see `prop/1`.
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
      {:let, unquote(name), unquote_splicing(compile_atomic_evaluator(expr, macro_env))}
    end
  end

  def compile_proposition(expr, macro_env) do
    quote do: {:expr, unquote_splicing(compile_atomic_evaluator(expr, macro_env))}
  end

  @spec compile_atomic_evaluator(Macro.input(), Macro.Env.t()) :: list(Macro.output())
  @doc """
  Produce an evaluator for an Elixir expression used as part of a proposition.

  This expression is to be interpreted in a logical `t:env/0` that is put
  on top of the usual Elixir variable scope.  That is, any free variables
  of the expression should be looked up at evaluation time.
  """
  def compile_atomic_evaluator(expr, macro_env) do
    expr = Macro.expand(expr, macro_env)

    evaluator =
      if macro_env.context == :match do
        quote do: _
      else
        vars = Macro.Env.vars(macro_env)
        env_var = Macro.unique_var(:env, __MODULE__)

        body =
          Macro.prewalk(expr, fn
            ^env_var ->
              env_var

            {name, _, context} = var when is_atom(name) and is_atom(context) ->
              if var_context(var) in vars do
                var
              else
                quote do: Map.get(unquote(env_var), unquote(name))
              end

            other ->
              other
          end)

        quote do: fn unquote(env_var) -> unquote(body) end
      end

    [evaluator, Macro.escape(expr)]
  end

  defp var_context({name, meta, context}) do
    {name, meta[:counter] || context}
  end
end
