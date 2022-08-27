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
          | {:let, Keyword.t(binder), prop}
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
          {:expr, {(env -> boolean), Macro.output()}}

  # TODO: add an atomic and binding proposition for receiving messages

  @type binder :: {(env -> term), Macro.output()} | term()

  @type evaluator(result) :: {(env -> result), Macro.output()}

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
          | {:let, Keyword.t(evaluator(term)), prop}
          | {:not, guarded_prop}
          | {:and, guarded_prop, guarded_prop}
          | {:or, guarded_prop, guarded_prop}
          | {:implies, guarded_prop, guarded_prop}
          | {:next, :weak | :strong, prop}

  @typedoc """
  Logical environment under which a proposition can be evaluated.

  Provides values for any logical variables, which can be shadowed
  by the proposition `let x: value do p end`.
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

      iex> unfold prop always(if false, do: eventually(true))
      prop do
        ( if false, do: true or next_strong(eventually(true)) )
        and next_weak(always(if false, do: eventually true))
      end

      iex> match?(
      ...>   prop do (&e1) or next_strong(eventually(&{:expr, _} = e2)) end when e1 == e2,
      ...>   unfold(prop do eventually(state.x > 0) end)
      ...> )
      true

      Rewrites only the outermost temporal operators, even if they are nested inside
      propositional operators.

      TODO: more tests

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
  def unfold({:expr, _} = p), do: p
  def unfold({:let, binders, p}), do: {:let, binders, unfold(p)}

  def unfold({:not, p}), do: {:not, unfold(p)}
  def unfold({:and, p, q}), do: {:and, unfold(p), unfold(q)}
  def unfold({:or, p, q}), do: {:or, unfold(p), unfold(q)}
  def unfold({:implies, p, q}), do: {:implies, unfold(p), unfold(q)}

  @spec step(guarded_prop(), env()) :: prop()
  @doc """
  Evaluate the guarded proposition at the current state.

  Any atomic propositions that are outside temporal operators will be evaluated
  at the given logical `t:env/0`.

  The outermost occurrences of the `next` operator will be removed and replaced
  by their children.

  ## Examples

  Unguarded boolean expressions will be evaluated at the current environment.

      iex> p = prop do (x < 0 or x > 0) and next_weak(x == 0) end
      iex> match?(
      ...>   prop do (false or true) and &{:expr, _} end,
      ...>   step(p, %{x: 1})
      ...> )
      true

  We can use `let` to bind variables for future use.

      iex> p = prop do
      ...>   x > 0 and let orig: x do
      ...>     orig == x and next_weak(x > orig)
      ...>   end
      ...> end
      iex> q = step(p, %{x: 1})
      iex> match?(
      ...>   prop do
      ...>     true and let orig: (&1) do
      ...>       true and x > orig
      ...>     end
      ...>   end,
      ...>   q)
      iex> step(q, %{x: 2})
      prop do true and let orig: &1, do: true and true end

  Note that let bindings can shadow outer bindings.

      iex> p = prop do
      ...>   let x: x + 1, do: x == 1
      ...> end
      iex> step(p, %{x: 0})
      prop do let x: (&1), do: true end

  The outermost next operators will be removed, but *only* the outermost.

      iex> p = prop do
      ...>   let orig: x, do: next_strong(x > orig or next_weak(x > orig))
      ...> end
      iex> q = step(p, %{x: 1})
      iex> match?(
      ...>   prop do let orig: &1, do: (&{:expr, _}) or next_weak(_) end,
      ...>   q)
      true
      iex> r = step(q, %{x: 0})
      iex> match?(
      ...>   prop do let orig: &1, do: false or &{:expr, _} end,
      ...>   q)
      iex> step(r, %{x: 2})
      prop do let orig: (&1), do: false or true end

  """
  def step(true, _env), do: true
  def step(false, _env), do: false

  def step({:next, _, p}, _env), do: p

  def step({:expr, {eval, _src}}, env) do
    if eval.(env) do
      true
    else
      false
    end
  end

  def step({:let, binders, p}, env) do
    {binders, env} = eval_binders(binders, env)
    {:let, binders, step(p, env)}
  end

  def step({:not, p}, env) do
    {:not, step(p, env)}
  end

  def step({:and, p, q}, env) do
    {:and, step(p, env), step(q, env)}
  end

  def step({:or, p, q}, env) do
    {:or, step(p, env), step(q, env)}
  end

  def step({:implies, p, q}, env) do
    {:implies, step(p, env), step(q, env)}
  end

  @spec conclude(guarded_prop, env) :: prop
  @doc """
  Evaluate the guarded proposition at the end of a trace.

  This is analogous to `step/2`, but assumes no states will follow the current one.
  Thus, it will evaluate any `next` operators to `true` or `false` if they were
  weak or strong, respectively.

  ## Examples

  Unguarded boolean expressions will be evaluated at the current environment.

      iex> p = prop do x < 0 or x > 0 end
      iex> conclude(p, %{x: 1})
      prop do false or true end

  Let-bindings will also be resolved for the current state.

      iex> p = prop do
      ...>   x > 0 and let orig: x, do:
      ...>     orig == x and next_weak(x > orig)
      ...> end
      iex> conclude(p, %{x: 1})
      prop do true and let orig: &1, do:
        true and true
      end

  The weak next operator will always conclude as true.

      iex> p = prop do let x: state.x, do: next_weak(state.x == x + 1) end
      iex> conclude(p, %{state: %{x: 1}})
      prop do let x: (&1), do: true end

  The strong next operator will always conclude as false.

      iex> p = prop do let x: state.x, do: next_strong(state.x == x + 1) end
      iex> conclude(p, %{state: %{x: 1}})
      prop do let x: (&1), do: false end

  """
  def conclude(true, _env), do: true
  def conclude(false, _env), do: false

  def conclude({:next, :weak, _}, _env), do: true
  def conclude({:next, :strong, _}, _env), do: false

  def conclude({:expr, {eval, _src}}, env), do: eval.(env)

  def conclude({:let, binders, p}, env) do
    {binders, env} = eval_binders(binders, env)
    {:let, binders, conclude(p, env)}
  end

  def conclude({:not, p}, env) do
    {:not, conclude(p, env)}
  end

  def conclude({:and, p, q}, env) do
    {:and, conclude(p, env), conclude(q, env)}
  end

  def conclude({:or, p, q}, env) do
    {:or, conclude(p, env), conclude(q, env)}
  end

  def conclude({:implies, p, q}, env) do
    {:implies, conclude(p, env), conclude(q, env)}
  end

  @spec eval_binders(list(binder), env) :: {list(binder), env}
  defp eval_binders(binders, env) do
    eval_binders(binders, env, [])
  end

  defp eval_binders([], env, acc), do: {Enum.reverse(acc), env}

  defp eval_binders([{name, {eval, _src}} | binders], env, acc) do
    value = eval.(env)
    eval_binders(binders, Map.put(env, name, value), [{name, value} | acc])
  end

  defp eval_binders([{name, value} | binders], env, acc) do
    eval_binders(binders, Map.put(env, name, value), [{name, value} | acc])
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
      ...>   {:always, {:expr, {fn1, _}}}
      ...>     when is_function(fn1),
      ...>   p
      ...> )
      true

      iex> p = prop always not (state.x == 2)
      iex> match?(
      ...>   {:always, {:not, {:expr, {fn1, _}}}}
      ...>     when is_function(fn1),
      ...>   p
      ...> )
      true

      iex> p = prop do
      ...>   always do
      ...>     let orig: state.x, do: until(state.x > orig, state.x == orig)
      ...>   end
      ...> end
      iex> match?(
      ...>   {:always,
      ...>     {:let, [{:orig, {fn1, _}}],
      ...>       {:until,
      ...>         {:expr, {fn2, _}},
      ...>         {:expr, {fn3, _}}
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

      iex> prop do let x: (&1), do: true end
      {:let, [x: 1], true}

      iex> match?(
      ...>   prop do always (&{:expr, _}) and true end,
      ...>   prop do always (x == 2) and true end
      ...> )
      true

      iex> x = :foo
      iex> match?(
      ...>   prop do let x: ^x, do: true end,
      ...>   prop do let x: (&:foo), do: true end
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
    quote do: {:expr, unquote(compile_atomic_evaluator(expr, macro_env))}
  end

  def compile_binders(binders, macro_env) do
    for {name, expr} <- binders do
      binder =
        case expr do
          {:&, _, [raw_expr]} -> raw_expr
          {:^, _, [_]} = pin -> pin
          _ -> compile_atomic_evaluator(expr, macro_env)
        end

      quote do: {unquote(name), unquote(binder)}
    end
  end

  @spec compile_atomic_evaluator(Macro.input(), Macro.Env.t()) :: Macro.output()
  @doc """
  Produce an evaluator for an Elixir expression used as part of a proposition.

  This expression is to be interpreted in a logical `t:env/0` that is put
  on top of the usual Elixir variable scope.  That is, any free variables
  of the expression should be looked up at evaluation time.
  """
  defp compile_atomic_evaluator(expr, macro_env) do
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

    quote do: {unquote(evaluator), unquote(Macro.escape(expr))}
  end

  defp var_context({name, meta, context}) do
    {name, meta[:counter] || context}
  end
end
