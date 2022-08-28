defmodule QuickLTL do
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

  alias QuickLTL.Syntax

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
    Syntax.compile_proposition(arg, __CALLER__)
  end

  @typedoc """
  Representation of a state of the system being specified with QuickLTL.

  The system being specified is assumed to contain a set of variables
  that may change over time. A state is just one assignment of arbitrary
  Elixir values (`t:term/0`) to these variables.

  Note that these variables may be shadowed by the `t:env/0` or by let-expressions.
  """
  @type state :: %{atom => term}

  @typedoc """
  A logical environment under which a QuickLTL proposition may be evaluated.

  Provides a set of variables whose values are unchanged over time, unlike
  the `t:state/0`. Indeed, variables of the logical environment will shadow
  those of the state if there is a name clash.

  The logical environment may be extended locally within a proposition
  using the let-expression.
  """
  @type env :: %{atom => term}

  @spec evaluate_naive(Syntax.t(), nonempty_list(state), env) :: boolean()
  @doc """
  Evaluates the given proposition for the given state-trace.

  This is an inefficient implementation for long traces, as it will
  traverse the given tracae multiple times.  It is mostly useful as a reference
  implementation.
  """
  def evaluate_naive(p, trace, env \\ %{})

  def evaluate_naive(true, _, _), do: true
  def evaluate_naive(false, _, _), do: false

  def evaluate_naive({:expr, {eval, _src}}, [state | _], env) do
    # Make sure we have a boolean reflecting the truthiness of the result
    if eval.(state, env), do: true, else: false
  end

  def evaluate_naive({:let, binders, p}, [state | _] = trace, outer_env) do
    {_, inner_env} = eval_binders(binders, state, outer_env)
    evaluate_naive(p, trace, inner_env)
  end

  def evaluate_naive({:not, p}, trace, env), do: not evaluate_naive(p, trace, env)

  def evaluate_naive({:and, p1, p2}, trace, env) do
    if evaluate_naive(p1, trace, env), do: evaluate_naive(p2, trace, env), else: false
  end

  def evaluate_naive({:or, p1, p2}, trace, env) do
    if evaluate_naive(p1, trace, env), do: true, else: evaluate_naive(p2, trace, env)
  end

  def evaluate_naive({:implies, p1, p2}, trace, env) do
    if evaluate_naive(p1, trace, env), do: evaluate_naive(p2, trace, env), else: true
  end

  def evaluate_naive({:next, kind, _p}, [_state], _env) do
    case kind do
      :weak -> true
      :strong -> false
    end
  end

  def evaluate_naive({:next, _kind, p}, [_state | trace_rest], env) do
    evaluate_naive(p, trace_rest, env)
  end

  def evaluate_naive({:always, p}, trace, env) do
    nonempty_postfixes(trace) |> Enum.all?(&evaluate_naive(p, &1, env))
  end

  def evaluate_naive({:eventually, p}, trace, env) do
    nonempty_postfixes(trace) |> Enum.any?(&evaluate_naive(p, &1, env))
  end

  def evaluate_naive({:until, goal, meanwhile}, trace, env) do
    {before_goal, after_goal} =
      nonempty_postfixes(trace)
      |> Enum.split_while(fn subtrace -> not evaluate_naive(goal, subtrace, env) end)

    if after_goal == [] do
      false
    else
      Enum.all?(before_goal, fn subtrace -> evaluate_naive(meanwhile, subtrace, env) end)
    end
  end

  def evaluate_naive({:weak_until, goal, meanwhile}, trace, env) do
    nonempty_postfixes(trace)
    |> Stream.take_while(&(not evaluate_naive(goal, &1, env)))
    |> Enum.all?(&evaluate_naive(meanwhile, &1, env))
  end

  defmodule NonemptyPostfixes do
    @moduledoc false
    defstruct list: []

    defimpl Enumerable do
      def count(%{list: list}), do: {:ok, length(list)}
      def member?(_, _), do: {:error, __MODULE__}
      def slice(_), do: {:error, __MODULE__}

      def reduce(_state, {:halt, acc}, _fun), do: {:halted, acc}
      def reduce(state, {:suspend, acc}, fun), do: {:suspended, acc, &reduce(state, &1, fun)}
      def reduce(%{list: []}, {:cont, acc}, _fun), do: {:done, acc}

      def reduce(%{list: [_ | tail] = list}, {:cont, acc}, fun),
        do: reduce(tail, fun.(list, acc), fun)
    end
  end

  defp nonempty_postfixes(list), do: %NonemptyPostfixes{list: list}

  @spec evaluate(Syntax.t(), nonempty_list(state), env) :: Syntax.t()
  @doc """
  Evaluates the given proposition for the given state-trace.
  """
  def evaluate(p, trace, env \\ %{})

  def evaluate(p, [], _env) do
    p |> unfold() |> conclude() |> simplify()
  end

  def evaluate(p, [state | future], env) do
    p |> unfold() |> step(state) |> simplify() |> evaluate(future, env)
  end

  @spec simplify(Syntax.t()) :: Syntax.t()
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

  @spec unfold(Syntax.t()) :: Syntax.guarded()
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

  @spec step(Syntax.guarded(), state(), env()) :: Syntax.t()
  @doc """
  Evaluate the guarded proposition at the current state and environment.

  Any atomic propositions that are outside temporal operators will be evaluated
  at the given logical `t:env/0`.

  The outermost occurrences of the `next` operator will be removed and replaced
  by their children.

  ## Examples

  Unguarded boolean expressions will be evaluated at the current state.

      iex> p = prop do (x < zero or x > zero) and next_weak(x == 0) end
      iex> match?(
      ...>   prop do (false or true) and &{:expr, _} end,
      ...>   step(p, %{x: 1}, %{zero: 0})
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
  def step(p, state \\ %{}, env)

  def step(true, _state, _env), do: true
  def step(false, _state, _env), do: false

  def step({:next, _, p}, _state, _env), do: p

  def step({:expr, {eval, _src}}, state, env) do
    if eval.(state, env) do
      true
    else
      false
    end
  end

  def step({:let, binders, p}, state, env) do
    {binders, env} = eval_binders(binders, state, env)
    {:let, binders, step(p, state, env)}
  end

  def step({:not, p}, state, env) do
    {:not, step(p, state, env)}
  end

  def step({:and, p, q}, state, env) do
    {:and, step(p, state, env), step(q, state, env)}
  end

  def step({:or, p, q}, state, env) do
    {:or, step(p, state, env), step(q, state, env)}
  end

  def step({:implies, p, q}, state, env) do
    {:implies, step(p, state, env), step(q, state, env)}
  end

  @spec conclude(Syntax.t()) :: Syntax.t()
  @doc """
  Evaluate the guarded proposition at the end of a trace.
  Will essentially default the temporal operators to true or false depending on their semantics.

  ## Examples

  Boolean expressions will not be evaluated.

      iex> p = prop do x < zero or x > zero end
      iex> conclude(p)
      p

  Let-bindings will also not be evaluated.

      iex> p = prop do
      ...>   x > 0 and let orig: x, do:
      ...>     orig == x and next_weak(x > orig)
      ...> end
      iex> match?(
      ...>   prop do
      ...>     (&{:expr, _}) and let orig: &{_, _}, do:
      ...>       (&{:expr, _}) and true
      ...>   end,
      ...>   conclude(p))
      true

  The weak next, always and weak_until operators will always conclude as true.

      iex> p = prop do false or next_weak(state.x == x + 1) end
      iex> conclude(p)
      prop do false or true end

      iex> p = prop do false or always(state.x == x + 1) end
      iex> conclude(p)
      prop do false or true end

      iex> p = prop do false or weak_until(state.x == x + 1, state.x == x) end
      iex> conclude(p)
      prop do false or true end

  The strong next, eventually and until operators will always conclude as false.

      iex> p = prop do false or next_strong(state.x == x + 1) end
      iex> conclude(p)
      prop do false or false end

      iex> p = prop do false or eventually(state.x == x + 1) end
      iex> conclude(p)
      prop do false or false end

      iex> p = prop do false or until(state.x == x + 1, state.x == x) end
      iex> conclude(p)
      prop do false or false end

  """
  def conclude({:next, :weak, _}), do: true
  def conclude({:next, :strong, _}), do: false

  def conclude({:always, _}), do: true
  def conclude({:eventually, _}), do: false

  def conclude({:until, _, _}), do: false
  def conclude({:weak_until, _, _}), do: true

  def conclude({:not, p}), do: {:not, conclude(p)}
  def conclude({:and, p, q}), do: {:and, conclude(p), conclude(q)}
  def conclude({:or, p, q}), do: {:or, conclude(p), conclude(q)}
  def conclude({:implies, p, q}), do: {:implies, conclude(p), conclude(q)}

  def conclude({:let, binders, p}), do: {:let, binders, conclude(p)}

  def conclude(p), do: p

  @spec conclude(Syntax.guarded(), state, env) :: Syntax.guarded()
  @doc """
  Evaluate the guarded proposition at the end of a trace.

  This is analogous to `step/2`, but assumes no states will follow the current one.
  Thus, it will evaluate any `next` operators to `true` or `false` if they were
  weak or strong, respectively.

  ## Examples

  Unguarded boolean expressions will be evaluated at the current state and environment.

      iex> p = prop do x < zero or x > zero end
      iex> conclude(p, %{x: 1}, %{zero: 0})
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
  def conclude(p, state \\ %{}, env)

  def conclude(true, _state, _env), do: true
  def conclude(false, _state, _env), do: false

  def conclude({:next, :weak, _}, _state, _env), do: true
  def conclude({:next, :strong, _}, _state, _env), do: false

  def conclude({:expr, {eval, _src}}, state, env), do: eval.(state, env)

  def conclude({:let, binders, p}, state, env) do
    {binders, env} = eval_binders(binders, state, env)
    {:let, binders, conclude(p, env)}
  end

  def conclude({:not, p}, state, env) do
    {:not, conclude(p, state, env)}
  end

  def conclude({:and, p, q}, state, env) do
    {:and, conclude(p, state, env), conclude(q, state, env)}
  end

  def conclude({:or, p, q}, state, env) do
    {:or, conclude(p, state, env), conclude(q, state, env)}
  end

  def conclude({:implies, p, q}, state, env) do
    {:implies, conclude(p, state, env), conclude(q, state, env)}
  end

  @spec eval_binders(list(Syntax.binder()), state, env) :: {list(Syntax.binder()), env}
  defp eval_binders(binders, state, outer_env) do
    {new_binders_rev, inner_env} =
      for binder <- binders, reduce: {[], outer_env} do
        {acc, env} ->
          {name, value} = eval_binder(binder, state, env)
          {[{name, value} | acc], Map.put(env, name, value)}
      end

    {Enum.reverse(new_binders_rev), inner_env}
  end

  defp eval_binder({name, {eval, _src}}, state, env) do
    {name, eval.(state, env)}
  end

  defp eval_binder({name, value}, _state, _env) do
    {name, value}
  end
end
