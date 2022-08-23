defmodule PropLTL.Proposition do
  @type env :: %{atom => term}

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

  @type guarded_prop ::
          boolean()
          | atomic
          | {:not, guarded_prop}
          | {:and, guarded_prop, guarded_prop}
          | {:or, guarded_prop, guarded_prop}
          | {:implies, guarded_prop, guarded_prop}
          | {:next, :weak | :strong, prop}

  @type atomic ::
          {:expr, (env -> boolean())}
          | {:recv, (env -> env | false)}
          | {:let, atom, (env -> term)}

  @doc """
  Simplify a proposition using some common equivalences.

  Essentially, this will push negation as deep as possible into the expression,
  then simplify around `true` and `false` subexpressions.

  ## Examples

      iex> simplify prop(
      ...>   if true or not false, do: false
      ...> )
      false

      iex> simplify prop true or (if not false, do: false)
      true

      iex> simplify prop not (always do
      ...>   if true, do: weak_until(false, true)
      ...> end)
      prop eventually(until(true, false))

      iex> p = simplify prop not (always do
      ...>   if x == 1, do: eventually(x == 2)
      ...> end)
      iex> match?(
      ...>   prop(
      ...>      eventually(_ and always(not _))
      ...>   ), p)
      true
  """
  @spec simplify(prop) :: prop
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
  def simplify({:not, {:next, :weak, p}}), do: {:next, :strong, simplify({:not, p})}
  def simplify({:not, {:next, :strong, p}}), do: {:next, :weak, simplify({:not, p})}
  def simplify({:not, {:always, p}}), do: {:eventually, simplify({:not, p})}
  def simplify({:not, {:eventually, p}}), do: {:always, simplify({:not, p})}

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

  def simplify(prop), do: prop

  @doc """

  ## Examples

    iex> unfold prop always(if false, do: eventually(true))
    prop do
      ( if false, do: true or next_strong( eventually(true) ) )
      and next_weak(always(if false, do: eventually true))
    end
  """
  @spec unfold(prop) :: guarded_prop
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
  def unfold({:recv, _} = p), do: p
  def unfold({:let, _, _} = p), do: p

  def unfold({:not, p}), do: {:not, unfold(p)}
  def unfold({:and, p, q}), do: {:and, unfold(p), unfold(q)}
  def unfold({:or, p, q}), do: {:or, unfold(p), unfold(q)}
  def unfold({:implies, p, q}), do: {:implies, unfold(p), unfold(q)}

  @doc """

  ## Examples

    iex> p = prop do
    ...>   if (let x = 1), do: x == 1
    ...> end
    iex> {q, env} = step(p, %{})
    iex> env
    %{x: 1}
    iex> q
    prop( if true, do: true )

    iex> p = prop (x == 1) and (let x = 1)
    iex> {q, env} = step(p, %{})
    iex> env
    %{x: 1}
    iex> q
    prop false and true

    iex> p = prop recv({:foo, ^bar, baz}) and baz == :bar
    iex> send(self(), {:foo, 42, :bar})
    iex> {q, env} = step(p, %{bar: 42})
    iex> env
    %{bar: 42, baz: :bar}
    iex> q
    prop true and true

  """
  @spec step(guarded_prop, env) :: {guarded_prop, env}
  def step(true, env), do: {true, env}
  def step(false, env), do: {false, env}

  def step({:next, _, p}, env), do: {p, env}

  def step({:expr, eval}, env), do: {eval.(env), env}

  def step({:let, var, eval}, env) do
    Map.get_and_update(env, var, fn
      nil -> {true, eval.(env)}
      val -> {false, val}
    end)
  end

  def step({:recv, recv}, env) do
    case recv.(env) do
      nil -> {false, env}
      new_env -> {true, new_env}
    end
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
  def conclude(true, env), do: {true, env}
  def conclude(false, env), do: {false, env}

  def conclude({:next, :weak, _}, env), do: {true, env}
  def conclude({:next, :strong, _}, env), do: {false, env}

  def conclude({:expr, eval}, env), do: {eval.(env), env}

  def conclude({:let, var, eval}, env) do
    Map.get_and_update(env, var, fn
      nil -> {true, eval.(env)}
      val -> {false, val}
    end)
  end

  def conclude({:recv, recv}, env) do
    case recv.(env) do
      nil -> {false, env}
      new_env -> {true, new_env}
    end
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
  Read a QuickLTL proposition with Elixir syntax.

  FIXME properly document the syntax

  ## Examples

      iex> prop do
      ...>   if true or not false, do: true
      ...> end
      {:implies, {:or, true, {:not, false}}, :true}

      iex> p = prop always not x == 2
      iex> match?({:always, {:expr, _}}, p)
      true

      iex> p = prop always not (x == 2)
      iex> match?({:always, {:not, {:expr, _}}}, p)
      true

      iex> p = prop do
      ...>   always do
      ...>     if (let orig = x), do: until(x > orig, x == orig)
      ...>   end
      ...> end
      iex> match?(
      ...>   {:always,
      ...>     {:implies,
      ...>       {:let, :orig, _},
      ...>       {:until, {:expr, _}, {:expr, _}}
      ...>     }
      ...>   },
      ...>   p)
      true

      This macro can also be used as part of a pattern:

      iex> x = true
      iex> match?(prop(not _ and ^x), prop(not true and true))
      true
      iex> match?(prop(not _ and ^x), prop(not true and false))
      false

      iex> match?(prop do always (not &{:expr, _}) end, prop do always not(x == 2) end)
      true

  """
  defmacro prop(ast) do
    translate_prop(ast, __CALLER__)
  end

  @spec translate_prop(term, caller :: Macro.Env.t()) :: prop
  defp translate_prop(true, _) do
    true
  end

  defp translate_prop(false, _) do
    false
  end

  defp translate_prop([do: prop], caller) do
    translate_prop(prop, caller)
  end

  defp translate_prop({:__block__, _, [prop]}, caller) do
    translate_prop(prop, caller)
  end

  defp translate_prop({:not, _opts, [prop]}, caller) do
    quote do: {:not, unquote(translate_prop(prop, caller))}
  end

  defp translate_prop({:and, _opts, [prop1, prop2]}, caller) do
    quote do
      {:and, unquote(translate_prop(prop1, caller)), unquote(translate_prop(prop2, caller))}
    end
  end

  defp translate_prop({:or, _opts, [prop1, prop2]}, caller) do
    quote do
      {:or, unquote(translate_prop(prop1, caller)), unquote(translate_prop(prop2, caller))}
    end
  end

  defp translate_prop({:if, _opts, [prop1, [do: prop2]]}, caller) do
    quote do
      {:implies, unquote(translate_prop(prop1, caller)), unquote(translate_prop(prop2, caller))}
    end
  end

  defp translate_prop({:next_weak, _opts, [prop]}, caller) do
    quote do: {:next, :weak, unquote(translate_prop(prop, caller))}
  end

  defp translate_prop({:next_strong, _opts, [prop]}, caller) do
    quote do: {:next, :strong, unquote(translate_prop(prop, caller))}
  end

  defp translate_prop({:always, _opts, [prop]}, caller) do
    quote do: {:always, unquote(translate_prop(prop, caller))}
  end

  defp translate_prop({:eventually, _opts, [prop]}, caller) do
    quote do: {:eventually, unquote(translate_prop(prop, caller))}
  end

  defp translate_prop({:until, _opts, [prop1, prop2]}, caller) do
    quote do
      {:until, unquote(translate_prop(prop1, caller)), unquote(translate_prop(prop2, caller))}
    end
  end

  defp translate_prop({:weak_until, _opts, [prop1, prop2]}, caller) do
    quote do
      {:weak_until, unquote(translate_prop(prop1, caller)),
       unquote(translate_prop(prop2, caller))}
    end
  end

  defp translate_prop({:recv, _opts, [pattern]}, caller) do
    quote do: {:recv, unquote(make_recv_handler(pattern, 0, caller))}
  end

  defp translate_prop({:let, _, [{:=, _, [{name, _, context}, expr]}]}, caller)
       when is_atom(name) and is_atom(context) do
    quote do: {:let, unquote(name), unquote(make_atomic_handler(expr, caller))}
  end

  defp translate_prop({:_, _, context} = wildcard, _caller) when is_atom(context) do
    wildcard
  end

  defp translate_prop({:^, _, _} = pin, _caller) do
    pin
  end

  defp translate_prop({:&, _, [pattern]}, _caller) do
    pattern
  end

  defp translate_prop(expr, caller) do
    quote do: {:expr, unquote(make_atomic_handler(expr, caller))}
  end

  @spec make_recv_handler(Macro.input(), non_neg_integer(), Macro.Env.t()) :: term
  def make_recv_handler(pattern, timeout, caller) do
    vars = collect_vars_from_pattern(pattern)
    env_pins = collect_pins_from_pattern(pattern, Macro.Env.vars(caller))

    pin_decls =
      for {symbol, _, _} = var <- env_pins do
        quote do
          unquote(var) = Map.get(env, unquote(symbol))
        end
      end

    var_assgs =
      for {symbol, _, _} = var <- vars do
        quote do
          env = Map.put(env, unquote(symbol), unquote(var))
        end
      end

    quote do
      fn env ->
        unquote_splicing(pin_decls)

        receive do
          unquote(pattern) ->
            unquote_splicing(var_assgs)
            env
        after
          unquote(timeout) ->
            nil
        end
      end
    end
  end

  def make_atomic_handler(expr, caller) do
    vars = Macro.Env.vars(caller)
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

  defmacro escape_var(name) do
    quote do: Map.get(env, unquote(name))
  end

  defp collect_pins_from_pattern(pattern, vars) do
    {_, pins} =
      Macro.prewalk(pattern, [], fn
        {:^, _, [var]}, acc ->
          if var_context(var) in vars do
            {:ok, acc}
          else
            {:ok, [var | acc]}
          end

        form, acc ->
          {form, acc}
      end)

    pins
  end

  defp collect_vars_from_pattern({:when, _, [left, _right]}) do
    collect_vars_from_pattern(left)
  end

  defp collect_vars_from_pattern(pattern) do
    {_, vars} =
      Macro.prewalk(pattern, [], fn
        {skip, _, [_]}, acc when skip in [:^, :@] ->
          {:ok, acc}

        {:_, _, context}, acc when is_atom(context) ->
          {:ok, acc}

        {name, meta, context}, acc when is_atom(name) and is_atom(context) ->
          {:ok, [{name, meta, context} | acc]}

        node, acc ->
          {node, acc}
      end)

    vars
  end

  defp var_context({name, meta, context}) do
    {name, meta[:counter] || context}
  end
end
