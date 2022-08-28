defmodule GenServerLTL do
  defmodule ViolatedProperty do
    defexception message: "One or more LTL properties were violated",
                 trace: nil,
                 state: nil,
                 properties: nil

    @impl true
    def message(exception) do
      trace = inspect(exception.trace, pretty: true)
      state = inspect(exception.state, pretty: true)
      properties = inspect(exception.properties, pretty: true)

      "#{exception.message}\n  trace: #{trace}\n  state: #{state}\n  violated properties: #{properties}"
    end
  end

  defmacro properties(do: props) do
    compile_properties(props, __CALLER__)
  end

  def compile_properties({kind, _, [_name, [do: _proposition]]} = decl, caller)
      when kind in [:property, :invariant] do
    quote do: [unquote(compile_property(decl, caller))]
  end

  def compile_properties({:__block__, _, properties}, caller) do
    properties = properties |> Enum.map(&compile_property(&1, caller))
    quote do: [unquote_splicing(properties)]
  end

  defp compile_property({:property, _, [name, [do: proposition]]}, caller) do
    compiled = QuickLTL.compile_proposition(proposition, caller)
    quote do: {unquote(name), unquote(compiled)}
  end

  defp compile_property({:invariant, _, [name, [do: proposition]]}, caller) do
    compiled =
      QuickLTL.compile_proposition(
        quote do
          always(unquote(proposition))
        end,
        caller
      )

    quote do: {unquote(name), unquote(compiled)}
  end

  def run_simulation(module, init_arg, events, properties) do
    {state, properties, trace_rev} =
      for event <- events, reduce: init_simulation(module, init_arg, properties) do
        {state, properties, trace_rev} ->
          {state, properties} = step_simulation(module, event, state, properties)

          failed_properties = for {description, false, env} <- properties, do: {description, env}

          unless Enum.empty?(failed_properties) do
            raise ViolatedProperty,
              trace: Enum.reverse([event | trace_rev]),
              state: state,
              properties: failed_properties
          end

          unsatisfied_properties = for {_, p, _} = item <- properties, p != true, do: item

          {state, unsatisfied_properties, [event | trace_rev]}
      end

    unless Enum.empty?(properties) do
      raise ViolatedProperty,
        message: "One or more LTL properties could not be ensured",
        trace: Enum.reverse(trace_rev),
        state: state,
        properties: for({description, _, _} <- properties, do: description)
    end

    :ok
  end

  def init_simulation(module, init_arg, properties) do
    {:ok, state} = module.init(init_arg)

    properties =
      for {description, p} <- properties do
        {description, step_property(state, QuickLTL.simplify(p))}
      end

    {state, properties, []}
  end

  def step_simulation(module, event, state, properties) do
    # FIXME: support other kinds of events and other results
    {:noreply, state} = module.handle_cast(event, state)

    properties =
      for {description, p} <- properties do
        p = step_property(state, p)
        {description, p}
      end

    {state, properties}
  end

  defp step_property(state, property) do
    property |> QuickLTL.unfold() |> QuickLTL.step(%{state: state}) |> QuickLTL.simplify()
  end
end
