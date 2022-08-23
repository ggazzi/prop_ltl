defmodule PropLTL do
  import ExUnit.Assertions
  alias PropLTL.Proposition, as: Proposition

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

  def run_simulation(module, init_arg, events, properties) do
    {state, properties, trace_rev} =
      for event <- events, reduce: init_simulation(module, init_arg, properties) do
        {state, properties, trace_rev} ->
          {state, properties} = step_simulation(module, event, state, properties)

          failed_properties = for {description, false, env} <- properties, do: {description, env}

          unless Enum.empty?(failed_properties) do
            raise ViolatedProperty,
              trace: Enum.reverse(trace_rev),
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
        {p, env} = step_property(state, Proposition.simplify(p), %{state: state})
        {description, p, env}
      end

    {state, properties, []}
  end

  def step_simulation(module, event, state, properties) do
    # FIXME: support other kinds of events and other results
    {:noreply, state} = module.handle_cast(event, state)

    properties =
      for {description, p, env} <- properties do
        {p, env} = step_property(state, p, %{env | state: state})
        {description, p, env}
      end

    {state, properties}
  end

  defp step_property(state, property, env) do
    {property, env} = Proposition.step(Proposition.unfold(property), %{env | state: state})
    property = Proposition.simplify(property)
    {property, env}
  end
end
