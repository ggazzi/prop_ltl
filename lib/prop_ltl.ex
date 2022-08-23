defmodule PropLTL do
  alias PropLTL.Proposition, as: Proposition

  def init_simulation(module, init_arg, property) do
    {:ok, state} = module.init(init_arg)

    {state, step_property(state, {Proposition.simplify(property), %{state: state}})}
  end

  def step_simulation(module, event, state, prop) do
    {:noreply, state} = module.handle_cast(event, state)
    {state, step_property(state, prop)}
  end

  defp step_property(state, {property, env}) do
    {property, env} = Proposition.step(Proposition.unfold(property), %{env | state: state})
    property = Proposition.simplify(property)
    {property, env}
  end
end
