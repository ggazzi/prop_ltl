defmodule PropLTLTest do
  use ExUnit.Case
  import PropLTL.Proposition
  import PropLTL
  doctest PropLTL

  defmodule OnOff do
    use GenServer

    @impl true
    def init(observer) do
      {:ok, %{observer: observer, on?: false}}
    end

    @impl true
    def handle_cast(event, state) do
      new_state = handle_event(event, state)
      send_effects(state, new_state)
      {:noreply, new_state}
    end

    defp handle_event(:toggle, state) do
      %{state | on?: not state.on?}
    end

    defp handle_event(:on, state) do
      %{state | on?: true}
    end

    defp handle_event(:off, state) do
      %{state | on?: false}
    end

    defp send_effects(curr, next) do
      if next.on? != curr.on? do
        send(next.observer, {:set_lights, next.on?})
      end
    end
  end

  describe "OnOff" do
    test "try some steps" do
      property =
        prop do
          always do
            state.on? -- eventually(not state.on?)
          end
        end

      property =
        prop do
          eventually(state.on?)
        end

      {state, {p, env}} = init_simulation(OnOff, self(), property)
      assert p == property

      {state, {p, env}} = step_simulation(OnOff, :toggle, state, {p, env})
      assert p == true
    end
  end
end
