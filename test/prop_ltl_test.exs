defmodule PropLTLTest do
  use ExUnit.Case
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
    test "with satisfied proposition" do
      assert :ok ==
               run_simulation(
                 OnOff,
                 self(),
                 [:toggle],
                 properties do
                   property "the lights are eventually turned on" do
                     eventually(state.on?)
                   end
                 end
               )
    end

    test "with unsatisfied proposition" do
      assert_raise PropLTL.ViolatedProperty, ~r/lights are eventually turned on/, fn ->
        run_simulation(
          OnOff,
          self(),
          [:off, :off],
          properties do
            property "the lights are eventually turned on" do
              eventually(state.on?)
            end
          end
        )
      end
    end
  end
end
