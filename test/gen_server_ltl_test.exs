defmodule GenServerLTLTest do
  use ExUnit.Case
  import ExUnitProperties
  import StreamData

  import GenServerLTL
  import QuickLTL
  doctest GenServerLTL

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
      assert_raise GenServerLTL.ViolatedProperty, ~r/lights are eventually turned on/, fn ->
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

    test "with violated proposition" do
      assert_raise GenServerLTL.ViolatedProperty, ~r/the lights remain off forever/, fn ->
        run_simulation(
          OnOff,
          self(),
          [:off, :toggle, :toggle],
          properties do
            invariant("the lights remain off forever", do: not state.on?)
          end
        )
      end
    end

    test "with generated trace" do
      # initial_size: 20
      check all(
              trace <- StreamData.list_of(StreamData.one_of([:on, :off, :toggle])),
              length(trace) > 5,
              initial_size: 20,
              max_runs: 1000
            ) do
        run_simulation(
          OnOff,
          self(),
          trace,
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
