defmodule OnOff do
  use GenServer

  @impl true
  def init(subscriber) do
    {:ok, %{subscriber: subscriber, on?: false, timeout_event: nil}}
  end

  @impl true
  def handle_cast(event, state) do
    new_state = react_to_event(event, state)

    case determine_timeout(new_state) do
      nil ->
        {:noreply, %{new_state | timeout_event: nil}}

      {timeout, event} ->
        {:noreply, %{new_state | timeout_event: event}, timeout}
    end
  end

  @impl true
  def handle_info(:timeout, state) do
    {:noreply, %{state | on?: false, timeout_event: nil}}
  end

  defp react_to_event({:set, on?}, state) do
    %{state | on?: on?}
  end

  defp react_to_event(:toggle, state) do
    %{state | on?: not state.on?}
  end

  @light_timeout 5 * 60 * 1000

  def determine_timeout(state) do
    if state.on? do
      {@light_timeout, {:set, false}}
    end
  end
end
