defmodule OnOffTest do
  use ExUnit.Case
  use ExUnitProperties
  import GenServerLTL
  import QuickLTL

  import OnOff
  doctest OnOff

  property "satisfies the LTL specification" do
    event = one_of([{:cast, :toggle}, {:cast, {:set, boolean()}}])

    trace =
      gen(all(prefix <- list_of(one_of([event, {:info, :timeout}])), last <- event),
        do: prefix ++ [last]
      )

    check all(events <- trace, initial_size: 10) do
      run_execution(
        OnOff,
        self(),
        events,
        properties do
          property "starts turned off", not state.on?

          invariant "doesn't remain on forever" do
            if state.on?, do: eventually(not state.on?)
          end
        end
      )
    end
  end
end
