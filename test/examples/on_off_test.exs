defmodule OnOffTest do
  use ExUnit.Case
  use ExUnitProperties
  import GenServerLTL
  import QuickLTL

  property "satisfies the LTL specification" do
    event =
      one_of([
        constant(
          {:cast, :toggle,
           prop do
             let prev: state, do: next_strong(state.on? == not prev.on?)
           end}
        ),
        gen all(on? <- boolean()) do
          {:cast, {:set, on?}, prop(next_strong state.on? == on?)}
        end
      ])

    timeout = constant({:info, :timeout})

    trace =
      gen(
        all(
          prefix <- list_of(one_of([event, timeout])),
          last <- event
        ),
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
