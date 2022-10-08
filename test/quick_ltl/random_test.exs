defmodule QuickLTLTest do
  use ExUnit.Case, async: true
  use PropCheck
  import QuickLTL
  import QuickLTL.Random
  doctest QuickLTL.Random

  describe "proposition/1" do
    property "always generates valid QuickLTL propositions" do
      prop =
        let [
              env <- QuickLTL.Random.Env.global(),
              proposition <- proposition(^env)
            ],
            do: proposition

      forall p <- prop do
        QuickLTL.Syntax.valid?(p)
      end
    end
  end
end
