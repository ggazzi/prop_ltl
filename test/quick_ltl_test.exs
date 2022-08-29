defmodule QuickLTLTest do
  use ExUnit.Case
  use ExUnitProperties
  import QuickLTL
  doctest QuickLTL

  alias QuickLTL.Random
  alias QuickLTL.Syntax

  property "printing and parsing roundtrip" do
    # This tests the compatibility of three things:
    #    1. Syntax.proposition_to_quoted
    #    2. Syntax.compile_proposition
    #    3. Random.proposition
    check all(
            vars <- list_of(atom(:alphanumeric)),
            original <- Random.proposition(vars),
            quoted = Syntax.proposition_to_quoted(original),
            {compiled, _} = Code.eval_quoted(Syntax.compile_proposition(quoted, __ENV__))
          ) do
      assert Syntax.proposition_to_quoted(compiled) == quoted

      check all(trace <- nonempty(list_of(Random.state(vars)))) do
        assert evaluate_naive(original, trace) == evaluate_naive(compiled, trace)
      end
    end
  end
end
