defmodule QuickLTLTest do
  use ExUnit.Case
  use ExUnitProperties
  import QuickLTL
  doctest QuickLTL

  alias QuickLTL.Random
  alias QuickLTL.Syntax

  property "printing and parsing roundtrip" do
    # This tests the compatibility of four things:
    #    1. Syntax.proposition_to_quoted/1
    #    2. Syntax.compile_proposition/2
    #    3. Random.proposition/1
    #    4. evaluate_naive/2
    check all(
            vars <- list_of(atom(:alphanumeric)),
            original <- Random.proposition(vars),
            quoted = Syntax.proposition_to_quoted(original.ast),
            {compiled, _} = Code.eval_quoted(Syntax.compile_proposition(quoted, __ENV__)),
            trace <- scale(nonempty(list_of(Random.state(vars))), &min(&1, 50)),
            max_runs: 250
          ) do
      assert Syntax.proposition_to_quoted(compiled) == quoted
      assert evaluate_naive(original, trace) == evaluate_naive(compiled, trace)
    end
  end
end
