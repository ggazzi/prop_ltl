defmodule QuickLTLTest do
  use ExUnit.Case, async: true
  use PropCheck
  import QuickLTL
  doctest QuickLTL

  alias QuickLTL.Metrics
  alias QuickLTL.Random
  alias QuickLTL.Syntax

  property "printing and parsing roundtrip", max_size: 50, numtests: 500 do
    # This tests the compatibility of four things:
    #    1. Syntax.proposition_to_quoted/1
    #    2. Syntax.compile_proposition/2
    #    3. Random.proposition/1
    #    4. evaluate_naive/2

    data =
      let [
        env <- Random.Env.global(),
        original <- Random.proposition(^env),
        trace <- Random.trace(^env)
      ] do
        {original, trace}
      end

    forall {original, trace} <- data do
      quoted = Syntax.proposition_to_quoted(original.ast)
      {compiled, _} = Code.eval_quoted(Syntax.compile_proposition(quoted, __ENV__))

      (Syntax.proposition_to_quoted(compiled) === quoted and
         evaluate_naive(original, trace) === evaluate_naive(compiled, trace))
      |> Random.collect_metric(:depth, Metrics.depth(original), 5)
      |> Random.collect_metric(:num_bindings, Metrics.num_bindings(original), 5)
    end
  end
end
