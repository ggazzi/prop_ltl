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

  describe "simplify/1" do
    property "preserves semantics of the formula" do
      check all(
              vars <- list_of(atom(:alphanumeric)),
              original <- Random.proposition(vars),
              simplified = simplify(original),
              trace <- scale(nonempty(list_of(Random.state(vars))), &min(&1, 50)),
              max_runs: 250
            ) do
        assert evaluate_naive(original, trace) == evaluate_naive(simplified, trace)
      end
    end
  end

  describe "unfold/1" do
    property "preserves semantics of the formula" do
      check all(
              vars <- list_of(atom(:alphanumeric)),
              original <- Random.proposition(vars),
              unfolded = unfold(original),
              trace <- scale(nonempty(list_of(Random.state(vars))), &max(&1, 50)),
              max_runs: 250
            ) do
        assert evaluate_naive(original, trace) == evaluate_naive(unfolded, trace)
      end
    end
  end

  describe "step/3" do
    property "preserves semantics of the formula" do
      check all(
              vars <- list_of(atom(:alphanumeric)),
              original <- Random.proposition(vars),
              first_state <- Random.state(vars),
              trace_rest <- scale(nonempty(list_of(Random.state(vars))), &min(&1, 50)),
              stepped = original |> unfold |> step(first_state),
              max_runs: 250
            ) do
        assert evaluate_naive(original, [first_state | trace_rest]) ==
                 evaluate_naive(stepped, trace_rest)
      end
    end
  end

  describe "conclude/3" do
    property "preserves semantics of the formula" do
      check all(
              vars <- list_of(atom(:alphanumeric)),
              original <- Random.proposition(vars),
              last_state <- Random.state(vars),
              concluded = original |> unfold |> conclude(last_state),
              max_runs: 250
            ) do
        assert %QuickLTL{ast: evaluate_naive(original, [last_state])} ==
                 simplify(concluded)
      end
    end

    property "result always simplifies to either true or false" do
      check all(
              vars <- list_of(atom(:alphanumeric)),
              original <- Random.proposition(vars),
              last_state <- Random.state(vars),
              concluded = original |> unfold |> conclude(last_state),
              simplified = simplify(concluded),
              max_runs: 250
            ) do
        assert is_boolean(simplified.ast)
      end
    end
  end

  describe "evaluate/3" do
    property "always results in true or false" do
      check all(
              vars <- list_of(atom(:alphanumeric)),
              p <- Random.proposition(vars),
              trace <- scale(nonempty(list_of(Random.state(vars))), &max(&1, 50)),
              max_runs: 250
            ) do
        assert is_boolean(evaluate(p, trace).ast)
      end
    end

    property "is equivalent to evaluate_naive" do
      check all(
              vars <- list_of(atom(:alphanumeric)),
              p <- Random.proposition(vars),
              trace <- scale(nonempty(list_of(Random.state(vars))), &max(&1, 50)),
              max_runs: 250
            ) do
        assert %QuickLTL{ast: evaluate_naive(p, trace)} == evaluate(p, trace)
      end
    end
  end
end
