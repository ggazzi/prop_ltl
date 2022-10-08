defmodule QuickLTL.SemanticsTest do
  use ExUnit.Case, async: true
  use PropCheck
  import QuickLTL

  alias QuickLTL.Random
  alias QuickLTL.Syntax
  import QuickLTL.Metrics

  describe "simplify/1" do
    property "preserves semantics of the formula", max_size: 30, numtests: 250 do
      data =
        let [
          env <- Random.Env.global(),
          proposition <- Random.proposition(^env),
          trace <- Random.trace(^env)
        ] do
          {proposition, trace}
        end

      forall {proposition, trace} <- data do
        (evaluate_naive(proposition, trace) ===
           evaluate_naive(simplify(proposition), trace))
        |> Random.collect_metric(:trace_len, length(trace), 10)
        |> Random.collect_metric(:depth, depth(proposition), 5)
        |> Random.collect_metric(:temporal_depth, temporal_depth(proposition), 5)
        |> Random.collect_metric(:num_binders, num_bindings(proposition), 5)
      end
    end
  end

  describe "unfold/1" do
    property "always produces a guarded formula" do
      proposition =
        let [
              env <- Random.Env.global(),
              proposition <- Random.proposition(^env)
            ],
            do: proposition

      forall p <- proposition do
        Syntax.guarded?(unfold(p))
      end
    end

    property "preserves semantics of the formula", max_size: 30, numtests: 250 do
      data =
        let [
          env <- Random.Env.global(),
          proposition <- Random.proposition(^env),
          trace <- Random.trace(^env)
        ] do
          {proposition, trace}
        end

      forall {proposition, trace} <- data do
        (evaluate_naive(proposition, trace) ===
           evaluate_naive(unfold(proposition), trace))
        |> Random.collect_metric(:trace_len, length(trace), 10)
        |> Random.collect_metric(:depth, depth(proposition), 5)
        |> Random.collect_metric(:temporal_depth, temporal_depth(proposition), 5)
        |> Random.collect_metric(:num_binders, num_bindings(proposition), 5)
      end
    end
  end

  describe "step/3" do
    property "preserves semantics of the formula", max_size: 30, numtests: 250 do
      data =
        let [
          env <- Random.Env.global(),
          proposition <- Random.proposition(^env),
          first_state <- Random.state(^env),
          trace_rest <- Random.trace(^env)
        ] do
          {proposition, [first_state | trace_rest]}
        end

      forall {proposition, [first_state | trace_rest] = trace} <- data do
        (evaluate_naive(proposition, trace) ===
           evaluate_naive(proposition |> unfold() |> step(first_state), trace_rest))
        |> Random.collect_metric(:trace_len, length(trace), 10)
        |> Random.collect_metric(:depth, depth(proposition), 5)
        |> Random.collect_metric(:temporal_depth, temporal_depth(proposition), 5)
        |> Random.collect_metric(:num_binders, num_bindings(proposition), 5)
      end
    end
  end

  describe "conclude/3" do
    property "result always simplifies to either true or false" do
      data =
        let [
              env <- Random.Env.global(),
              proposition <- Random.proposition(^env),
              last_state <- Random.state(^env)
            ],
            do: {proposition, last_state}

      forall {proposition, last_state} <- data do
        is_boolean((proposition |> unfold() |> conclude(last_state) |> simplify).ast)
      end
    end

    property "preserves semantics of the formula", max_size: 30, numtests: 250 do
      data =
        let [
          env <- Random.Env.global(),
          proposition <- Random.proposition(^env),
          last_state <- Random.state(^env)
        ] do
          {proposition, last_state}
        end

      forall {proposition, last_state} <- data do
        (evaluate_naive(proposition, [last_state]) ===
           (proposition |> unfold() |> conclude(last_state) |> simplify()).ast)
        |> Random.collect_metric(:depth, depth(proposition), 5)
        |> Random.collect_metric(:temporal_depth, temporal_depth(proposition), 5)
        |> Random.collect_metric(:num_binders, num_bindings(proposition), 5)
      end
    end
  end

  describe "evaluate/3" do
    property "always results in true or false" do
      data =
        let [
              env <- Random.Env.global(),
              p <- Random.proposition(^env),
              trace <- Random.trace(^env)
            ],
            do: {p, trace}

      forall {p, trace} <- data do
        is_boolean(evaluate(p, trace).ast)
      end
    end

    property "is equivalent to evaluate_naive", max_size: 30, numtests: 250 do
      data =
        let [
              env <- Random.Env.global(),
              p <- Random.proposition(^env),
              trace <- Random.trace(^env)
            ],
            do: {p, trace}

      forall {p, trace} <- data do
        %QuickLTL{ast: evaluate_naive(p, trace)} === evaluate(p, trace)
      end
    end
  end
end
