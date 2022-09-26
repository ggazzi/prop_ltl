defmodule QuickLTL.SyntaxTest do
  use ExUnit.Case
  import QuickLTL.Syntax
  doctest QuickLTL.Syntax

  defmacro apply_compiler(function, input) do
    escaped = Macro.escape(input)
    env = __CALLER__

    # We need to collect variables in context so they can be captured by eval_quoted
    binding =
      for {var, context} when is_atom(context) or is_integer(context) <- Macro.Env.vars(env) do
        quote do: {unquote(var), unquote(Macro.var(var, context))}
      end

    env = Macro.escape(env)

    quote do
      quoted = QuickLTL.Syntax.unquote(function)(unquote(escaped), unquote(env))
      Code.eval_quoted(quoted, unquote(binding), unquote(env)) |> elem(0)
    end
  end

  describe "compile_proposition/2" do
    test "works for constant booleans" do
      assert apply_compiler(compile_proposition, true) == true
      assert apply_compiler(compile_proposition, false) == false
    end

    test "works for the usual boolean operators" do
      assert apply_compiler(compile_proposition, not true) == {:not, true}
      assert apply_compiler(compile_proposition, true and false) == {:and, true, false}
      assert apply_compiler(compile_proposition, true or false) == {:or, true, false}
      assert apply_compiler(compile_proposition, if(true, do: false)) == {:implies, true, false}
    end

    test "works for the temporal connectives" do
      assert apply_compiler(compile_proposition, next_weak(true)) == {:next, :weak, true}
      assert apply_compiler(compile_proposition, next_strong(true)) == {:next, :strong, true}
      assert apply_compiler(compile_proposition, always(true)) == {:always, true}
      assert apply_compiler(compile_proposition, eventually(true)) == {:eventually, true}

      assert apply_compiler(compile_proposition, until_weak(true, false)) ==
               {:until, :weak, true, false}

      assert apply_compiler(compile_proposition, until_strong(true, false)) ==
               {:until, :strong, true, false}
    end

    test "does not support else-blocks" do
      assert_raise CompileError, fn ->
        apply_compiler(compile_proposition, if(true, do: false, else: true))
      end
    end

    test "evaluates expressions capturing variables from Elixir scope, state and logical environment" do
      foo = 40
      {:expr, {eval, _src}} = apply_compiler(compile_proposition, foo + bar - baz)
      assert eval.(%{bar: 4}, %{baz: 2}) == 42
    end

    test "suppports let-expressions to extend the logical environment" do
      foo = 40

      {:let, [answer: {:expr, {eval, _src}}], true} =
        apply_compiler(
          compile_proposition,
          let answer: foo + bar - baz do
            true
          end
        )

      assert eval.(%{bar: 4}, %{baz: 2}) == 42
    end

    test "suppports let-expressions with multiple bindings" do
      foo = 40

      {:let, binders, true} =
        apply_compiler(
          compile_proposition,
          let one: 1, two: 2, three: 3 do
            true
          end
        )

      {:expr, {eval, _}} = binders[:one]
      assert eval.(%{}, %{}) == 1

      {:expr, {eval, _}} = binders[:two]
      assert eval.(%{}, %{}) == 2

      {:expr, {eval, _}} = binders[:three]
      assert eval.(%{}, %{}) == 3
    end

    test "preserves pins" do
      assert_raise CompileError, ~r/cannot use \^foobar outside of match clauses/, fn ->
        apply_compiler(compile_proposition, ^foobar)
      end
    end

    test "embeds Elixir values with the &-operator" do
      ref = make_ref()
      assert apply_compiler(compile_proposition, true and (&ref)) == {:and, true, ref}
    end
  end

  describe "compile_native_expr/2" do
    test "works with constant expressions" do
      {eval, _src} = apply_compiler(compile_native_expr, 1 + 1)
      assert eval.(%{}, %{}) == 2
    end

    test "captures variables from the Elixir scope" do
      foo = :bar
      {eval, _src} = apply_compiler(compile_native_expr, foo)
      assert eval.(%{}, %{}) == :bar
    end

    test "captures variables from the state and logical environment" do
      {eval, _src} = apply_compiler(compile_native_expr, foo - bar)
      assert eval.(%{foo: 42}, %{bar: 2}) == 40
    end

    test "variables from the Elixir scope take precedence over state and logical environment" do
      foo = :bar
      {eval, _src} = apply_compiler(compile_native_expr, foo)
      assert eval.(%{foo: :baz}, %{foo: 42}) == :bar
    end

    test "variables from the logical environment take precedence over state" do
      {eval, _src} = apply_compiler(compile_native_expr, foo)
      assert eval.(%{foo: :baz}, %{foo: 42}) == 42
    end

    test "raises an error when pinned variables are undefined" do
      {eval, _src} = apply_compiler(compile_native_expr, foo - bar)

      assert_raise KeyError, ~r/:foo/, fn ->
        eval.(%{bar: 2}, %{})
      end
    end
  end
end
