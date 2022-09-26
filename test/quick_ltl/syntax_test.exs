defmodule QuickLTL.SyntaxTest do
  use ExUnit.Case
  import QuickLTL.Syntax
  doctest QuickLTL.Syntax

  defmacro apply_compiler(function, input) do
    escaped = Macro.escape(input)

    env = __CALLER__

    # We need to collect variables in context so they can be captured by eval_quoted
    binding =
      for {var, context} <- Macro.Env.vars(env) do
        quote do: {unquote(var), unquote(Macro.var(var, context))}
      end

    env = Macro.escape(env)

    quote do
      quoted = QuickLTL.Syntax.unquote(function)(unquote(escaped), unquote(env))
      Code.eval_quoted(quoted, unquote(binding), unquote(env)) |> elem(0)
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
