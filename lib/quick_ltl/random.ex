defmodule QuickLTL.Random do
  import StreamData
  alias QuickLTL.Syntax

  def proposition(vars) do
    atom = map(native_expr_boolean(vars), &{:expr, &1})

    ast =
      tree(atom, fn child_gen ->
        variants = [
          {:not, child_gen},
          {:and, child_gen, child_gen},
          {:or, child_gen, child_gen},
          {:implies, child_gen, child_gen},
          {:next, member_of([:weak, :strong]), child_gen},
          {:always, child_gen},
          {:eventually, child_gen},
          {:until, member_of([:weak, :strong]), child_gen, child_gen}
        ]

        one_of(
          if Enum.empty?(vars) do
            variants
          else
            binder = {member_of(vars), {:expr, native_expr_boolean(vars)}}

            [
              {:let, nonempty(list_of(binder)), child_gen},
              {:recv, native_recv(vars)},
              {:recv, native_recv(vars), child_gen},
              {:if_recv, native_recv(vars), child_gen}
              | variants
            ]
          end
        )
      end)

    map(ast, &%QuickLTL{ast: &1})
  end

  def state(vars) do
    map(fixed_list(for var <- vars, do: map(boolean(), &{var, &1})), &Map.new/1)
  end

  def native_recv(vars) do
    var = map(member_of(vars), &Macro.var(&1, __MODULE__))
    pattern = one_of([var, map(var, &quote(do: ^unquote(&1)))])

    map(pattern, fn quoted ->
      recv = Syntax.compile_native_recv(quoted, make_custom_env())
      Code.eval_quoted(recv) |> elem(0)
    end)
  end

  def native_expr_boolean(vars) do
    vars = Enum.filter(vars, &(&1 != :_))
    constant = map(member_of([true, false]), &{fn _, _ -> &1 end, &1})

    if Enum.empty?(vars) do
      constant
    else
      one_of([
        constant,
        map(member_of(vars), fn var ->
          {
            fn state, env -> Map.get_lazy(env, var, fn -> Map.get(state, var) end) end,
            Macro.var(var, __MODULE__)
          }
        end)
      ])
    end
  end

  def make_custom_env do
    __ENV__
  end
end
