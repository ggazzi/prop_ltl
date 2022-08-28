defmodule QuickLTL.Random do
  import StreamData

  def proposition(vars) do
    atom = map(boolean_atom_evaluator(vars), &{:expr, &1})

    # TODO: generate propositions that actually extend the scope with let

    tree(atom, fn child_gen ->
      variants = [
        {:not, child_gen},
        {:and, child_gen, child_gen},
        {:or, child_gen, child_gen},
        {:implies, child_gen, child_gen},
        {:next, member_of([:weak, :strong]), child_gen},
        {:always, child_gen},
        {:eventually, child_gen},
        {:until, child_gen, child_gen},
        {:weak_until, child_gen, child_gen}
      ]

      one_of(
        if Enum.empty?(vars) do
          variants
        else
          binder = {member_of(vars), boolean_atom_evaluator(vars)}
          [{:let, list_of(binder), child_gen} | variants]
        end
      )
    end)
  end

  def state(vars) do
    map(fixed_list(for var <- vars, do: map(boolean(), &{var, &1})), &Map.new/1)
  end

  def boolean_atom_evaluator(vars) do
    constant = map(member_of([true, false]), &{fn _, _ -> &1 end, &1})

    if Enum.empty?(vars) do
      constant
    else
      one_of([
        constant,
        map(member_of(vars), fn var ->
          {
            fn state, env -> Map.get_lazy(env, var, fn -> Map.get(state, var) end) end,
            var
          }
        end)
      ])
    end
  end
end
