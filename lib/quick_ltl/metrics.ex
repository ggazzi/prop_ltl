defmodule QuickLTL.Metrics do
  def depth(%QuickLTL{ast: ast}), do: depth(ast)
  def depth(true), do: 1
  def depth(false), do: 1
  def depth({:expr, _}), do: 1
  def depth({:let, _, p}), do: 1 + depth(p)

  def depth({op, p}) when op in [:not, :always, :eventually] do
    1 + depth(p)
  end

  def depth({op, p1, p2}) when op in [:and, :or, :implies] do
    1 + max(depth(p1), depth(p2))
  end

  def depth({:next, str, p}) when str in [:weak, :strong] do
    1 + depth(p)
  end

  def depth({:until, str, p1, p2}) when str in [:weak, :strong] do
    1 + max(depth(p1), depth(p2))
  end

  def temporal_depth(%QuickLTL{ast: ast}), do: temporal_depth(ast)
  def temporal_depth(true), do: 0
  def temporal_depth(false), do: 0
  def temporal_depth({:expr, _}), do: 0
  def temporal_depth({:let, _, p}), do: 0 + temporal_depth(p)
  def temporal_depth({:not, p}), do: temporal_depth(p)

  def temporal_depth({op, p1, p2}) when op in [:and, :or, :implies] do
    max(temporal_depth(p1), temporal_depth(p2))
  end

  def temporal_depth({op, p}) when op in [:always, :eventually] do
    1 + temporal_depth(p)
  end

  def temporal_depth({:next, str, p}) when str in [:weak, :strong] do
    1 + temporal_depth(p)
  end

  def temporal_depth({:until, str, p1, p2}) when str in [:weak, :strong] do
    1 + max(temporal_depth(p1), temporal_depth(p2))
  end

  def num_bindings(%QuickLTL{ast: ast}), do: num_bindings(ast)
  def num_bindings(true), do: 0
  def num_bindings(false), do: 0
  def num_bindings({:expr, _}), do: 0
  def num_bindings({:let, bindings, p}), do: length(bindings) + num_bindings(p)

  def num_bindings({op, p1, p2}) when op in [:and, :or, :implies] do
    num_bindings(p1) + num_bindings(p2)
  end

  def num_bindings({op, p}) when op in [:not, :always, :eventually] do
    num_bindings(p)
  end

  def num_bindings({:next, str, p}) when str in [:weak, :strong] do
    num_bindings(p)
  end

  def num_bindings({:until, str, p1, p2}) when str in [:weak, :strong] do
    num_bindings(p1) + num_bindings(p2)
  end
end
