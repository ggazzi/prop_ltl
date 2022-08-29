# QuickLTL

Infrastructure for property-testing reactive systems with specification in a linear temporal logic.
Heavily influenced by [Quickstrom](https://quickstrom.io) and the [paper](https://arxiv.org/abs/2203.11532) describing its foundations.

This project __intends to be__ a pragmatic tool for testing Elixir applications with formal underpinnings and a _reasonable_ expectation of soundness.
It __does not intend to be__ formally proven sound, at least not yet.
I would rather have a lot of flexibility and interoperation with Elixir, allowing users to explore patterns that work best to test systems in a robust and understandable way.

## Installation

If [available in Hex](https://hex.pm/docs/publish), the package can be installed
by adding `prop_ltl` to your list of dependencies in `mix.exs`:

```elixir
def deps do
  [
    {:prop_ltl, "~> 0.1.0"}
  ]
end
```

Documentation can be generated with [ExDoc](https://github.com/elixir-lang/ex_doc)
and published on [HexDocs](https://hexdocs.pm). Once published, the docs can
be found at <https://hexdocs.pm/prop_ltl>.

