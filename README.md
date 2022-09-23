# QuickLTL

Infrastructure for property-testing reactive systems with specification in a linear temporal logic.
Heavily influenced by [Quickstrom](https://quickstrom.io) and the [paper](https://arxiv.org/abs/2203.11532) describing its foundations.
Currently __very experimental__ and subject to major changes.

This project __intends to be__ a pragmatic tool for testing Elixir applications with formal underpinnings and a _reasonable_ expectation of soundness.
It __does not intend to be__ formally proven sound, at least not yet.
I would rather have a lot of flexibility and interoperation with Elixir, allowing users to explore patterns that work best to test systems in a robust and understandable way.

## Installation

Since this project is very experimental, it will not be published in Hex in the foreseeable future.
Still, the package can be installed
by adding `prop_ltl` to your list of dependencies in `mix.exs`:

```elixir
def deps do
  [
    {:prop_ltl, github: "ggazzi/prop_ltl", branch: "main"}
  ]
end
```

Documentation can be generated locally with [ExDoc](https://github.com/elixir-lang/ex_doc), just run `mix docs`.
