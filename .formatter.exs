# Used by "mix format"
[
  inputs: ["{mix,.formatter}.exs", "{config,lib,test,examples}/**/*.{ex,exs}"],
  locals_without_parens: [
    property: 2,
    invariant: 2,
    let: :*,
    next_weak: 1,
    next_strong: 1,
    always: 1,
    eventually: 1,
    until_strong: 2,
    until_weak: 2
  ]
]
