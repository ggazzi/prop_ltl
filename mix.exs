defmodule QuickLTL.MixProject do
  use Mix.Project

  def project do
    [
      app: :quick_ltl,
      version: "0.1.0",
      elixir: "~> 1.13",
      start_permanent: Mix.env() == :prod,
      deps: deps(),
      elixirc_paths:
        case Mix.env() do
          :test -> ["lib", "examples"]
          _ -> ["lib"]
        end
    ]
  end

  # Run "mix help compile.app" to learn about applications.
  def application do
    [
      extra_applications: [:logger]
    ]
  end

  # Run "mix help deps" to learn about dependencies.
  defp deps do
    [
      {:stream_data, "~> 0.5.0"},
      {:ex_doc, "~> 0.27", only: [:dev], runtime: false},
      {:dialyxir, "~> 1.0", only: [:dev], runtime: false},
      {:propcheck, "~> 1.4", only: [:test, :dev]}
    ]
  end
end
