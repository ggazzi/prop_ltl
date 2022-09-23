defmodule GenServerLTL do
  defmodule ViolatedProperty do
    defexception message: "One or more LTL properties were violated",
                 trace: nil,
                 state: nil,
                 properties: nil

    @impl true
    def message(exception) do
      trace = inspect(exception.trace, pretty: true)
      state = inspect(exception.state, pretty: true)
      properties = inspect(exception.properties, pretty: true)

      "#{exception.message}\n  trace: #{trace}\n  state: #{state}\n  violated properties: #{properties}"
    end
  end

  defmodule ServerStopped do
    defexception message: "The GenServer stopped unexpectedly",
                 reason: nil,
                 trace: nil,
                 state: nil

    @impl true
    def message(exception) do
      reason = inspect(exception.reason, pretty: true)
      trace = inspect(exception.trace, pretty: true)
      state = inspect(exception.state, pretty: true)

      "#{exception.message}\n  reason: #{reason}\n  trace: #{trace}\n  state: #{state}"
    end
  end

  defmacro properties(do: props) do
    # TODO: forbid the variable "state" from being captured by the environment
    compile_properties(props, __CALLER__)
  end

  def compile_properties({kind, _, [_name, _proposition]} = decl, caller)
      when kind in [:property, :invariant] do
    quote do: [unquote(compile_property(decl, caller))]
  end

  def compile_properties({:__block__, _, properties}, caller) do
    properties = properties |> Enum.map(&compile_property(&1, caller))
    quote do: [unquote_splicing(properties)]
  end

  defp compile_property({:property, _, [name, proposition]}, caller) do
    compiled = QuickLTL.Syntax.compile_proposition(proposition, caller)
    quote do: {unquote(name), %QuickLTL{ast: unquote(compiled)}}
  end

  defp compile_property({:invariant, _, [name, proposition]}, caller) do
    compiled =
      QuickLTL.Syntax.compile_proposition(
        quote do
          always(unquote(proposition))
        end,
        caller
      )

    quote do: {unquote(name), %QuickLTL{ast: unquote(compiled)}}
  end

  def run_execution(module, init_arg, events, properties) do
    run_execution(events, init_execution(module, init_arg, properties))
  end

  def run_execution([final_event], state) do
    conclude_execution(final_event, state)
  end

  def run_execution([event | future_events], state) do
    run_execution(future_events, step_execution(event, state))
  end

  def init_execution(module, init_arg, properties) do
    {:ok, server_state} = module.init(init_arg)

    initial_state = %{
      server_module: module,
      server_state: server_state,
      expects_timeout?: false,
      status: :running,
      properties: Enum.map(properties, fn {descr, p} -> {descr, QuickLTL.simplify(p)} end),
      trace_rev: []
    }

    step_properties(initial_state, &QuickLTL.step/2)
  end

  def step_execution({:info, :timeout} = event, state) do
    if state.expects_timeout? do
      state |> step_server(event) |> step_properties(&QuickLTL.step/2)
    else
      state
    end
  end

  def step_execution(event, state) do
    state |> step_server(event) |> step_properties(&QuickLTL.step/2)
  end

  def conclude_execution(final_event, state) do
    final_state = state |> step_server(final_event) |> inject_final_timeouts()

    unless Enum.empty?(final_state.properties) do
      raise ViolatedProperty,
        message: "One or more LTL properties could not be ensured",
        trace: Enum.reverse(final_state.trace_rev),
        state: final_state.server_state,
        properties: for({description, _} <- final_state.properties, do: description)
    end

    final_state
  end

  defp inject_final_timeouts(state) do
    if state.expects_timeout? do
      state
      |> step_properties(&QuickLTL.step/2)
      |> step_server({:info, :timeout})
      |> inject_final_timeouts()
    else
      state |> step_properties(&QuickLTL.conclude/2)
    end
  end

  defp step_server(state, event) do
    # TODO: expose a {:reply, reply} as a logical variable
    # TODO: support {:continue, continue} as part of the response
    new_state =
      case process_event(event, state) do
        {:reply, _reply, new_state} ->
          %{state | server_state: new_state, expects_timeout?: false}

        {:reply, _reply, new_state, atom} when atom in [:hibernate, :infinity] ->
          %{state | server_state: new_state, expects_timeout?: false}

        {:reply, _reply, new_state, :infinity} ->
          %{state | server_state: new_state, expects_timeout?: false}

        {:reply, _reply, new_state, timeout} when is_number(timeout) ->
          %{state | server_state: new_state, expects_timeout?: true}

        {:noreply, new_state} ->
          %{state | server_state: new_state, expects_timeout?: false}

        {:noreply, new_state, atom} when atom in [:hibernate, :infinity] ->
          %{state | server_state: new_state, expects_timeout?: false}

        {:noreply, new_state, timeout} when is_number(timeout) ->
          %{state | server_state: new_state, expects_timeout?: true}

        {:stop, reason, _reply, new_state} ->
          %{state | server_state: new_state, expects_timeout?: true, status: {:stopped, reason}}

        {:stop, reason, new_state} ->
          %{state | server_state: new_state, expects_timeout?: true, status: {:stopped, reason}}
      end

    new_state = %{new_state | trace_rev: [event | state.trace_rev]}

    case new_state.status do
      :running ->
        new_state

      {:stopped, reason} ->
        raise ServerStopped,
          reason: reason,
          state: new_state.server_state,
          trace: Enum.reverse(new_state.trace_rev)
    end
  end

  defp process_event(event, %{server_module: module, server_state: server_state}) do
    case event do
      {:call, payload} -> module.handle_call(payload, {self(), make_ref()}, server_state)
      {:cast, payload} -> module.handle_cast(payload, server_state)
      {:info, payload} -> module.handle_info(payload, server_state)
    end
  end

  defp step_properties(state, stepper) do
    stepped_properties =
      for {name, p} <- state.properties do
        {name,
         p
         |> QuickLTL.unfold()
         |> stepper.(%{state: state.server_state})
         |> QuickLTL.simplify()}
      end

    {failed_properties, pending_properties} =
      Enum.split_with(stepped_properties, fn {_, p} -> p.ast == false end)

    unless Enum.empty?(failed_properties) do
      raise ViolatedProperty,
        trace: Enum.reverse(state.trace_rev),
        state: state.server_state,
        properties: failed_properties
    end

    %{state | properties: Enum.filter(pending_properties, fn {_, p} -> p.ast != true end)}
  end
end
