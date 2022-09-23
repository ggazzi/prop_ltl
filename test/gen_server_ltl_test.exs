defmodule GenServerLTLTest do
  use ExUnit.Case
  import ExUnitProperties
  import StreamData

  import GenServerLTL
  import QuickLTL
  doctest GenServerLTL

  describe "init_execution/3" do
    defmodule DummyServer_init_execution do
      use GenServer

      @impl true
      def init(arg) do
        {:ok, %{init_arg: arg}}
      end
    end

    alias DummyServer_init_execution, as: DummyServer

    test "calls the GenServer's init with the appropriate argument" do
      ref = make_ref()
      state = init_execution(DummyServer, ref, [])

      assert state.server_state == %{init_arg: ref}
    end

    test "starts with status = :running, empty trace and not expecting a timeout" do
      state = init_execution(DummyServer, self(), [])

      assert state.status == :running
      assert Enum.empty?(state.trace_rev)
      assert not state.expects_timeout?
    end

    test "steps and simplifies all properties with the initial state" do
      state =
        init_execution(
          DummyServer,
          false,
          properties do
            property "very simple",
                     next_weak(state.init_arg and true) or false

            property "eventually" do
              if not state.init_arg do
                eventually state.init_arg
              end
            end

            invariant "invariant", not state.init_arg
          end
        )

      assert match?(
               prop(&{:expr, _}),
               find_prop("very simple", state)
             )

      assert match?(
               prop(always not _),
               find_prop("invariant", state)
             )

      assert match?(
               prop(eventually _),
               find_prop("eventually", state)
             )
    end

    test "removes properties that are already satisfied" do
      ref = make_ref()

      state =
        init_execution(
          DummyServer,
          ref,
          properties do
            property "initial condition", state.init_arg == ref
            invariant "doesn't change", state.init_arg == ref
          end
        )

      assert find_prop("initial_condition", state) == nil
      assert match?(prop(always &{:expr, _}), find_prop("doesn't change", state))
    end

    test "raises an exception if any property has been violated" do
      ref = make_ref()

      assert_raise GenServerLTL.ViolatedProperty, ~r/fails immediately/, fn ->
        init_execution(
          DummyServer,
          ref,
          properties do
            invariant "fails immediately", state.init_arg != ref
          end
        )
      end
    end
  end

  describe "step_execution/2" do
    defmodule DummyServer_step_execution do
      use GenServer

      @impl true
      def init(state) do
        {:ok, state}
      end

      @impl true
      def handle_call(event, _from, _state) do
        new_state = {:call, event[:payload]}

        case {event[:stop], event[:reply], event[:timeout]} do
          {nil, nil, nil} -> {:noreply, new_state}
          {nil, nil, timeout} -> {:noreply, new_state, timeout}
          {nil, reply, nil} -> {:reply, reply, new_state}
          {nil, reply, timeout} -> {:reply, reply, new_state, timeout}
          {reason, nil, _} -> {:stop, reason, new_state}
          {reason, reply, _} -> {:stop, reason, reply, new_state}
        end
      end

      @impl true
      def handle_cast(event, _state) do
        new_state = {:cast, event[:payload]}

        case {event[:stop], event[:timeout]} do
          {nil, nil} -> {:noreply, new_state}
          {nil, timeout} -> {:noreply, new_state, timeout}
          {reason, _} -> {:stop, reason, new_state}
        end
      end

      @impl true
      def handle_info(event, _state) do
        new_state = {:info, event[:payload]}

        case {event[:stop], event[:timeout]} do
          {nil, nil} -> {:noreply, new_state}
          {nil, timeout} -> {:noreply, new_state, timeout}
          {reason, _} -> {:stop, reason, new_state}
        end
      end
    end

    alias DummyServer_step_execution, as: DummyServer

    def timeout do
      unshrinkable(one_of([nil, positive_integer(), :infinity, :hibernate]))
    end

    test "dispatches the event to the right handler" do
      state_before = init_execution(DummyServer, nil, [])

      check all(kind <- one_of([:cast, :info, :call]), payload <- binary()) do
        state_after = step_execution({kind, %{payload: payload}}, state_before)
        assert state_after.server_state == {kind, payload}
      end
    end

    test "adjusts the trace and expectations of timeout appropriately" do
      state_before = init_execution(DummyServer, nil, [])

      check all(
              kind <- one_of([:cast, :info, :call]),
              payload <- binary(),
              timeout <- timeout(),
              trace_before = list_of(binary()),
              expected_timeout_before <- boolean()
            ) do
        state_before = %{
          state_before
          | trace_rev: trace_before,
            expects_timeout?: expected_timeout_before
        }

        event = {kind, %{payload: payload, timeout: timeout}}
        state_after = step_execution(event, state_before)

        assert state_after.trace_rev == [event | trace_before]

        if timeout in [nil, :infinity, :hibernate] do
          refute state_after.expects_timeout?
        else
          assert state_after.expects_timeout?
        end
      end
    end

    test "raises an exception if the server stops" do
      state_before = init_execution(DummyServer, nil, [])

      check all(
              kind <- one_of([:cast, :info, :call]),
              payload <- binary(),
              reason <- string(:alphanumeric)
            ) do
        event = {kind, %{payload: payload, stop: reason}}

        assert_raise GenServerLTL.ServerStopped, ~r/#{inspect(reason)}/, fn ->
          step_execution(event, state_before)
        end
      end
    end

    test "steps the evaluation of the properties" do
      state_0 =
        init_execution(
          DummyServer,
          0,
          properties do
            property "succeeds in two", next_weak(next_weak state == 2)
          end
        )

      assert match?(
               prop(next_weak &{:expr, _}),
               find_prop("succeeds in two", state_0)
             )

      for kind <- [:cast, :info, :call] do
        state_1 = step_execution({kind, %{payload: 1}}, state_0)
        assert match?(prop(&{:expr, _}), find_prop("succeeds in two", state_1))
      end
    end

    test "removes properties that have been satisfied" do
      for kind <- [:cast, :info, :call] do
        state_0 =
          init_execution(
            DummyServer,
            0,
            properties do
              property "succeeds in two",
                       next_weak(next_weak(state == {kind, 2}))
            end
          )

        assert match?(
                 prop(next_weak &{:expr, _}),
                 find_prop("succeeds in two", state_0)
               )

        state_1 = step_execution({kind, %{payload: 1}}, state_0)
        assert match?(prop(&{:expr, _}), find_prop("succeeds in two", state_1))

        state_2 = step_execution({kind, %{payload: 2}}, state_1)
        assert state_2.properties == []
      end
    end

    test "raises an exception if a property has been violated" do
      for kind <- [:cast, :info, :call] do
        state_0 =
          init_execution(
            DummyServer,
            0,
            properties do
              property "fails in two" do
                next_weak(next_weak state != {kind, 2})
              end
            end
          )

        assert match?(
                 prop(next_weak &{:expr, _}),
                 find_prop("fails in two", state_0)
               )

        state_1 = step_execution({kind, %{payload: 1}}, state_0)
        assert match?(prop(&{:expr, _}), find_prop("fails in two", state_1))

        assert_raise GenServerLTL.ViolatedProperty, ~r/fails in two/, fn ->
          step_execution({kind, %{payload: 2}}, state_1)
        end
      end
    end
  end

  describe "conclude_execution/1" do
    defmodule DummyServer_step_execution do
      use GenServer

      @impl true
      def init(state) do
        {:ok, state}
      end

      @impl true
      def handle_call(event, _from, _state) do
        new_state = {:call, event[:payload]}

        case {event[:stop], event[:reply], event[:timeout]} do
          {nil, nil, nil} -> {:noreply, new_state}
          {nil, nil, timeout} -> {:noreply, new_state, timeout}
          {nil, reply, nil} -> {:reply, reply, new_state}
          {nil, reply, timeout} -> {:reply, reply, new_state, timeout}
          {reason, nil, _} -> {:stop, reason, new_state}
          {reason, reply, _} -> {:stop, reason, reply, new_state}
        end
      end

      @impl true
      def handle_cast(event, _state) do
        new_state = {:cast, event[:payload]}

        case {event[:stop], event[:timeout]} do
          {nil, nil} -> {:noreply, new_state}
          {nil, timeout} -> {:noreply, new_state, timeout}
          {reason, _} -> {:stop, reason, new_state}
        end
      end

      @impl true
      def handle_info(event, _state) do
        new_state = {:info, event[:payload]}

        case {event[:stop], event[:timeout]} do
          {nil, nil} -> {:noreply, new_state}
          {nil, timeout} -> {:noreply, new_state, timeout}
          {reason, _} -> {:stop, reason, new_state}
        end
      end
    end

    alias DummyServer_step_execution, as: DummyServer

    def timeout do
      unshrinkable(one_of([nil, positive_integer(), :infinity, :hibernate]))
    end

    test "dispatches the last event to the right handler" do
      state_before = init_execution(DummyServer, nil, [])

      check all(kind <- one_of([:cast, :info, :call]), payload <- binary()) do
        final_state = conclude_execution({kind, %{payload: payload}}, state_before)
        assert final_state.server_state == {kind, payload}
      end
    end

    test "adjusts the trace and expectations of timeout appropriately" do
      state_before = init_execution(DummyServer, nil, [])

      check all(
              kind <- one_of([:cast, :info, :call]),
              payload <- binary(),
              timeout <- timeout(),
              trace_before = list_of(binary()),
              expected_timeout_before <- boolean()
            ) do
        state_before = %{
          state_before
          | trace_rev: trace_before,
            expects_timeout?: expected_timeout_before
        }

        event = {kind, %{payload: payload, timeout: timeout}}
        final_state = conclude_execution(event, state_before)

        assert final_state.trace_rev == [event | trace_before]

        if timeout in [nil, :infinity, :hibernate] do
          refute final_state.expects_timeout?
        else
          assert final_state.expects_timeout?
        end
      end
    end

    test "raises an exception if the server stops" do
      state_before = init_execution(DummyServer, nil, [])

      check all(
              kind <- one_of([:cast, :info, :call]),
              payload <- binary(),
              reason <- string(:alphanumeric)
            ) do
        event = {kind, %{payload: payload, stop: reason}}

        assert_raise GenServerLTL.ServerStopped, ~r/#{inspect(reason)}/, fn ->
          conclude_execution(event, state_before)
        end
      end
    end

    test "removes properties that are satisfied after stepping" do
      for kind <- [:cast, :info, :call] do
        state_0 =
          init_execution(
            DummyServer,
            0,
            properties do
              property "succeeds at the end", eventually(state == {kind, 2})
            end
          )

        assert match?(
                 prop(eventually &{:expr, _}),
                 find_prop("succeeds at the end", state_0)
               )

        final_state = conclude_execution({kind, %{payload: 2}}, state_0)
        assert final_state.properties == []
      end
    end

    test "raises an exception if a property has been violated" do
      for kind <- [:cast, :info, :call] do
        state_0 =
          init_execution(
            DummyServer,
            0,
            properties do
              invariant "fails at the end", state != {kind, 2}
            end
          )

        assert_raise GenServerLTL.ViolatedProperty, ~r/fails at the end/, fn ->
          conclude_execution({kind, %{payload: 2}}, state_0)
        end
      end
    end

    test "raises an exception if a property has not been fully satisfied" do
      for kind <- [:cast, :info, :call] do
        state_0 =
          init_execution(
            DummyServer,
            0,
            properties do
              property "does not succeed at the end",
                       eventually(state == {kind, 2})
            end
          )

        assert_raise GenServerLTL.ViolatedProperty, ~r/does not succeed at the end/, fn ->
          conclude_execution({kind, %{payload: 1}}, state_0)
        end
      end
    end
  end

  defp find_prop(name, %{properties: properties} = _state) do
    case Enum.find(properties, &match?({^name, _}, &1)) do
      {_, property} -> property
      nil -> nil
    end
  end
end
