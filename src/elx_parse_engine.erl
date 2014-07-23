%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%% @doc Parsing of token stream according to dfa's.
%%% @end
%%% @author Thomas Järvstrand <tjarvstrand@gmail.com>
%%% @copyright
%%% Copyright 2014 Thomas Järvstrand <tjarvstrand@gmail.com>
%%%
%%% This file is part of ELX.
%%%
%%% ELX is free software: you can redistribute it and/or modify
%%% it under the terms of the Lesser GNU General Public License as published by
%%% the Free Software Foundation, either version 3 of the License, or
%%% (at your option) any later version.
%%%
%%% ELX is distributed in the hope that it will be useful,
%%% but WITHOUT ANY WARRANTY; without even the implied warranty of
%%% MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
%%% Lesser GNU General Public License for more details.
%%%
%%% You should have received a copy of the Lesser GNU General Public License
%%% along with ELX. If not, see <http://www.gnu.org/licenses/>.
%%% @end
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

%%%_* Module declaration =======================================================
-module(elx_parse_engine).

%%%_* Exports ==================================================================
-export([run/3]).

-export_type([]).

%%%_* Includes =================================================================
-include_lib("eunit/include/eunit.hrl").

%%%_* Defines ==================================================================

-record(engine, {grammar    :: elx_grammar:grammar(),
                 dfa        :: elx_dfa:dfa(),
                 stack = [] :: [{atom(), elx_dfa:state_id()}]}).

%%%_* Types ====================================================================

%%%_* API ======================================================================

run(Grammar, StartSymbol, Input) ->
  read_tokens(init(new(Grammar), StartSymbol), Input).

%%%_* Internal functions =======================================================

init(Engine, StartSymbol) ->
  case elx_dfa:start_state(dfa(Engine), StartSymbol) of
    {ok, StateId} -> init_stack(Engine, StateId);
    {error, Rsn}  -> erlang:error(Rsn)
  end.

read_tokens(Engine, []) ->
  case action(Engine, '$') of
    accept       -> {ok, stack(Engine)};
    {error, Rsn} -> error(Engine, '$', Rsn)
  end;
read_tokens(Engine, [Token|Rest]) ->
  read_tokens(read_token(Engine, Token), Rest).

read_token(Engine0, Token) ->
  case do_read_token(Engine0, Token) of
    {ok, Engine} -> Engine;
    {error, Rsn} -> error(Engine0, Token, Rsn)
  end.

do_read_token(Engine, Token) ->
  case action(Engine, Token) of
    {shift, State} -> shift(State, Token, Engine);
    {reduce, Rule} -> reduce(Rule, Engine, Token);
    {error, _} = E -> E
  end.

error(Engine, Token, Rsn) ->
  {error, {syntax_error, {Rsn,
                          Engine,
                          Token}}}.

action(Engine, Token) ->
  elx_dfa:action(dfa(Engine), state(Engine), Token).

shift(State, Token, Engine) ->
  {ok, push_stack(Engine, Token, State)}.

reduce({NonTerm, Symbols}, Engine0, Token) ->
  {Tokens, Engine} = pop_stack(Engine0, length(Symbols)),
  case action(Engine, Token) of
    {goto, NewState} ->
      ActionResult = elx_grammar:action(grammar(Engine0), NonTerm, Tokens),
      {ok, push_stack(Engine, ActionResult, NewState)};
    {error, _} = E  -> E
  end.

new(Grammar)         -> #engine{grammar = Grammar, dfa = elx_dfa:new(Grammar)}.
dfa(Engine)          -> Engine#engine.dfa.
grammar(Engine)      -> Engine#engine.grammar.
stack(Engine)        -> Engine#engine.stack.
state(Engine)   -> element(2, hd(state(Engine))).
pop_stack(Engine, N) ->
  {Popped, Stack} = lists:split(N, stack(Engine)),
  {[T || {_, T} <- Popped], set_stack(Engine, Stack)}.

push_stack(Engine, Token, State) ->
  set_stack(Engine, [{Token, State}|stack(Engine)]).

init_stack(Engine, StateId) -> set_stack(Engine, [{undefined, StateId}]).
set_stack(Engine, Stack)    -> Engine#engine{stack = Stack}.

%%%_* Tests ====================================================================

%%%_* Test helpers =============================================================
%%%_* Emacs ====================================================================
%%% Local Variables:
%%% allout-layout: t
%%% erlang-indent-level: 2
%%% End:
