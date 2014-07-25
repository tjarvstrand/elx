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

%%------------------------------------------------------------------------------
%% @doc Generate a DFA based on Grammar and use it to parse the tokens in Input.
-spec run(Grammar      :: elx_grammar:grammar(),
          StartingRule :: elx_grammar:non_term_symbol(),
          Input        :: [elx_lex:token()]) -> [term()].
%%------------------------------------------------------------------------------
run(Grammar, StartSymbol, Input) ->
  case read_tokens(init(new(Grammar), StartSymbol), Input) of
    {ok, Engine} -> {ok, stack_tokens(Engine)};
    {error, Rsn} -> {error, {syntax_error, Rsn}}
  end.

%%%_* Internal functions =======================================================

init(Engine, StartSymbol) ->
  case elx_dfa:start_state(dfa(Engine), StartSymbol) of
    {ok, StateId} -> init_stack(Engine, StateId);
    {error, Rsn}  -> erlang:error(Rsn)
  end.

read_tokens(Engine0, []) ->
  case read_eof(Engine0) of
    {ok, accept}          -> {ok, Engine0};
    {ok, {Engine, ['$']}} -> read_tokens(Engine, []);
    {error, _} = E        -> E
  end;
read_tokens(Engine0, Tokens0) ->
  case read_one_token(Engine0, Tokens0) of
    {ok, {Engine, Tokens}} -> read_tokens(Engine, Tokens);
    {error, _} = E         -> E
  end.

read_eof(Engine) ->
  case action(Engine, '$') of
    accept         -> {ok, accept};
    {reduce, Rule} -> reduce(Rule, Engine, ['$']);
    {error, Rsn}   -> {error, {Engine, '$', Rsn}}
  end.

read_one_token(Engine, [Token|_] = Tokens) ->
  case action(Engine, Token) of
    {shift, State} -> shift(State, Engine, Tokens);
    {reduce, Rule} -> reduce(Rule, Engine, Tokens);
    {error, Rsn}   -> {error, {Engine, Token, Rsn}}
  end.

action(Engine, Token) ->
  elx_dfa:action(dfa(Engine), state(Engine), Token).

shift(State, Engine, [Token|Rest]) ->
  {ok, {push_stack(Engine, Token, State), Rest}}.

reduce({NonTerm, Symbols} = R, Engine0, Tokens) ->
  {Popped, Engine} = pop_stack(Engine0, length(Symbols)),
  case action(Engine, NonTerm) of
    {goto, NewState} ->
      ActionResult = elx_grammar:action(grammar(Engine0), NonTerm, Popped),
      {ok, {push_stack(Engine, ActionResult, NewState), Tokens}};
    {error, _} ->
      erlang:error({inconsistent_grammar, {reduce, R, Engine0}})
  end.

new(Grammar)         -> #engine{grammar = Grammar, dfa = elx_dfa:new(Grammar)}.
dfa(Engine)          -> Engine#engine.dfa.
grammar(Engine)      -> Engine#engine.grammar.
stack(Engine)        -> Engine#engine.stack.
stack_tokens(Engine) -> [T || {T, _} <- stack(Engine), T =/= undefined].
state(Engine)        -> element(2, hd(stack(Engine))).
pop_stack(Engine, N) ->
  {Popped, Stack} = lists:split(N, stack(Engine)),
  {[T || {T, _} <- Popped], set_stack(Engine, Stack)}.

push_stack(Engine, Token, State) ->
  set_stack(Engine, [{Token, State}|stack(Engine)]).

init_stack(Engine, StateId) -> set_stack(Engine, [{undefined, StateId}]).
set_stack(Engine, Stack)    -> Engine#engine{stack = Stack}.

%%%_* Tests ====================================================================

eof_test_() ->
  [?_assertMatch({error, {syntax_error, {_, '$', eof}}},
                 run(elx_grammar:new([{'S', [["foo", "bar"]]}], ['S']),
                     'S',
                     ["foo"]))
  ].

run_test_() ->
  [?_assertEqual({ok, ["foo"]},
                 run(elx_grammar:new([{'S', [['E']]},
                                      {'E', [["foo"]]}],
                                     ['S']),
                     'S',
                     ["foo"])),
   ?_assertEqual({ok, ["foo+foo"]},
                 run(elx_grammar:new(
                       [{'S', [['E', "+", 'E']], fun(A) -> lists:concat(A) end},
                        {'E', [["foo"]]}],
                       ['S']),
                     'S',
                     ["foo", "+", "foo"])),
   ?_assertMatch({error, {syntax_error, {_, "bar", {unexpected_token, "bar"}}}},
                 run(elx_grammar:new([{'S', [["foo"]]}], ['S']),
                     'S',
                     ["foo", "bar"])),
   ?_assertError({not_start_symbol, 'A'},
                 run(elx_grammar:new([{'S', [["foo"]]}], ['S']), 'A', []))
  ].
%%%_* Test helpers =============================================================
%%%_* Emacs ====================================================================
%%% Local Variables:
%%% allout-layout: t
%%% erlang-indent-level: 2
%%% End:
