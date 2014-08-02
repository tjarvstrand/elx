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


% TODO:
% - Implement relevant parts of
%    http://www.gnu.org/software/bison/manual/html_node/Action-Features.html
% - Error recovery
% - Mid rule actions


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
  case action(Engine, elx:token_symbol(Token)) of
    {shift, State} -> shift(State, Engine, Tokens);
    {reduce, Rule} -> reduce(Rule, Engine, Tokens);
    {error, Rsn}   -> {error, {Engine, Token, Rsn}}
  end.

action(Engine, Symbol) ->
  elx_dfa:action(dfa(Engine), state(Engine), Symbol).

shift(State, Engine, [Token|Rest]) ->
  {ok, {push_stack(Engine, Token, State), Rest}}.

reduce({NonTerm, Symbols} = Rule, Engine0, Tokens) ->
  {Popped, Engine} = pop_stack(Engine0, length(Symbols)),
  case elx_dfa:goto(dfa(Engine), state(Engine), NonTerm) of
    {ok, NewState} ->
      Token0 = create_parent_token(NonTerm, lists:reverse(Popped)),
      Token = elx_grammar:action(grammar(Engine0), Rule, Token0),
      {ok, {push_stack(Engine, Token, NewState), Tokens}};
    {error, _} ->
      erlang:error({inconsistent_grammar, {reduce, Rule, Engine0}})
  end.

create_parent_token(NonTerm, Children) ->
  Value = parent_token_value(Children),
  Start = parent_token_start(Children),
  End   = parent_token_end(Children),
  elx:token(NonTerm, Value, NonTerm, Start, End, Children).

parent_token_value([])        -> undefined;
parent_token_value([Child|_]) -> elx:token_value(Child).

parent_token_start([]) -> undefined;
parent_token_start([Child|Children]) ->
  case elx:token_start(Child) of
    undefined -> parent_token_start(Children);
    Start     -> Start
  end.

parent_token_end(Children) ->
  do_parent_token_end(lists:reverse(Children)).

do_parent_token_end([]) -> undefined;
do_parent_token_end([Child|Children]) ->
  case elx:token_end(Child) of
    undefined -> do_parent_token_end(Children);
    End       -> End
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
                 run(elx_grammar:new([{'S', ["foo", "bar"]}], ['S'], []),
                     'S',
                     [elx:token(undefined, undefined, "foo")]))
  ].

run_test_() ->
  [% Parse one token
   ?_assertEqual({ok, [elx:token('S',
                                 undefined,
                                 'S',
                                 undefined,
                                 undefined,
                                 [elx:token('E',
                                            undefined,
                                            'E',
                                            undefined,
                                            undefined,
                                            [elx:token(undefined,
                                                       undefined,
                                                       "foo")])])]},
                 run(elx_grammar:new([{'S', ['E']},
                                      {'E', ["foo"]}],
                                     ['S'],
                                     []),
                     'S',
                     [elx:token(undefined,
                                undefined,
                                "foo")])),
   % Parse several tokens.
   ?_assertEqual({ok, [elx:token('S',
                                 undefined,
                                 'S',
                                 undefined,
                                 undefined,
                                 [elx:token('E',
                                            undefined,
                                            'E',
                                            undefined,
                                            undefined,
                                            [elx:token(undefined,
                                                       undefined,
                                                       "foo1")]),
                                  elx:token(undefined,
                                            undefined,
                                            "+"),
                                  elx:token('E',
                                            undefined,
                                            'E',
                                            undefined,
                                            undefined,
                                            [elx:token(undefined,
                                                       undefined,
                                                       "foo2")])])]},
                 run(elx_grammar:new(
                       [{'S', ['E', "+", 'E'], fun(A) -> A end},
                        {'E', ["foo1"]},
                        {'E', ["foo2"]}],
                       ['S'],
                       []),
                     'S',
                     [elx:token(undefined, undefined, "foo1"),
                      elx:token(undefined, undefined, "+"),
                      elx:token(undefined, undefined, "foo2")])),
   % Test that parent start/end is correct when second E is empty,
   ?_assertEqual({ok, [elx:token('S',
                                 undefined,
                                 'S',
                                 elx:point(1,1,1),
                                 elx:point(6,1,6),
                                 [elx:token('E',
                                            undefined,
                                            'E',
                                            elx:point(1,1,1),
                                            elx:point(4,1,4),
                                            [elx:token(undefined,
                                                       undefined,
                                                       "foo",
                                                       elx:point(1,1,1),
                                                       elx:point(4,1,4))]),
                                 elx:token(undefined,
                                           undefined,
                                           "+",
                                            elx:point(5,1,5),
                                            elx:point(6,1,6)),
                                 elx:token('E',
                                           undefined,
                                           'E')])]},
                 run(elx_grammar:new(
                       [{'S', ['E', "+", 'E'], fun(A) -> A end},
                        {'E', ["foo"]},
                        {'E', []}],
                       ['S'],
                       []),
                     'S',
                     [elx:token(undefined,
                                undefined,
                                "foo",
                                elx:point(1,1,1),
                                elx:point(4,1,4)),
                      elx:token(undefined,
                                undefined,
                                "+",
                                elx:point(5,1,5),
                                elx:point(6,1,6))])),
   % Test that parent start/end is correct when first E is empty,
   ?_assertEqual({ok, [elx:token('S',
                                 undefined,
                                 'S',
                                 elx:point(1,1,1),
                                 elx:point(6,1,6),
                                 [elx:token('E',
                                           undefined,
                                           'E'),
                                  elx:token(undefined,
                                            undefined,
                                            "+",
                                            elx:point(1,1,1),
                                            elx:point(2,1,2)),
                                  elx:token('E',
                                            undefined,
                                            'E',
                                            elx:point(3,1,3),
                                            elx:point(6,1,6),
                                            [elx:token(undefined,
                                                       undefined,
                                                       "foo",
                                                       elx:point(3,1,3),
                                                       elx:point(6,1,6))])])]},
                 run(elx_grammar:new(
                       [{'S', ['E', "+", 'E'], fun(A) -> A end},
                        {'E', ["foo"], fun(A) -> A end},
                        {'E', [], fun(A) -> A end}],
                       ['S'],
                       []),
                     'S',
                     [elx:token(undefined,
                                undefined,
                                "+",
                                elx:point(1,1,1),
                                elx:point(2,1,2)),
                      elx:token(undefined,
                                undefined,
                                "foo",
                                elx:point(3,1,3),
                                elx:point(6,1,6))])),
   ?_assertMatch({error, {syntax_error, {_, _, {unexpected_token,  "bar"}}}},
                 run(elx_grammar:new([{'S', ["foo"]}], ['S'], []),
                     'S',
                     [elx:token(undefined, undefined, "foo"),
                      elx:token(undefined, undefined, "bar")])),
   ?_assertError({not_start_symbol, 'A'},
                 run(elx_grammar:new([{'S', [["foo"]]}], ['S'], []), 'A', []))
  ].

inconsistency_test_() ->
  {setup,
   fun() ->
       push_stack(new(elx_grammar:new([{'A', []}], ['A'], [])), undefined, 0)
   end,
   fun(Engine) ->
       [?_assertError({inconsistent_grammar,
                       {reduce, {'B', []}, Engine}},
                      reduce({'B', []}, Engine, []))
       ]
   end
  }.

%%%_* Test helpers =============================================================
%%%_* Emacs ====================================================================
%%% Local Variables:
%%% allout-layout: t
%%% erlang-indent-level: 2
%%% End:
