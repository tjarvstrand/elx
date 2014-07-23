%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%% @doc BNF context-free grammars
%%% @end
%%% @author Thomas Järvstrand <tjarvstrand@gmail.com>
%%% @copyright
%%% Copyright 2012 Thomas Järvstrand <tjarvstrand@gmail.com>
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
-module(elx_grammar).

%%%_* Exports ==================================================================
-export([action/3,
         new/2,
         productions/1,
         start_symbols/1]).

-export_type([grammar/0,
              production/0,
              term_symbol/0,
              non_term_symbol/0,
              symbol/0]).

%%%_* Includes =================================================================
-include_lib("eunit/include/eunit.hrl").

%%%_* Defines ==================================================================

-record(grammar, {rules         :: [rule()],
                  start_symbols :: [non_term_symbol()]}).

-record(rule, {non_term   :: non_term_symbol(),
               components :: [ [symbol()] ],
               action     :: fun()}).

%%%_* Types ====================================================================

-opaque grammar()       :: #grammar{}.
-type rule()            :: #rule{}.
-type production()      :: {non_term_symbol, [symbol()]}.

-type symbol()          :: non_term_symbol() | term_symbol().
-type non_term_symbol() :: atom().
-type term_symbol()     :: string().


%%%_* API ======================================================================


%%------------------------------------------------------------------------------
%% @doc
%% Perform the action corresponding to Symbol according to Grammar. Action is
%% called with Tokens as the only argument and its result is returned.
-spec action(Grammar :: grammar(),
             Symbol :: non_term_symbol(),
             Tokens :: [term()]) -> term().
%%------------------------------------------------------------------------------
action(#grammar{rules = Rules}, Symbol, Tokens) ->
  #rule{action = Action} = lists:keyfind(Symbol, #rule.non_term, Rules),
  Action(Tokens).

%%------------------------------------------------------------------------------
%% @doc Return a new grammar() instance.
-spec new(Rules :: [{non_term_symbol(), [[symbol()]], fun()}],
          StartSymbols :: [non_term_symbol()]) -> grammar().
%%------------------------------------------------------------------------------
new(Rules, [_|_] = StartSymbols) ->
  #grammar{rules         = lists:map(fun new_rule/1, Rules),
           start_symbols = StartSymbols};
new(_, _) ->
  erlang:error(no_start_state).


%%------------------------------------------------------------------------------
%% @doc
%% Return a list of all non_term_symbol() -> [symbol()] productions of
%% Grammar
-spec productions(Grammar :: grammar()) -> [{non_term_symbol(), [symbol()]}].
%%------------------------------------------------------------------------------
productions(#grammar{rules = Rules}) ->
  lists:flatmap(fun rule_to_productions/1, Rules).

%%------------------------------------------------------------------------------
%% @doc Return the start symbols valid for Grammar.
-spec start_symbols(Grammar :: grammar()) -> [non_term_symbol()].
%%------------------------------------------------------------------------------
start_symbols(#grammar{start_symbols = Start}) ->
  Start.

%%%_* Internal functions =======================================================

rule_to_productions(#rule{non_term = Left, components = Rights}) ->
  [{Left, Right} || Right <- Rights].

new_rule({L, _Rs}) when L =:= '.' orelse
                        L =:= '$' ->
  erlang:error({illegal_non_terminal, L});
new_rule({L, Rs}) ->
  new_rule({L, Rs, fun(Tokens) -> hd(Tokens) end});
new_rule({L, Rs, A}) ->
  #rule{non_term = L,
        components = Rs,
        action = A}.

%%%_* Tests ====================================================================

new_test_() ->
  [?_assertError({illegal_non_terminal, '.'}, new([{'.', [["b"]]}], ['.']))
  ].


start_symbols_test_() ->
  [?_assertEqual(['A', 'B'], start_symbols(new([], ['A', 'B']))),
   ?_assertError(no_start_state, start_symbols(new([], [])))
  ].

productions_test_() ->
  {setup,
   fun() ->
       new([{'A', [["b", "c"], ["d"]], fun() -> ok end}], ['A'])
   end,
   fun(Grammar) ->
       [?_assertEqual([{'A', ["b", "c"]}, {'A', ["d"]}], productions(Grammar))]
   end}.

action_test_() ->
  {setup,
   fun() ->
       new([{'A', [], fun([I]) -> "action_"  ++ integer_to_list(I) end},
            {'B', [] }], ['A'])
   end,
   fun(Grammar) ->
       [?_assertEqual("action_1",action(Grammar, 'A', [1])),
        ?_assertEqual("action_2",action(Grammar, 'B', ["action_2"]))]
   end}.

%%%_* Test helpers =============================================================
%%%_* Emacs ====================================================================
%%% Local Variables:
%%% allout-layout: t
%%% erlang-indent-level: 2
%%% End:
