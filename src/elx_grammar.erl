%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%% @doc BNF context-free grammars
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
-module(elx_grammar).

%%%_* Exports ==================================================================
-export([action/3,
         new/3,
         precedence_lvl_associativity/2,
         productions/1,
         rule_precedence/2,
         start_symbols/1,
         symbol_to_start_symbol/1]).

-export_type([grammar/0,
              rule/0,
              production/0,
              symbol/0,
              term_symbol/0,
              non_term_symbol/0,
              action/0,

              associativity/0,
              precedence_lvl/0]).

%%%_* Includes =================================================================
-include_lib("eunit/include/eunit.hrl").

%%%_* Defines ==================================================================

-record(grammar, {rules           :: [rule()],
                  start_symbols   :: [non_term_symbol()],
                  precedence_lvls :: [{precedence_lvl(),
                                     associativity(),
                                     [non_term_symbol()]}]}).

%%%_* Types ====================================================================

-opaque grammar()       :: #grammar{}.
-type rule()            :: {production(), action()}.
-type production()      :: {non_term_symbol, [symbol()]}.
-type action()          :: fun().

-type symbol()          :: non_term_symbol() | term_symbol().
-type non_term_symbol() :: atom().
-type term_symbol()     :: string().
-type associativity()   :: left | right | nonassoc.
-type precedence_lvl()  :: pos_integer().


%%%_* API ======================================================================


%%------------------------------------------------------------------------------
%% @doc
%% Perform the action corresponding to Symbol according to Grammar. Action is
%% called with Tokens as the only argument and its result is returned.
-spec action(Grammar :: grammar(),
             Rule    :: rule(),
             Token   :: elx:token()) -> term().
%%------------------------------------------------------------------------------
action(#grammar{rules = Rules}, Rule, Token) ->
  {Rule, Action} = lists:keyfind(Rule, 1, Rules),
  Action(Token).

%%------------------------------------------------------------------------------
%% @doc Return a new grammar() instance.
-spec new(Rules        :: rule(),
          OpPrecedence :: [{associativity(), [symbol()]}],
          StartSymbols :: [non_term_symbol()]) -> grammar().
%%------------------------------------------------------------------------------
new(Rules, [_|_] = StartSymbols, PrecedenceDecls) ->
  #grammar{rules           = lists:map(fun new_rule/1,
                                       start_rules(StartSymbols) ++ Rules),
           start_symbols   = StartSymbols,
           precedence_lvls = precedence(PrecedenceDecls)};
new(_Rules, _StartSymbols, _Precedence) ->
  erlang:error(no_start_state).


%%------------------------------------------------------------------------------
%% @doc
%% Return a list of all non_term_symbol() -> [symbol()] productions of
%% Grammar
-spec productions(Grammar :: grammar()) -> [{non_term_symbol(), [symbol()]}].
%%------------------------------------------------------------------------------
productions(#grammar{rules = Rules}) ->
  [Production || {Production, _Action} <- Rules].

%%------------------------------------------------------------------------------
%% @doc Return the precedence of Rule if defined.
-spec rule_precedence(Grammar :: grammar(),
                      Rule    :: production()) -> precedence_lvl() | undefined.
%%------------------------------------------------------------------------------
rule_precedence(Grammar, Rule) ->
  case rule_last_term_symbol(Rule) of
    {ok, Terminal}    -> term_symbol_precedence(Grammar, Terminal);
    {error, notfound} -> undefined
  end.

%%------------------------------------------------------------------------------
%% @doc Return the precedence of Terminal if defined.
-spec term_symbol_precedence(Grammar  :: grammar(),
                             Terminal :: term_symbol()) ->
                             precedence_lvl() | undefined.
%%------------------------------------------------------------------------------
term_symbol_precedence(#grammar{precedence_lvls = PrecLvls}, Terminal) ->
  do_term_symbol_precedence(PrecLvls, Terminal).

%%------------------------------------------------------------------------------
%% @doc Return the associativity of PrecLvl
-spec precedence_lvl_associativity(Grammar :: grammar(),
                                   PrecLvl :: precedence_lvl()) ->
                                      {ok, associativity()} | {error, notfound}.
%%------------------------------------------------------------------------------
precedence_lvl_associativity(#grammar{precedence_lvls = PrecLvls}, PrecLvl) ->
  case lists:keyfind(PrecLvl, 1, PrecLvls) of
    {PrecLvl, Assoc, _Symbols} -> Assoc;
    false                      -> {error, notfound}
  end.


%%------------------------------------------------------------------------------
%% @doc Return Symbol converted to a valid start symbol Grammar.
-spec symbol_to_start_symbol(non_term_symbol()) -> non_term_symbol().
%%------------------------------------------------------------------------------
symbol_to_start_symbol(Symbol) ->
  list_to_atom(atom_to_list(Symbol) ++ "'").

%%------------------------------------------------------------------------------
%% @doc Return the start symbols valid for Grammar.
-spec start_symbols(Grammar :: grammar()) -> [non_term_symbol()].
%%------------------------------------------------------------------------------
start_symbols(#grammar{start_symbols = Start}) ->
  Start.

%%%_* Internal functions =======================================================

rule_last_term_symbol({_L, R}) ->
  do_last_terminal_symbol(lists:reverse(R)).

do_last_terminal_symbol([])                    -> {error, notfound};
do_last_terminal_symbol([S|_]) when is_list(S) -> {ok, S};
do_last_terminal_symbol([_|Rest])              -> do_last_terminal_symbol(Rest).

do_term_symbol_precedence([], _Terminal) ->
  undefined;
do_term_symbol_precedence([{Prec, _Assoc, Symbols}|Lvls], Terminal) ->
  case lists:member(Terminal, Symbols) of
    true  -> Prec;
    false -> do_term_symbol_precedence(Lvls, Terminal)
  end.

precedence(PrecedenceDecls) ->
  % If precedence for a symbol is declared more than once, we will choose the
  % highest declared precedence.
  lists:reverse(
    lists:zipwith(fun({Assoc, Symbols}, Prec) -> {Prec, Assoc, Symbols} end,
                  PrecedenceDecls,
                  lists:seq(1, length(PrecedenceDecls)))).


start_rules(Symbols) ->
  [{symbol_to_start_symbol(S), [S, '$']} || S <- Symbols].

new_rule({L, _Rs}) when L =:= '.' orelse
                        L =:= '$' ->
  erlang:error({illegal_non_terminal, L});
new_rule({L, Rs}) ->
  new_rule({L, Rs, fun(Token) -> Token end});
new_rule({L, Rs, A}) ->
  {{L, Rs}, A}.

%%%_* Tests ====================================================================

new_test_() ->
  [?_assertError({illegal_non_terminal, '.'}, new([{'.', [["b"]]}], ['.'], []))
  ].


start_symbols_test_() ->
  [?_assertEqual(['A', 'B'], start_symbols(new([], ['A', 'B'], []))),
   ?_assertError(no_start_state, start_symbols(new([], [], [])))
  ].

productions_test_() ->
  {setup,
   fun() ->
       new([{'A', ["b", "c"]},
            {'A', ["d"]}],
           ['A'],
          [])
   end,
   fun(Grammar) ->
       [?_assertEqual([{'A\'', ['A', '$']},
                       {'A', ["b", "c"]},
                       {'A', ["d"]}],
                      productions(Grammar))]
   end}.

action_test_() ->
  {setup,
   fun() ->
       new([{'A', [], fun(Token) ->
                          elx:set_token_value(Token, "action_1")
                      end},
            {'B', []}],
           ['A'],
          [])
   end,
   fun(Grammar) ->
       [?_assertEqual(elx:token(undefined,
                                "action_1",
                               []),
                      action(Grammar,
                             {'A', []},
                             elx:token())),
       ?_assertEqual(elx:token(undefined,
                               undefined,
                               []),
                      action(Grammar,
                             {'B', []},
                             elx:token()))
       ]
   end}.

precedences_test_() ->
  {setup,
   fun() ->
       new([{'A', []},
            {'A', ["a", 'B']},
            {'A', ["c", 'B']},
            {'B', []}],
           ['A'],
          [{right, ["a"]}])
   end,
   fun(Grammar) ->
       [?_assertEqual(undefined, rule_precedence(Grammar, {'B', []})),
        ?_assertEqual(1, rule_precedence(Grammar, {'A', ["a", 'B']})),
        ?_assertEqual(undefined, rule_precedence(Grammar, {'A', ["c", 'B']})),
        ?_assertEqual(right, precedence_lvl_associativity(Grammar, 1)),
        ?_assertEqual({error, notfound},
                      precedence_lvl_associativity(Grammar, 2))
       ]
   end}.


%%%_* Test helpers =============================================================
%%%_* Emacs ====================================================================
%%% Local Variables:
%%% allout-layout: t
%%% erlang-indent-level: 2
%%% End:
