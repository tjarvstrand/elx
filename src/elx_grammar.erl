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
%%% it under the terms of the GNU Lesser General Public License as published by
%%% the Free Software Foundation, either version 3 of the License, or
%%% (at your option) any later version.
%%%
%%% ELX is distributed in the hope that it will be useful,
%%% but WITHOUT ANY WARRANTY; without even the implied warranty of
%%% MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
%%% GNU Lesser General Public License for more details.
%%%
%%% You should have received a copy of the GNU Lesser General Public License
%%% along with ELX. If not, see <http://www.gnu.org/licenses/>.
%%% @end
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

%%%_* Module declaration =======================================================
-module(elx_grammar).

%%%_* Exports ==================================================================
-export([action/3,
         new/3,
         productions/1,
         precedence/1,
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

-record(grammar, {rules         :: [rule()],
                  start_symbols :: [non_term_symbol()],
                  precedence    :: [{precedence_lvl(),
                                     associativity(),
                                     [non_term_symbol()]}]}).

%%%_* Types ====================================================================

-opaque grammar()       :: #grammar{}.
-type rule() :: {non_term_symbol(), [symbol()]} |
                {non_term_symbol(), [symbol()], action()} |
                {non_term_symbol(), [symbol()], term_symbol()} |
                {non_term_symbol(), [symbol()], action(), term_symbol()}.

-type production()      :: {non_term_symbol, [symbol()]}.
-type action()          :: fun().

-type symbol()          :: non_term_symbol() | term_symbol().
-type non_term_symbol() :: atom().
-type term_symbol()     :: string().
-type associativity()   :: left | right | nonassoc.
-type precedence()      :: pos_integer().
-type precedence_lvl()  :: {precedence(), associativity()}.


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
  {Rule, Action, _Precedence} = lists:keyfind(Rule, 1, Rules),
  Action(Token).

%%------------------------------------------------------------------------------
%% @doc Return a new grammar() instance.
-spec new(Rules           :: rule(),
          StartSymbols    :: [non_term_symbol()],
          PrecedenceDecls :: [{associativity(), [term_symbol()]}]) -> grammar().
%%------------------------------------------------------------------------------
new(Rules0, [_|_] = StartSymbols, PrecedenceDecls) ->
  validate(Rules0, StartSymbols, PrecedenceDecls),
  TermSymbolPrec = precedence_lvls(PrecedenceDecls),
  Rules          = lists:map(fun new_rule/1,
                             start_rules(StartSymbols) ++ Rules0),
  RulePrec       = rule_precedences(Rules, TermSymbolPrec),
  Grammar = #grammar{rules         = Rules,
                     start_symbols = StartSymbols,
                     precedence    = TermSymbolPrec ++ RulePrec},
  Grammar;
new(_Rules, _StartSymbols, _Precedence) ->
  erlang:error(no_start_state).


%%------------------------------------------------------------------------------
%% @doc
%% Return a list of all non_term_symbol() -> [symbol()] productions of
%% Grammar
-spec productions(Grammar :: grammar()) -> [{non_term_symbol(), [symbol()]}].
%%------------------------------------------------------------------------------
productions(#grammar{rules = Rules}) ->
  lists:map(fun({Production, _, _}) -> Production
            end,
            Rules).

%%------------------------------------------------------------------------------
%% @doc Return the precedence of Rule if defined.
-spec precedence(Grammar :: grammar()) ->
                    [{term_symbol() | production(), precedence_lvl()}].
%%------------------------------------------------------------------------------
precedence(Grammar) -> Grammar#grammar.precedence.

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


precedence_lvls([]) ->
  [];
precedence_lvls(PrecedenceDecls) ->
  % If precedence for a symbol is declared more than once, we will choose the
  % highest declared precedence.
  lists:reverse(
    lists:append(
      lists:zipwith(fun({Assoc, Symbols}, Lvl) ->
                        [{S, {Lvl, Assoc}} || S <- Symbols]
                    end,
                    PrecedenceDecls,
                    lists:seq(1, length(PrecedenceDecls))))).

rule_precedences(Rules, TermSymbolPrecs) ->
  lists:filtermap(fun({Production, _Action, no_precedence}) ->
                      case production_precedence(Production, TermSymbolPrecs) of
                        undefined      -> false;
                        {_Prec, _Assoc} = Lvl -> {true, {Production, Lvl}}
                      end;
                     ({Production, _Action, Term}) ->
                      case term_symbol_precedence(Term, TermSymbolPrecs) of
                        undefined ->
                          erlang:error({invalid_rule_precedence, Term});
                         {_Prec, _Assoc} = Lvl ->
                          {true, {Production, Lvl}}
                      end
                  end,
                  Rules).

production_precedence(Rule, TermSymbolPrecs) ->
  case rule_last_term_symbol(Rule) of
    {ok, Terminal}    -> term_symbol_precedence(Terminal, TermSymbolPrecs);
    {error, notfound} -> undefined
  end.

rule_last_term_symbol({_L, R}) ->
  do_last_terminal_symbol(lists:reverse(R)).

do_last_terminal_symbol([])                    -> {error, notfound};
do_last_terminal_symbol([S|_]) when is_list(S) -> {ok, S};
do_last_terminal_symbol([_|Rest])              -> do_last_terminal_symbol(Rest).

term_symbol_precedence(Terminal, TermSymbolPrecs) ->
  case lists:keyfind(Terminal, 1, TermSymbolPrecs) of
    {Terminal, Lvl} -> Lvl;
    false           -> undefined
  end.

start_rules(Symbols) ->
  [{symbol_to_start_symbol(S), [S, '$']} || S <- Symbols].

new_rule({Left, _Rs}) when Left =:= '.' orelse
                        Left =:= '$' ->
  erlang:error({illegal_non_terminal, Left});
new_rule({Left, Rights}) ->
  new_rule({Left, Rights, fun(Token) -> Token end});
new_rule({Left, Rights, Action}) when is_function(Action) ->
  new_rule({Left, Rights, Action, no_precedence});
new_rule({Left, Rights, Precedence}) when is_list(Precedence) ->
  new_rule({Left, Rights, fun(Token) -> Token end, Precedence});
new_rule({Left, Rights, Action, Precedence}) ->
  {{Left, Rights}, Action, Precedence};
new_rule(Rule) ->
  erlang:error({invalid_rule, Rule}).

validate(Rules, StartSymbols, __PrecedenceDecls) ->
  NonTerminals = ordsets:from_list(lists:map(fun({S, _}) -> S;
                                                ({S, _, _}) -> S;
                                                ({S, _, _, _}) -> S
                                             end, Rules)),
  lists:foreach(fun(S) -> validate_component(NonTerminals, S) end,
                StartSymbols),
  lists:foreach(fun(Rule) -> validate_rule(NonTerminals, Rule) end, Rules).

validate_rule(NonTerminals, {_Left, Components}) ->
  validate_components(NonTerminals, Components);
validate_rule(NonTerminals, {_Left, Components, _Prec}) ->
  validate_components(NonTerminals, Components);
validate_rule(NonTerminals, {_Left, Components, _Prec, _Decls}) ->
  validate_components(NonTerminals, Components).

validate_components(NonTerminals, Components) ->
  lists:foreach(fun(Component) ->
                    validate_component(NonTerminals, Component)
                end,
                Components).

validate_component(NonTerminals, Component) when is_atom(Component) ->
  case lists:member(Component, NonTerminals) of
    true  -> ok;
    false -> erlang:error({illegal_non_terminal, Component})
  end;
validate_component(_NonTerminals, _Rule) ->
  ok.


%%%_* Tests ====================================================================

new_test_() ->
  [?_assertError(no_start_state, new([], [], [])),
   ?_assertError({illegal_non_terminal, '.'}, new([{'.', [["b"]]}], ['.'], [])),
   ?_assertError({invalid_rule_precedence, "z"},
                 new([{'A', ["b", "c"], "z"},
                      {'A', ["d"]}],
                     ['A'],
                     [])),
   ?_assertError({invalid_rule, {'A', ["b", "c"], 'z'}},
                 new([{'A', ["b", "c"], 'z'},
                      {'A', ["d"]}],
                     ['A'],
                     [])),
   ?_assertError({illegal_non_terminal, 'B'},
                 new([{'A', ['B']}],
                     ['A'],
                     [])),
   ?_assertMatch(#grammar{start_symbols = ['A'],
                          precedence = [{"z", {1, right}},
                                        {{'A', ["b", "c"]}, {1, right}}]},
                 new([{'A', ["b", "c"], "z"}],
                     ['A'],
                     [{right, ["z"]}])),
   ?_assertMatch(#grammar{start_symbols = ['A'],
                          precedence = [{"z", {1, right}},
                                        {{'A', ["b", "c"]}, {1, right}}]},
                 new([{'A', ["b", "c"], fake_fun, "z"}],
                     ['A'],
                     [{right, ["z"]}]))
  ].

start_symbols_test_() ->
  [?_assertEqual(['A', 'B'],
                 start_symbols(new([{'A', []},
                                    {'B', []}],
                                   ['A', 'B'], [])))
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
       [?_assertEqual([], precedence(elx_grammar:new([{'A', []}], ['A'], []))),
        ?_assertEqual([{"a", {1, right}}, {{'A', ["a", 'B']}, {1, right}}],
                      precedence(Grammar))
       ]
   end}.


%%%_* Test helpers =============================================================
%%%_* Emacs ====================================================================
%%% Local Variables:
%%% allout-layout: t
%%% erlang-indent-level: 2
%%% End:
