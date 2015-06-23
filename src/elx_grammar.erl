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
         new/4,
         productions/1,
         precedence/1,
         start_symbols/1,
         symbol_to_start_symbol/1,
         term_symbols/1]).

-export_type([grammar/0,
              rule/0,
              production/0,
              action/0,

              associativity/0,
              precedence_lvl/0]).

%%%_* Includes =================================================================
-include_lib("eunit/include/eunit.hrl").

-include("elx.hrl").

%%%_* Defines ==================================================================

-record(grammar, {rules         :: [elx:rule()],
                  start_symbols :: [elx:symbol()],
                  term_symbols  :: [elx:symbol()],
                  precedence    :: [{precedence_lvl(),
                                     associativity(),
                                     [elx:symbol()]}]}).

%%%_* Types ====================================================================

-opaque grammar()       :: #grammar{}.
-type rule()            :: {elx:symbol(), [rule_component()]} |
                           {elx:symbol(), [rule_component()], action()} |
                           {elx:symbol(), [rule_component()], elx:symbol()} |
                           {elx:symbol(),
                            [rule_component()],
                            action(),
                            elx:symbol()}.

-type rule_component()  :: elx:symbol() | ?point | ?eof.

-type production()      :: {elx:non_term_symbol(), [elx:symbol()]}.
-type action()          :: fun().

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
          Terminals       :: [elx:symbol()],
          StartSymbols    :: [elx:symbol()],
          PrecedenceDecls :: [{associativity(), [elx:symbol()]}]) -> grammar().
%%------------------------------------------------------------------------------
new(Rules0, Terminals, StartSymbols, PrecedenceDecls) ->
  validate(Rules0, Terminals, StartSymbols, PrecedenceDecls),
  TermSymbolPrec = precedence_lvls(PrecedenceDecls),
  Rules          = lists:map(fun new_rule/1,
                             start_rules(StartSymbols) ++ Rules0),
  RulePrec       = rule_precedences(Rules, Terminals, TermSymbolPrec),
  Grammar = #grammar{rules         = Rules,
                     term_symbols  = Terminals,
                     start_symbols = StartSymbols,
                     precedence    = TermSymbolPrec ++ RulePrec},
  Grammar.


%%------------------------------------------------------------------------------
%% @doc
%% Return a list of all symbol() -> [symbol()] productions of
%% Grammar
-spec productions(Grammar :: grammar()) -> [production()].
%%------------------------------------------------------------------------------
productions(#grammar{rules = Rules}) ->
  lists:map(fun({Production, _, _}) -> Production
            end,
            Rules).

%%------------------------------------------------------------------------------
%% @doc Return the precedence of Rule if defined.
-spec precedence(Grammar :: grammar()) ->
                    [{elx:symbol() | production(), precedence_lvl()}].
%%------------------------------------------------------------------------------
precedence(Grammar) -> Grammar#grammar.precedence.

%%------------------------------------------------------------------------------
%% @doc Return Symbol converted to a valid start symbol Grammar.
-spec symbol_to_start_symbol(elx:symbol()) -> elx:symbol().
%%------------------------------------------------------------------------------
symbol_to_start_symbol(Symbol) ->
  list_to_atom(atom_to_list(Symbol) ++ "'").

%%------------------------------------------------------------------------------
%% @doc Return the start symbols valid for Grammar.
-spec start_symbols(Grammar :: grammar()) -> [elx:symbol()].
%%------------------------------------------------------------------------------
start_symbols(#grammar{start_symbols = Start}) ->
  Start.

%%------------------------------------------------------------------------------
%% @doc Return the term symbols valid for Grammar.
-spec term_symbols(Grammar :: grammar()) -> [elx:symbol()].
%%------------------------------------------------------------------------------
term_symbols(#grammar{term_symbols = TermSymbols}) ->
  TermSymbols.

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

rule_precedences(Rules, TermSymbols, TermSymbolPrecs) ->
  lists:filtermap(
    fun({Production, _Action, default_precedence}) ->
        case production_precedence(Production, TermSymbols, TermSymbolPrecs) of
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

production_precedence(Rule, _TermSymbols, TermSymbolPrecs) ->
  case rule_last_term_symbol(Rule, _TermSymbols, TermSymbolPrecs) of
    {ok, Terminal}    -> term_symbol_precedence(Terminal, TermSymbolPrecs);
    {error, notfound} -> undefined
  end.

rule_last_term_symbol({_L, R}, TermSymbols, TermSymbolPrecs) ->
  do_last_terminal_symbol(lists:reverse(R), TermSymbols, TermSymbolPrecs).

do_last_terminal_symbol([],      _TermSymbols, _TermSymbolPrecs) ->
  {error, notfound};
do_last_terminal_symbol([S|Rest], TermSymbols,  TermSymbolPrecs) ->
  case lists:member(S, TermSymbols) of
    true  -> {ok, S};
    false -> do_last_terminal_symbol(Rest, TermSymbols, TermSymbolPrecs)
  end.

term_symbol_precedence(Terminal, TermSymbolPrecs) ->
  case lists:keyfind(Terminal, 1, TermSymbolPrecs) of
    {Terminal, Lvl} -> Lvl;
    false           -> undefined
  end.

start_rules(Symbols) ->
  [{symbol_to_start_symbol(S), [S, ?eof]} || S <- Symbols].

new_rule({Left, _Rs}) when Left =:= ?point orelse
                        Left =:= ?eof ->
  erlang:error({illegal_symbol, Left});
new_rule({Left, Rights}) ->
  new_rule({Left, Rights, fun(Token) -> Token end});
new_rule({Left, Rights, Action}) when is_function(Action) ->
  new_rule({Left, Rights, Action, default_precedence});
new_rule({Left, Rights, Precedence}) ->
  new_rule({Left, Rights, fun(Token) -> Token end, Precedence});
new_rule({Left, Rights, Action, Precedence}) ->
  {{Left, Rights}, Action, Precedence}.


validate(_Rules, [],         _StartSymbols, _Precedence) ->
  erlang:error(no_terminal_declarations);
validate(_Rules, _Terminals, [], _Precedence) ->
  erlang:error(no_start_state);
validate(Rules, Terminals, StartSymbols, _PrecedenceDecls) ->
  NonTerminals =
    ordsets:from_list(lists:map(fun({S, _})       -> S;
                                   ({S, _, _})    -> S;
                                   ({S, _, _, _}) -> S;
                                   (Rule)         ->
                                    erlang:error({invalid_rule, Rule})
                                end,
                                Rules)),
  lists:foreach(fun(S) -> validate_symbol(Terminals, NonTerminals, S) end,
                StartSymbols),
  lists:foreach(fun(R) -> validate_rule(Terminals, NonTerminals, R) end,
                Rules).

validate_rule(Terminals, NonTerminals, {_Left, Symbols}) ->
  validate_symbols(Terminals, NonTerminals, Symbols);
validate_rule(Terminals, NonTerminals, {_Left, Symbols, _Prec}) ->
  validate_symbols(Terminals, NonTerminals, Symbols);
validate_rule(Terminals, NonTerminals, {_Left, Symbols, _Prec, _Decls}) ->
  validate_symbols(Terminals, NonTerminals, Symbols).

validate_symbols(Terminals, NonTerminals, Symbols) ->
  lists:foreach(fun(Symbol) ->
                    validate_symbol(Terminals, NonTerminals, Symbol)
                end,
                Symbols).

validate_symbol(_Terminals, _NonTerminals, Symbol) when Symbol =:= ?eof orelse
                                                        Symbol =:= ?point ->
  erlang:error({illegal_symbol, Symbol});
validate_symbol(Terminals, NonTerminals, Symbol) when is_atom(Symbol) ->
  case lists:member(Symbol, Terminals ++ NonTerminals) of
    true  -> ok;
    false -> erlang:error({illegal_symbol, Symbol})
  end;
validate_symbol(_Terminals, _NonTerminals, Symbol) ->
  erlang:error({illegal_symbol, Symbol}).



%%%_* Tests ====================================================================

new_test_() ->
  [?_assertError(no_terminal_declarations, new([], [], [], [])),
   ?_assertError(no_start_state, new([], ['a'], [], [])),
   ?_assertError({illegal_symbol, ?eof},
                 new([{?eof, [['b']]}], ['b'], [?eof], [])),
   ?_assertError({illegal_symbol, ?eof},
                 new([{?eof, ['b']},
                      {'S',  ['a']}], ['a', 'b'], ['S'], [])),
   ?_assertError({illegal_symbol, {'.'}},
                 new([{".", [['b']]}], ['b'], [{'.'}], [])),
   ?_assertError({illegal_symbol, "."},
                 new([{".", [['b']]}], ['b'], ["."], [])),
   ?_assertError({invalid_rule_precedence, 'z'},
                 new([{'A', ['b', 'c'], 'z'},
                      {'A', ['d']}],
                     ['b', 'c', 'd', 'z'],
                     ['A'],
                     [])),
   ?_assertError({invalid_rule, {'A'}},
                 new([{'A'}],
                     ['a'],
                     ['A'],
                     [])),
   ?_assertError({illegal_symbol, 'B'},
                 new([{'A', ['B']}],
                     ['a'],
                     ['A'],
                     [])),
   ?_assertMatch(#grammar{start_symbols = ['A'],
                          precedence = [{'z', {1, right}},
                                        {{'A', ['b', 'c']}, {1, right}}]},
                 new([{'A', ['b', 'c'], 'z'}],
                     ['b', 'c', 'd'],
                     ['A'],
                     [{right, ['z']}])),
   ?_assertMatch(#grammar{start_symbols = ['A'],
                          precedence = [{'z', {1, right}},
                                        {{'A', ['b', 'c']}, {1, right}}]},
                 new([{'A', ['b', 'c'], fake_fun, 'z'}],
                     ['b', 'c', 'z'],
                     ['A'],
                     [{right, ['z']}]))
  ].

start_symbols_test_() ->
  [?_assertEqual(['A', 'B'],
                 start_symbols(new([{'A', []},
                                    {'B', []}],
                                   ['a'],
                                   ['A', 'B'], [])))
  ].

productions_test_() ->
  {setup,
   fun() ->
       new([{'A', ['b', 'c']},
            {'A', ['d']}],
           ['b', 'c', 'd'],
           ['A'],
          [])
   end,
   fun(Grammar) ->
       [?_assertEqual([{'A\'', ['A', ?eof]},
                       {'A', ['b', 'c']},
                       {'A', ['d']}],
                      productions(Grammar))]
   end}.

action_test_() ->
  {setup,
   fun() ->
       new([{'A', [], fun(Token) ->
                          elx:set_token_value(Token, "action_1")
                      end},
            {'B', []}],
           ['a'],
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
            {'A', ['a', 'B']},
            {'A', ['c', 'B']},
            {'B', []}],
           ['a', 'c'],
           ['A'],
          [{right, ['a']}])
   end,
   fun(Grammar) ->
       [
        ?_assertEqual([], precedence(new([{'A', []}], ['a'], ['A'], []))),
        ?_assertEqual([{'a', {1, right}}, {{'A', ['a', 'B']}, {1, right}}],
                      precedence(Grammar))
       ]
   end}.


%%%_* Test helpers =============================================================
%%%_* Emacs ====================================================================
%%% Local Variables:
%%% allout-layout: t
%%% erlang-indent-level: 2
%%% End:
