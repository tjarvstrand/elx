%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%% @doc Context free grammars.
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
-export([dfa_init/2]).

-export_type([grammar/0]).

%%%_* Includes =================================================================
-include_lib("eunit/include/eunit.hrl").

%%%_* Defines ==================================================================

-record(grammar, {productions = [] :: non_terminal()
                 }).

-record(non_term, {nullable = false,
                   first = ordsets:new(),
                   follow = ordsets:new()}).

-record(dfa, {start = [],
              state,
              states = []}).


-record(state, {id,
                items = [],
                items_hash,
                edges = orddict:new()}).

%%%_* Types ====================================================================

-opaque grammar() :: #grammar{}.
-type non_terminal() :: #non_term{}.

%%%_* API ======================================================================

%%%_* Internal functions =======================================================

dfa_init(#dfa{start = Start} = DFA, StartSymbol) ->
  case lists:keyfind(StartSymbol, 1, Start) of
    {StartSymbol, StartStateId} -> {ok, DFA#dfa{state = StartStateId}};
    {error, notfound}           -> {error, {not_start_symbol, StartSymbol}}
  end.

dfa(Productions, StartSymbols) ->
  NonTerms = first(Productions),
  {Start, StartStates} = init_start_states(Productions, NonTerms, StartSymbols),
  #dfa{start = Start, states = dfa_table(Productions, NonTerms, StartStates)}.

init_start_states(Productions, NonTerms, StartSymbols) ->
  SymbolIdMap = lists:zip(StartSymbols, lists:seq(0, length(StartSymbols) - 1)),
  States = lists:map(fun({Start, Id}) ->
                         init_start_state(Productions, NonTerms, Start, Id)
                     end,
                     SymbolIdMap),
  {SymbolIdMap, States}.

init_start_state(Productions, NonTerms, Start, Id) ->
  AuxStart = {list_to_atom(atom_to_list(Start) ++ "'"), [Start, '$']},
  Items = closure(Productions, NonTerms, [item_init(AuxStart, [])]),
  #state{id = Id, items = Items, items_hash = items_hash(Items)}.

dfa_table(Grammar, NonTerms, States0) ->
  States = do_graph(Grammar, NonTerms, States0),
  case length(States) =:= length(States0) of
    true   -> States0;
    false  -> dfa_table(Grammar, NonTerms, States)
  end.

do_graph(Grammar, NonTerms, States0) ->
  lists:foldl(fun(State, States) ->
                  graph_state(Grammar, NonTerms, State, States)
              end,
              States0,
              States0).

graph_state(Grammar, NonTerms, #state{id = Id, items = Items}, States0) ->
  lists:foldl(fun(Item, States) ->
                  add_item_state(Grammar, NonTerms, Item, Id, States) end,
               States0,
               Items).

add_item_state(Grammar, NonTerms, Item, ItemStateId, States0) ->
  case item_next(Item) of
    '$'            -> States0;
    {error, empty} -> States0;
    Next           ->
      From = lists:keyfind(ItemStateId, #state.id, States0),
      {ToId, States} = go_to(Grammar, NonTerms, From, States0, Next),
      lists:keystore(ItemStateId, #state.id, States, add_edge(From, Next, ToId))
  end.

add_edge(#state{edges = Edges} = From, NextToken, ToId) ->
  Update = fun(TokenEdges) -> ordsets:add_element(ToId, TokenEdges) end,
  From#state{edges = orddict:update(NextToken, Update, [ToId], Edges)}.

next_state_id(States) ->
  lists:max([Id || #state{id = Id} <- States]) + 1.

go_to(Grammar, NonTerms, From, States0, Token) ->
  To0 = do_go_to(Grammar, NonTerms, From, Token, ordsets:new()),
  case lists:keytake(To0#state.items_hash, #state.items_hash, States0) of
    false    ->
      Id = next_state_id(States0),
      {Id, lists:sort([To0#state{id = Id}|States0])};
    {value, #state{id = Id} = To, States} ->
      {Id, lists:sort([merge_state_items(To, To0)|States])}
  end.

merge_state_items(#state{items = Items1} = State1, #state{items = Items2}) ->
  State1#state{items = ordsets:union(Items1, Items2)}.

do_go_to(Grammar, NonTerms, #state{items = []}, _Token, Acc) ->
  Items = closure(Grammar, NonTerms, Acc),
  #state{items = Items, items_hash = items_hash(Items)};
do_go_to(Grammar, NonTerms, #state{items = [Item|Rst]} = State,  Token, Acc0) ->
  Acc = case item_next(Item) of
          Token -> ordsets:add_element(item_advance(Item), Acc0);
          _     -> Acc0
        end,
  do_go_to(Grammar, NonTerms, State#state{items = Rst}, Token, Acc).

items_hash(Items) ->
  erlang:phash2(ordsets:from_list([{L, R} || {L, R, _LA} <- Items])).

item_advance({L, R, Lookahead}) ->
  {L, item_advance_r(R, []), Lookahead}.

item_advance_r(['.',Next|Rest], Acc) ->
  lists:reverse(Acc) ++ [Next, '.'] ++ Rest;
item_advance_r([Next|Rest], Acc) ->
  item_advance_r(Rest, [Next|Acc]).

item_next(Item) ->
  case item_partition_next(Item) of
    {error, _} = E  -> E;
    {Next, _Rest}   -> Next
  end.

item_partition_next({_L, R, _LookAhead}) ->
  case lists:splitwith(fun(T) -> T =/= '.' end, R) of
    {_, ['.']} -> {error, empty};
    {_, ['.', Next|Rest]} -> {Next, Rest}
  end.

closure(Grammar, NonTerms, Items0) ->
  case do_closure(Grammar, NonTerms, Items0) of
    Items0 -> Items0;
    Items  -> closure(Grammar, NonTerms, Items)
  end.

do_closure(Grammar, NonTerms, Items) ->
  ordsets:fold(fun(I, Acc) ->
                   Closure = item_closure(Grammar, NonTerms, I),
                   ordsets:union(Acc, Closure)
               end,
               Items,
               Items).

item_closure(Grammar, NonTerms, Item) ->
  case item_partition_next(Item) of
    {error, empty} ->
      ordsets:new();
    {Next, Rest} ->
      Lookaheads = item_lookaheads(NonTerms, Rest, Item),
      F = fun({ProdL, _ProdR} = Prod, Acc) when ProdL =:= Next ->
             [item_init(Prod, LA) || LA <- Lookaheads] ++ Acc;
             (_Prod, Acc) ->
              Acc
          end,
      ordsets:from_list(lists:foldl(F, [], Grammar))
  end.

item_lookaheads(NonTerms0, Rest, {_ItemL, _ItemR, ItemLookahead}) ->
  Firsts = production_first(orddict:store('.', #non_term{}, NonTerms0),
                            {'.', Rest ++ [ItemLookahead]}),
  (orddict:fetch('.', Firsts))#non_term.first.

item_init({L, R}, Lookahead) ->
  {L, ['.'|R], Lookahead}.

first(Productions) ->
  first(grammar_non_terms(Productions), Productions).

first(NonTerms0, Productions) ->
  case do_first_follow(NonTerms0, Productions) of
    NonTerms0 -> NonTerms0;
    NonTerms  -> first(NonTerms, Productions)
  end.

do_first_follow(NonTerms, Productions) ->
  lists:foldl(fun(P, NonTerms1) ->
                  production_first(NonTerms1, P)
                end,
                NonTerms,
                Productions).


production_first(NonTerms, Production) ->
  update_prod_first(update_prod_nullable(NonTerms, Production), Production).

grammar_non_terms(Grammar) ->
  orddict:from_list([{L, #non_term{}} || {L, _R} <- Grammar]).

update_prod_nullable(NonTerms, {ProdL, ProdR}) ->
  Update = fun(#non_term{nullable = true} = NT) -> NT;
              (NT) -> NT#non_term{nullable = prod_nullable_p(NonTerms, ProdR)}
           end,
  orddict:update(ProdL, Update, NonTerms).

prod_nullable_p(NonTerms, ProdR) ->
  lists:all(fun(TermSymbol)    when is_list(TermSymbol)    -> false;
               ('$')                                       -> false;
               (NonTermSymbol) when is_atom(NonTermSymbol) ->
                (orddict:fetch(NonTermSymbol, NonTerms))#non_term.nullable
            end,
            ProdR).

update_prod_first(NonTerms, {ProdL, ProdR}) ->
  Update = fun(#non_term{first = First} = NT) ->
               NT#non_term{first = prod_first(NonTerms, ProdR, First)}
           end,
  orddict:update(ProdL, Update, NonTerms).

prod_first(_NonTerms, [],             Acc) -> Acc;
prod_first(_NonTerms,['$'|_Rest], Acc) ->
  ordsets:add_element('$', Acc);
prod_first(_NonTerms,[Symbol|_Rest], Acc) when is_list(Symbol) ->
  ordsets:add_element(Symbol, Acc);
prod_first(NonTerms, [Symbol|Rest], Acc0) ->
  NonTerm = orddict:fetch(Symbol, NonTerms),
  Acc = ordsets:union(Acc0, NonTerm#non_term.first),
  case NonTerm#non_term.nullable  of
    true  -> prod_first(NonTerms, Rest, Acc);
    false -> Acc
  end.

%%%_* Tests ====================================================================

first_test_() ->
  [?_assertEqual(
      [{'B', #non_term{nullable = false, first = ["w"]}},
       {'D', #non_term{nullable = true,  first = ["x", "y"]}},
       {'E', #non_term{nullable = true,  first = ["y"]}},
       {'F', #non_term{nullable = true,  first = ["x"]}},
       {'S', #non_term{nullable = false, first = ["u"]}}],
      first([{'S', ["u", 'B', 'D', "z"]},
             {'B', ['B', "v"]},           {'B', ["w"]},
             {'D', ['E', 'F']},
             {'E', ["y"]},                {'E', []},
             {'F', ["x"]},                {'F', []}])),
   ?_assertEqual(
      [{'E', #non_term{nullable = false, first = ["(", "-", "x"]}},
       {'L', #non_term{nullable = true,  first = ["("]}},
       {'M', #non_term{nullable = true,  first = ["-"]}},
       {'S', #non_term{nullable = false, first = ["(", "-", "x"]}},
       {'V', #non_term{nullable = false, first = ["x"]}}],
      first([{'S', ['E', '$']},
             {'E', ["-", 'E']}, {'E', ["(", 'E', ")"]}, {'E', ['V', 'M']},
             {'M', ["-", 'E']}, {'M', []},
             {'V', ["x", 'L']},
             {'L', ["(", 'E', ")"]}, {'L', []}]))].

update_prod_nullable_test_() ->
  {setup,
   fun() ->
       Grammar = [{'A', ["b"]},
                  {'B', []},
                  {'C', ['A']},
                  {'D', ['B']}],
       NonTerms = grammar_non_terms(Grammar),
       {Grammar, NonTerms}
   end,
   fun({Grammar, NonTerms}) ->
       [?_assertEqual(#non_term{nullable = false},
                      orddict:fetch(
                        'A',
                        update_prod_nullable(NonTerms, lists:nth(1, Grammar)))),
        ?_assertEqual(#non_term{nullable = true},
                      orddict:fetch(
                        'B',
                        update_prod_nullable(NonTerms, lists:nth(2, Grammar)))),
        ?_assertEqual(#non_term{nullable = false},
                      orddict:fetch(
                        'C',
                        update_prod_nullable(NonTerms, lists:nth(3, Grammar)))),
        ?_assertEqual(#non_term{nullable = true},
                      orddict:fetch(
                        'D',
                        update_prod_nullable(
                          orddict:store('B',
                                        #non_term{nullable = true},
                                        NonTerms),
                          lists:nth(4, Grammar))))
       ]
   end}.

update_prod_first_test_() ->
  {setup,
   fun() ->
       Grammar = [{'A', ["b"]},
                  {'B', []},
                  {'C', ['A']},
                  {'D', ['B', "a"]}],
       NonTerms = grammar_non_terms(Grammar),
       {Grammar, NonTerms}
   end,
   fun({Grammar, NonTerms}) ->
       [?_assertEqual(#non_term{first = ["b"]},
                      orddict:fetch(
                        'A',
                        update_prod_first(NonTerms, lists:nth(1, Grammar)))),
        ?_assertEqual(#non_term{first = []},
                      orddict:fetch(
                        'B',
                        update_prod_first(NonTerms, lists:nth(2, Grammar)))),
        ?_assertEqual(#non_term{first = ["b"]},
                      orddict:fetch(
                        'C',
                        update_prod_first(
                          orddict:store('A',
                                        #non_term{first = ["b"]},
                                        NonTerms),
                          lists:nth(3, Grammar)))),
        ?_assertEqual(#non_term{first = ["a"]},
                      orddict:fetch(
                        'D',
                        update_prod_first(
                          orddict:store('B',
                                        #non_term{nullable = true},
                                        NonTerms),
                          lists:nth(4, Grammar))))
       ]
   end}.

dfa_table_2_test_() ->
  {setup,
   fun() ->
       dfa([{'S',   ['V', "=", 'E']}, {'S',   ['E']},
            {'E',   ['V']},
            {'V',   ["x"]}, {'V', ["*", 'E']}],
           ['S'])
   end,
   fun(#dfa{states = Table}) ->
       [?_assertEqual(10, length(Table)),
        ?_assertMatch(#state{id = 0,
                             items = [{'E',['.','V'],'$'},
                                      {'S',['.','E'],'$'},
                                      {'S',['.','V',"=",'E'],'$'},
                                      {'S\'',['.','S','$'],[]},
                                      {'V',['.',"*",'E'],'$'},
                                      {'V',['.',"*",'E'],"="},
                                      {'V',['.',"x"],'$'},
                                      {'V',['.',"x"],"="}],
                             items_hash = Hash,
                             edges = [{'E',[2]},
                                      {'S',[3]},
                                      {'V',[1]},
                                      {"*",[4]},
                                      {"x",[5]}]} when is_integer(Hash),
                      lists:nth(1, Table)),
       ?_assertMatch(#state{id = 1,
                             items = [{'E',['V','.'],'$'},
                                      {'S',['V','.',"=",'E'],'$'}],
                             items_hash = Hash,
                             edges = [{"=",[6]}]} when is_integer(Hash),
                     lists:nth(2, Table)),
       ?_assertMatch(#state{id = 2,
                             items = [{'S',['E','.'],'$'}],
                             items_hash = Hash,
                             edges = []} when is_integer(Hash),
                                              lists:nth(3, Table)),
        ?_assertMatch(#state{id = 3,
                             items = [{'S\'',['S','.','$'],[]}],
                             items_hash = Hash,
                             edges = []} when is_integer(Hash),
                     lists:nth(4, Table)),
       ?_assertMatch(#state{id = 4,
                            items = [{'E',['.','V'],'$'},
                                     {'E',['.','V'],"="},
                                     {'V',['.',"*",'E'],'$'},
                                     {'V',['.',"*",'E'],"="},
                                     {'V',['.',"x"],'$'},
                                     {'V',['.',"x"],"="},
                                     {'V',["*",'.','E'],'$'},
                                     {'V',["*",'.','E'],"="}],
                            items_hash = Hash,
                            edges = [{'E',"\b"},
                                     {'V',[7]},
                                     {"*",[4]},
                                     {"x",[5]}]} when is_integer(Hash),
                     lists:nth(5, Table)),
        ?_assertMatch(#state{id = 5,
                            items = [{'V',["x",'.'],'$'},
                                     {'V',["x",'.'],"="}],
                            items_hash = Hash,
                            edges = []} when is_integer(Hash),
                     lists:nth(6, Table)),
        ?_assertMatch(#state{id = 6,
                            items = [{'E',['.','V'],'$'},
                                      {'S',['V',"=",'.','E'],'$'},
                                      {'V',['.',"*",'E'],'$'},
                                      {'V',['.',"x"],'$'}],
                            items_hash = Hash,
                            edges = [{'E',"\t"},
                                      {'V',[7]},
                                      {"*",[4]},
                                      {"x",[5]}]} when is_integer(Hash),
                     lists:nth(7, Table)),
        ?_assertMatch(#state{id = 7,
                            items = [{'E',['V','.'],'$'},
                                     {'E',['V','.'],"="}],
                            items_hash = Hash,
                            edges = []} when is_integer(Hash),
                     lists:nth(8, Table)),
        ?_assertMatch(#state{id = 8,
                            items = [{'V',["*",'E','.'],'$'},
                                     {'V',["*",'E','.'],"="}],
                            items_hash = Hash,
                            edges = []} when is_integer(Hash),
                     lists:nth(9, Table)),
        ?_assertMatch(#state{id = 9,
                            items = [{'S',['V',"=",'E','.'],'$'}],
                            items_hash = Hash,
                            edges = []} when is_integer(Hash),
                     lists:nth(10, Table))
       ]
   end}.

%%%_* Test helpers =============================================================
%%%_* Emacs ====================================================================
%%% Local Variables:
%%% allout-layout: t
%%% erlang-indent-level: 2
%%% End:
