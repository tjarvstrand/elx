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
-export([]).

-export_type([grammar/0]).

%%%_* Includes =================================================================
-include_lib("eunit/include/eunit.hrl").

%%%_* Defines ==================================================================

-record(grammar, {productions = [] :: non_terminal()
                 }).

-record(non_term, {nullable = false,
                   first = ordsets:new(),
                   follow = ordsets:new()}).


-record(state, {id,
                items = [],
                edges = orddict:new()}).

%%%_* Types ====================================================================

-opaque grammar() :: #grammar{}.
-type non_terminal() :: #non_term{}.

%%%_* API ======================================================================

%%%_* Internal functions =======================================================

%% grammar_symbols(Grammar) ->
%%   grammar_symbols(Grammar, ordsets:new(), ordsets:new()).

%% grammar_symbols([], Terms, NonTerms) ->
%%   {ordsets:to_list(Terms), ordsets:to_list(NonTerms)};
%% grammar_symbols([Prod|Rest], Terms0, NonTerms0) ->
%%   {PTerms, PNonTerms} = production_symbols(Prod),
%%   Terms    = ordsets:union(Terms0,    PTerms),
%%   NonTerms = ordsets:union(NonTerms0, PNonTerms),
%%   grammar_symbols(Rest, Terms, NonTerms).

%% production_symbols({L, R}) ->
%%   {Terms, NonTerms} = lists:partition(fun is_list/1, R),
%%   {ordsets:from_list(Terms), ordsets:from_list([L|NonTerms])}.

dfa_table(Grammar) ->
  NonTerms = first_follow(Grammar),
  Items = closure(Grammar, NonTerms, [item_init(hd(Grammar), '_?_')]),
  dfa_table(Grammar, NonTerms, [#state{id = 0, items = Items}]).

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

go_to(Grammar, NonTerms, FromState, States, Token) ->
  ToState0 = do_go_to(Grammar, NonTerms, FromState, Token, ordsets:new()),
  case lists:keyfind(ToState0#state.items, #state.items, States) of
    false    ->
      Id = next_state_id(States),
      {Id, lists:sort([ToState0#state{id = Id}|States])};
    #state{id = Id} ->
      {Id, States}
  end.

do_go_to(Grammar, NonTerms, #state{items = []}, _Token, Acc) ->
  #state{items = closure(Grammar, NonTerms, Acc)};
do_go_to(Grammar, NonTerms, #state{items = [Item|Rst]} = State,  Token, Acc0) ->
  Acc = case item_next(Item) of
          Token -> ordsets:add_element(item_advance(Item), Acc0);
          _     -> Acc0
        end,
  do_go_to(Grammar, NonTerms, State#state{items = Rst}, Token, Acc).

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

first_follow(Productions) ->
  first_follow(grammar_non_terms(Productions), Productions).

first_follow(NonTerms0, Productions) ->
  case do_first_follow(NonTerms0, Productions) of
    NonTerms0 -> NonTerms0;
    NonTerms  -> first_follow(NonTerms, Productions)
  end.

do_first_follow(NonTerms, Productions) ->
  lists:foldl(fun(P, NonTerms1) ->
                  production_first_follow(NonTerms1, P)
                end,
                NonTerms,
                Productions).

production_first(NonTerms, Production) ->
  update_prod_first(update_prod_nullable(NonTerms, Production), Production).

production_first_follow(NonTerms, Production) ->
  update_prod_follow(production_first(NonTerms, Production), Production).

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

update_prod_follow(NonTerms, {ProdL, ProdR}) ->
  Follow = (orddict:fetch(ProdL, NonTerms))#non_term.follow,
  do_update_prod_follow(NonTerms, Follow, ProdR).

do_update_prod_follow(NonTerms, _ProdFollow, []) -> NonTerms;
do_update_prod_follow(NonTerms, ProdFollow, ['$'|Rest]) ->
  do_update_prod_follow(NonTerms, ProdFollow, Rest);
do_update_prod_follow(NonTerms, ProdFollow, [Next|Rest]) when is_list(Next) ->
  do_update_prod_follow(NonTerms, ProdFollow, Rest);
do_update_prod_follow(NonTerms0, ProdFollow, [Next|Rest]) when is_atom(Next) ->
  Update = fun(NonTerm) ->
               update_non_term_follow(NonTerms0, ProdFollow, NonTerm, Rest)
           end,
  NonTerms = orddict:update(Next, Update, NonTerms0),
  do_update_prod_follow(NonTerms, ProdFollow, Rest).


update_non_term_follow(_NTs, ProdFollow, NT, []) ->
  %% Everything up to this point has been nullable so we add the toplevel
  %% follow set to the non-terminal's follow set.
  NT#non_term{follow = ordsets:union(ProdFollow, NT#non_term.follow)};
update_non_term_follow(_NTs, _ProdFollow, NT, ['$'|_]) ->
  NT#non_term{follow = ordsets:add_element('$', NT#non_term.follow)};
update_non_term_follow(_NTs, _ProdFollow, NT, [Next|_]) when is_list(Next) ->
  %% Next is a terminal symbol. Since it's not nullable, don't add anything
  %% after it to the follow set.
  NT#non_term{follow = ordsets:add_element(Next, NT#non_term.follow)};
update_non_term_follow(NTs, ProdFollow, NT0, [Next|Rest]) when is_atom(Next) ->
  %% Next is a non-terminal symbol. Add it's first set to NT0's follow set and
  %% if Next is nullable, keep the first sets of subsequent symbols until a non-
  %% nullable symbol or the end of the production is reached.
  NextNT = orddict:fetch(Next, NTs),
  NT = add_first_to_follow(NT0, NextNT),
  case NextNT#non_term.nullable of
    true  -> update_non_term_follow(NTs, ProdFollow, NT, Rest);
    false -> NT
  end.

%% Add NonTerm2's first set to NonTerm1's follow set.
add_first_to_follow(#non_term{follow = S0} = NT1, #non_term{first = S1}) ->
  NT1#non_term{follow = ordsets:union(S0, S1)}.

%%%_* Tests ====================================================================

-define(grammar_1, ).

first_follow_test_() ->
  [?_assertEqual(
      [{'B', #non_term{nullable = false, first = ["w"],      follow = ["v", "x", "y", "z"]}},
       {'D', #non_term{nullable = true,  first = ["x", "y"], follow = ["z"]}},
       {'E', #non_term{nullable = true,  first = ["y"],      follow = ["x", "z"]}},
       {'F', #non_term{nullable = true,  first = ["x"],      follow = ["z"]}},
       {'S', #non_term{nullable = false, first = ["u"],      follow = []}}],
      first_follow([{'S', ["u", 'B', 'D', "z"]},
                    {'B', ['B', "v"]},           {'B', ["w"]},
                    {'D', ['E', 'F']},
                    {'E', ["y"]},                {'E', []},
                    {'F', ["x"]},                {'F', []}])),
   ?_assertEqual(
      [{'E', #non_term{nullable = false, first = ["(", "-", "x"], follow = ['$', ")"]}},
       {'L', #non_term{nullable = true,  first = ["("],           follow = ['$', ")", "-"]}},
       {'M', #non_term{nullable = true,  first = ["-"],           follow = ['$', ")"]}},
       {'S', #non_term{nullable = false, first = ["(", "-", "x"], follow = []}},
       {'V', #non_term{nullable = false, first = ["x"],           follow = ['$', ")", "-"]}}],
      first_follow([{'S', ['E', '$']},
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

%% dfa_table_test() ->
%%   ?assertEqual([#state{id = 0,
%%                        items = [{'E',['.','T',"+",'T']},
%%                                 {'S',['.','E','$']},
%%                                 {'T',['.',"id"]}],
%%                        edges = [{'E',[2]},
%%                                 {'T',[1]},
%%                                 {"id",[3]}]},
%%                 #state{id = 1,
%%                        items = [{'E',['T','.',"+",'T']}],
%%                        edges = [{"+",[4]}]},
%%                 #state{id = 2,
%%                        items = [{'S',['E','.','$']}],
%%                        edges = []},
%%                 #state{id = 3,
%%                        items = [{'T',["id",'.']}],
%%                        edges = []},
%%                 #state{id = 4,
%%                        items = [{'E',['T',"+",'.','T']},
%%                                 {'T',['.',"id"]}],
%%                        edges = [{'T',[5]},
%%                                 {"id",[3]}]},
%%                 #state{id = 5,
%%                        items = [{'E',['T',"+",'T','.']}],
%%                        edges = []}],
%%                dfa_table([{'S', ['E', '$']},
%%                           {'E', ['T', "+", 'T']},
%%                           {'T', ["id"]}])).

dfa_table_2_test() ->
  Tab = dfa_table([{'S\'', ['S', '$']},
                   {'S',   ['V', "=", 'E']}, {'S',   ['E']},
                   {'E',   ['V']},
                   {'V',   ["x"]}, {'V', ["*", 'E']}]),
  io:fwrite(user, <<"~p ~p ~p: Tab = ~p~n">>, [self(), ?MODULE, ?LINE, Tab]).

%%%_* Test helpers =============================================================
%%%_* Emacs ====================================================================
%%% Local Variables:
%%% allout-layout: t
%%% erlang-indent-level: 2
%%% End: