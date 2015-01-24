%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%% @doc Context free grammars.
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
-module(elx_dfa).

%%%_* Exports ==================================================================
-export([action/3,
         check/1,
         goto/3,
         start_state/2,
         new/1]).

-export_type([dfa/0]).

%%%_* Includes =================================================================
-include_lib("eunit/include/eunit.hrl").

-include("elx.hrl").

%%%_* Defines ==================================================================

-record(non_term, {nullable = false         :: boolean(),
                   first    = ordsets:new() :: ordsets:ordset()}).

-record(dfa, {start       = [] :: [{elx_grammar:symbol(), state_id()}],
              states      = [] :: state(),
              precedence  = [] :: [{{elx_grammar:symbol() |
                                     elx_grammar:production()},
                                    elx_grammar:precedence()}]}).


-record(state, {id                         :: state_id(),
                items      = []            :: [item()],
                items_hash                 :: integer(),
                edges      = orddict:new() :: orddict:orddict()}).

%%%_* Types ====================================================================
-opaque dfa() :: #dfa{}.

-type state()           :: #state{}.
-type state_id()        :: non_neg_integer().

-type item()            :: {ProdLeft   :: elx_grammar:symbol(),
                            ProdR      :: [elx_grammar:symbol()],
                            Lookaheads :: [elx_grammar:symbol()]}.

%%%_* API ======================================================================

%%------------------------------------------------------------------------------
%% @doc
%% Return DFA's next action when reading Token with Lookahead in State.
-spec action(DFA     :: dfa(),
             StateId :: state_id(),
             Token   :: term()) ->
                accept                             |
                {shift,  state_id()}               |
                {reduce, elx_grammar:production()} |
                {goto,   state_id()}               |
                {error,  term()}.
%%------------------------------------------------------------------------------
action(#dfa{states = States, precedence = Precedence}, StateId, Token) ->
  do_action(lists:keyfind(StateId, #state.id, States), Precedence, Token).


%%------------------------------------------------------------------------------
%% @doc
%% Return DFA's next state when the lookahead is NonTerminal.
-spec goto(DFA         :: dfa(),
           StateId     :: state_id(),
           NonTerminal :: elx_grammar:symbol()) ->
              {ok, state_id()} |
              {error, {unexpected_token, elx_grammar:symbol()}}.
%%------------------------------------------------------------------------------
goto(#dfa{states = States}, StateId, NonTerminal) when is_atom(NonTerminal) ->
  #state{edges = Edges} = lists:keyfind(StateId, #state.id, States),
  case lists:keyfind(NonTerminal, 1, Edges) of
    {NonTerminal, [ToStateId|_]} -> {ok, ToStateId};
    false                        -> {error, {unexpected_token, NonTerminal}}
  end.



%%------------------------------------------------------------------------------
%% @doc Check DFA for conflicts.
-spec check(DFA :: dfa()) -> ok | {error, {conflicts, [{atom(), state_id()}]}}.
%%------------------------------------------------------------------------------
check(#dfa{states = States, precedence = Prec}) ->
  case lists:flatmap(fun(State) -> state_conflicts(State, Prec) end, States) of
    []        -> ok;
    Conflicts -> {error, {conflicts, Conflicts}}
  end.

%%------------------------------------------------------------------------------
%% @doc Return the id of dfa start state corresponding to StartSymbol.
-spec start_state(DFA :: dfa(), StartSymbol :: elx_grammar:symbol()) ->
              {ok, state_id()} |
              {error, {not_start_symbol, elx_grammar:symbol()}}.
%%------------------------------------------------------------------------------
start_state(#dfa{start = Start}, StartSymbol) ->
  case lists:keyfind(StartSymbol, 1, Start) of
    {StartSymbol, StartStateId} -> {ok, StartStateId};
    false                       -> {error, {not_start_symbol, StartSymbol}}
  end.

%%------------------------------------------------------------------------------
%% @doc Return a new dfa() computed from Grammar
-spec new(Grammar :: elx_grammar:grammar()) -> dfa().
%%------------------------------------------------------------------------------
new(Grammar) ->
  new(elx_grammar:productions(Grammar),
      elx_grammar:term_symbols(Grammar),
      elx_grammar:start_symbols(Grammar),
      elx_grammar:precedence(Grammar)).

%%%_* Internal functions =======================================================

new(Productions, Terms, StartSymbols, Precedence) ->
  NonTerms = first_sets(Productions, Terms, grammar_non_terms(Productions)),
  {Start, StartStates} = init_start_states(Productions,
                                           Terms,
                                           NonTerms,
                                           StartSymbols),
  #dfa{start = Start,
       states = dfa_table(Productions, Terms, NonTerms, StartStates),
       precedence = Precedence}.


do_action(#state{items = Items}, Precedence, ?eof) ->
  case reduction_rule(Items, Precedence, ?eof) of
    undefined ->
      case lists:any(fun item_accept_p/1, Items) of
        true  -> accept;
        false -> {error, eof}
      end;
    Rule -> {reduce, Rule}
  end;
do_action(State, Precedence, Token) ->
  ReductionRule = reduction_rule(State#state.items, Precedence, Token),
  ShiftState    = shift_state(State, Token),
  case {ShiftState, ReductionRule} of
    {undefined, undefined} -> {error, {unexpected_token, Token}};
    {undefined, Rule}      -> {reduce, Rule};
    {StateId,   undefined} -> {shift, StateId};
    {StateId, Rule}  ->
      case resolve_shift_reduce(Precedence, Rule, Token) of
        shift  -> {shift, StateId};
        reduce -> {reduce, Rule};
        error  -> {error, {unexpected_token, Token}}
      end
  end.

%% See Bison Manual 5.3.5: How Precedence Works
resolve_shift_reduce(Precedence, Rule, Token) ->
  case {precedence(Precedence, Rule), precedence(Precedence, Token)} of
    {_,                 undefined}                                -> shift;
    {undefined,         _}                                        -> shift;
    {{RulePrec, _},     {TokenPrec, _}} when RulePrec > TokenPrec -> reduce;
    {{Ruleprec, _},     {TokenPrec, _}} when Ruleprec < TokenPrec -> shift;
    {{Prec,  right},    {Prec,  right}}                           -> shift;
    {{Prec,  left},     {Prec,  left}}                            -> reduce;
    {{Prec,  prec},     {Prec,  prec}}                            -> shift;
    {{Prec,  nonassoc}, {Prec,  nonassoc}}                        -> error
  end.

precedence(Precedence, RuleOrTerminal) ->
  case lists:keyfind(RuleOrTerminal, 1, Precedence) of
    {RuleOrTerminal, Lvl} -> Lvl;
    false                 -> undefined
  end.

shift_state(#state{edges = Edges}, Token) ->
  case lists:keyfind(Token, 1, Edges) of
    {Token, [StateId|_]} -> StateId;
    false                -> undefined
  end.

reduction_rule(Items, Precedence, Token) ->
  case reduction_item(Items, Precedence, Token) of
    {undefined, undefined} -> undefined;
    {_ItemPrec, Item}      -> item_to_rule(Item)
  end.

state_conflicts(#state{id = Id, items = Items}, Precedence) ->
  lists:flatmap(fun({Lookahead, Rules}) ->
                   state_lookahead_conflicts(Id, Lookahead, Rules, Precedence)
                end,
                group_items_by_lookahead(orddict:to_list(Items))).

group_items_by_lookahead(Items) ->
  orddict:to_list(
    orddict:fold(
      fun(Production, Lookaheads, LookaheadMap0) ->
          ordsets:fold(fun(Lookahead, LookaheadMap) ->
                           Rule = {Production, Lookaheads},
                           orddict:update(Lookahead, fun(Rs) -> [Rule|Rs] end,
                                          [Rule],
                                          LookaheadMap)
                       end,
                       LookaheadMap0,
                       Lookaheads)
      end,
      orddict:new(),
      Items)).

state_lookahead_conflicts(StateId, Lookahead, Items, Precedence) ->
  {Reduce, Shift} = lists:partition(fun(I) -> item_reduce_p(I) end, Items),
  {RulePrec, _} = reduction_item(Reduce, Precedence, Lookahead),
  Errors0 = case {Reduce, Shift} of
              _ when Lookahead =:= ?eof -> [];
              {[], _}                   -> [];
              {_,  []}                  -> [];
              {[_|_], [_|_]}            ->
                case {RulePrec, precedence(Precedence, Lookahead)} of
                  {undefined, undefined} -> [{shift_reduce, StateId}];
                  _                         -> []
                end
            end,
  case length(Reduce) > 1 of
    true when RulePrec =:= undefined -> [{reduce_reduce, StateId}|Errors0];
    _                                -> Errors0
  end.

init_start_states(Productions, Terms, NonTerms, StartSymbols) ->
  SymbolIdMap = lists:zip(StartSymbols, lists:seq(0, length(StartSymbols) - 1)),
  States =
    lists:map(fun({Start, Id}) ->
                  init_start_state(Productions, Terms, NonTerms, Start, Id)
              end,
              SymbolIdMap),
  {SymbolIdMap, States}.

init_start_state(Productions, Terms, NonTerms, Start, Id) ->
  AuxStart = {elx_grammar:symbol_to_start_symbol(Start), [Start, ?eof]},
  StartItems = item_add(item_init(AuxStart, []), orddict:new()),
  Items = closure(Productions, Terms, NonTerms, StartItems),
  #state{id = Id, items = Items, items_hash = items_hash(Items)}.

dfa_table(Grammar, Terms, NonTerms, States0) ->
  States = do_graph(Grammar, Terms, NonTerms, States0),
  case States =:= States0 of
    true   -> States0;
    false  -> dfa_table(Grammar, Terms, NonTerms, States)
  end.

do_graph(Grammar, Terms, NonTerms, States0) ->
  lists:foldl(fun(State, States) ->
                  graph_state(Grammar, Terms, NonTerms, State, States)
              end,
              States0,
              States0).

graph_state(Grammar, Terms, NonTerms, State, States0) ->
  Id = State#state.id,
  lists:foldl(fun(Item, States) ->
                  % TODO Send in the state instead of ID
                  add_item_state(Grammar, Terms, NonTerms, Item, Id, States)
              end,
              States0,
              State#state.items).

add_item_state(Grammar, Terms, NonTerms, Item, ItemStateId, States0) ->
  case item_next(Item) of
    ?eof           -> States0;
    {error, empty} -> States0;
    Next           ->
      From = lists:keyfind(ItemStateId, #state.id, States0),
      {ToId, States} = go_to(Grammar, Terms, NonTerms, From, States0, Next),
      lists:keystore(ItemStateId, #state.id, States, add_edge(From, Next, ToId))
  end.

add_edge(#state{edges = Edges} = From, NextToken, ToId) ->
  Update = fun(TokenEdges) -> ordsets:add_element(ToId, TokenEdges) end,
  From#state{edges = orddict:update(NextToken, Update, [ToId], Edges)}.

next_state_id(States) ->
  lists:max([Id || #state{id = Id} <- States]) + 1.

go_to(Grammar, Terms, NonTerms, From, States0, Token) ->
  To0 = do_go_to(Grammar, Terms, NonTerms, From, Token, orddict:new()),
  case lists:keytake(To0#state.items_hash, #state.items_hash, States0) of
    false    ->
      Id = next_state_id(States0),
      {Id, lists:sort([To0#state{id = Id}|States0])};
    {value, #state{id = Id} = To, States} ->
      {Id, lists:sort([merge_state_items(To, To0)|States])}
  end.

merge_state_items(#state{items = Items1} = State1, #state{items = Items2}) ->
  State1#state{items = merge_closures(Items1, Items2)}.

do_go_to(Grammar, Terms, NonTerms, #state{items = []}, _Token, Acc) ->
  Items = closure(Grammar, Terms, NonTerms, Acc),
  #state{items = Items, items_hash = items_hash(Items)};
do_go_to(Grammar, Terms, NonTerms, State,  Token, Acc0) ->
  [Item|Rst] = State#state.items,
  Acc = case item_next(Item) of
          Token -> item_add(item_advance(Item), Acc0);
          _     -> Acc0
        end,
  do_go_to(Grammar, Terms, NonTerms, State#state{items = Rst}, Token, Acc).

closure(Grammar, Terms, NonTerms, Items0) ->
  case do_closure(Grammar, Terms, NonTerms, Items0) of
    Items0 -> Items0;
    Items  -> closure(Grammar, Terms, NonTerms, Items)
  end.

do_closure(Grammar, Terms, NonTerms, Items) ->
  orddict:fold(fun(Prod, Lookaheads, Acc) ->
                   Closure = item_closure(Grammar, Terms, NonTerms, {Prod, Lookaheads}),
                   merge_closures(Closure, Acc)
               end,
               Items,
               Items).

% Merge Closure1 into Closure2. A closure is a list of items.
merge_closures(Closure1, Closure2) ->
  orddict:fold(fun(Prod, Lookaheads, Closure) ->
                   item_add({Prod, Lookaheads}, Closure)
               end,
               Closure2,
               Closure1).

item_add({Prod, Lookaheads}, Dict) ->
  MergeLAs = fun(Lookaheads0) ->
                 ordsets:union(Lookaheads, Lookaheads0)
             end,
  orddict:update(Prod, MergeLAs, Lookaheads, Dict).

%% An item contains a point and a lookahead token for a dfa. A rule doesn't.
item_to_rule({{ProdL, ProdR}, _Lookaheads}) ->
  {ProdL, lists:delete(?point, ProdR)}.

reduction_item(Rules, Precedence, Lookahead) ->
  reduction_item(Rules, Precedence, Lookahead, undefined, undefined).

reduction_item([], _Prec, _Lookahead, Highest, HighestRule) ->
  {Highest, HighestRule};
reduction_item([Rule|Rs], Prec, Lookahead, Highest, HighestRule) ->
  {{_, _}, Lookaheads} = Rule,
  {NewHighest, NewHighestRule} =
    case lists:member(Lookahead, Lookaheads) and item_reduce_p(Rule) of
      false -> {Highest, HighestRule};
      true  ->
        case precedence(Prec, Rule) of
          undefined when HighestRule =:= undefined -> {undefined, Rule};
          undefined                                -> {Highest,   HighestRule};
          RulePrec when Highest =:= undefined      -> {RulePrec,  Rule};
          RulePrec when RulePrec > Highest         -> {RulePrec,  Rule};
          _                                        -> {Highest,   HighestRule}
        end
    end,
  reduction_item(Rs, Prec, Lookahead, NewHighest, NewHighestRule).

items_hash(Items) ->
  erlang:phash2(ordsets:from_list([Prod || {Prod, _LA} <- Items])).

item_init({L, R}, Lookaheads) ->
  {{L, [?point|R]}, ordsets:from_list(Lookaheads)}.

item_advance({{L, R}, Lookaheads}) ->
  {{L, item_advance_r(R, [])}, Lookaheads}.

item_advance_r([?point,Next|Rest], Acc) ->
  lists:reverse(Acc) ++ [Next, ?point] ++ Rest;
item_advance_r([Next|Rest], Acc) ->
  item_advance_r(Rest, [Next|Acc]).

item_accept_p({{_ProdL, ProdR}, _}) ->
  case lists:reverse(ProdR) of
    [?eof, ?point|_] -> true;
    _            -> false
  end.

item_reduce_p(Item) ->
  item_next(Item) =:= {error, empty}.

item_next(Item) ->
  case item_partition_next(Item) of
    {error, _} = E  -> E;
    {Next, _Rest}   -> Next
  end.

item_partition_next({{_L, R}, _Lookaheads}) ->
  case lists:splitwith(fun(T) -> T =/= ?point end, R) of
    {_, [?point]} -> {error, empty};
    {_, [?point, Next|Rest]} -> {Next, Rest}
  end.

item_closure(Grammar, Terms, NonTerms, Item) ->
  case item_partition_next(Item) of
    {error, empty} ->
      orddict:new();
    {Next, Rest} ->
      F = fun({ProdL, _ProdR} = Prod, Acc) when ProdL =:= Next ->
              Lookaheads = item_lookaheads(Terms, NonTerms, Rest, Item),
              item_add(item_init(Prod, Lookaheads), Acc);
             (_Prod, Acc) ->
              Acc
          end,
      orddict:from_list(lists:foldl(F, [], Grammar))
  end.

item_lookaheads(Terms, NonTerms, Rest, {{_ItemL, _ItemR}, ItemLookaheads}) ->
  First = prod_first(Terms, NonTerms, Rest),
  case prod_nullable_p(Rest, Terms, NonTerms) of
    false -> First;
    true  ->
      ordsets:fold(fun(Lookahead, Acc) ->
                       prod_first(Terms, NonTerms, [Lookahead], Acc)
                   end,
                   First,
                   ItemLookaheads)
  end.

first_sets(Productions, Terms) ->
  first_sets(Productions, Terms, grammar_non_terms(Productions)).

first_sets(Productions, Terms, NonTerms0) ->
  case do_first_sets(Productions, Terms, NonTerms0) of
    NonTerms0 -> NonTerms0;
    NonTerms  -> first_sets(Productions, Terms, NonTerms)
  end.

do_first_sets(Productions, Terms, NonTerms) ->
  lists:foldl(fun(P, NonTerms1) -> production_first(P, Terms, NonTerms1) end,
              NonTerms,
              Productions).

production_first(Production, Terms, NonTerms) ->
  update_prod_first(Production,
                    Terms,
                    update_prod_nullable(Production, Terms, NonTerms)).

update_prod_first({ProdL, ProdR}, Terms, NonTerms) ->
  Update = fun(#non_term{first = First} = NT) ->
               NT#non_term{first = prod_first(Terms, NonTerms, ProdR, First)}
           end,
  orddict:update(ProdL, Update, NonTerms).

grammar_non_terms(Grammar) ->
  orddict:from_list([{L, #non_term{}} || {L, _R} <- Grammar]).

update_prod_nullable({ProdL, ProdR}, Terms, NonTerms) ->
  Update = fun(#non_term{nullable = true} = NT) ->
               NT;
              (NT) ->
               NT#non_term{nullable = prod_nullable_p(ProdR, Terms, NonTerms)}
           end,
  orddict:update(ProdL, Update, NonTerms).

prod_nullable_p(ProdR, Terms, NonTerms) ->
  lists:all(fun(?eof) -> false;
               (Symbol) ->
               case lists:member(Symbol, Terms) of
                 true ->
                   false;
                 false ->
                   (orddict:fetch(Symbol, NonTerms))#non_term.nullable
               end
            end,
            ProdR).

prod_first(Terms, NonTerms, Prod)  ->
  prod_first(Terms, NonTerms, Prod, ordsets:new()).

prod_first(_Terms, _NonTerms, [],            Acc)  ->
  Acc;
prod_first(_Terms, _NonTerms, [?eof|_Rest],   Acc)  ->
  ordsets:add_element(?eof, Acc);
prod_first( Terms,  NonTerms, [Symbol|Rest], Acc0) ->
  case lists:member(Symbol, Terms) of
    true ->
      ordsets:add_element(Symbol, Acc0);
    false ->
      NonTerm = orddict:fetch(Symbol, NonTerms),
      Acc = ordsets:union(Acc0, NonTerm#non_term.first),
      case NonTerm#non_term.nullable  of
        true  -> prod_first(Terms, NonTerms, Rest, Acc);
        false -> Acc
      end
  end.

%%%_* Tests ====================================================================

new_test_() ->
  [?_assertMatch(#dfa{states = [#state{id = 0}|_]},
                new(elx_grammar:new([{'A', ['a', 'b']}],
                                    ['a', 'b'],
                                    ['A'],
                                    [])))
  ].

first_test_() ->
  [?_assertEqual(
      [{'B', #non_term{nullable = false, first = ['w']}},
       {'D', #non_term{nullable = true,  first = ['x', 'y']}},
       {'E', #non_term{nullable = true,  first = ['y']}},
       {'F', #non_term{nullable = true,  first = ['x']}},
       {'S', #non_term{nullable = false, first = ['u']}}],
      first_sets([{'S', ['u', 'B', 'D', 'z']},
                  {'B', ['B', 'v']},           {'B', ['w']},
                  {'D', ['E', 'F']},
                  {'E', ['y']},                {'E', []},
                  {'F', ['x']},                {'F', []}],
                 ['u', 'x', 'y', 'w', 'z'])),
   ?_assertEqual(
      [{'E', #non_term{nullable = false, first = ['(', '-', 'x']}},
       {'L', #non_term{nullable = true,  first = ['(']}},
       {'M', #non_term{nullable = true,  first = ['-']}},
       {'S', #non_term{nullable = false, first = ['(', '-', 'x']}},
       {'V', #non_term{nullable = false, first = ['x']}}],
      first_sets([{'S', ['E', ?eof]},
                  {'E', ['-', 'E']}, {'E', ['(', 'E', ')']}, {'E', ['V', 'M']},
                  {'M', ['-', 'E']}, {'M', []},
                  {'V', ['x', 'L']},
                  {'L', ['(', 'E', ')']}, {'L', []}],
                 ['(', ')', '-', 'x']))
  ].

update_prod_nullable_test_() ->
  {setup,
   fun() ->
       Grammar = [{'A', ['b']},
                  {'B', []},
                  {'C', ['A']},
                  {'D', ['B']}],
       NonTerms = grammar_non_terms(Grammar),
       {Grammar, ['b'], NonTerms}
   end,
   fun({Grammar, Terms, NonTerms}) ->
       [?_assertEqual(#non_term{nullable = false},
                      orddict:fetch(
                        'A',
                        update_prod_nullable(lists:nth(1, Grammar),
                                             Terms,
                                             NonTerms))),
        ?_assertEqual(#non_term{nullable = true},
                      orddict:fetch(
                        'B',
                        update_prod_nullable(lists:nth(2, Grammar),
                                             Terms,
                                             NonTerms))),
        ?_assertEqual(#non_term{nullable = false},
                      orddict:fetch(
                        'C',
                        update_prod_nullable(lists:nth(3, Grammar),
                                             Terms,
                                             NonTerms))),
        ?_assertEqual(#non_term{nullable = true},
                      orddict:fetch(
                        'D',
                        update_prod_nullable(
                          lists:nth(4, Grammar),
                          Terms,
                          orddict:store('B',
                                        #non_term{nullable = true},
                                        NonTerms)
                          )))
       ]
   end}.

update_prod_first_test_() ->
  {setup,
   fun() ->
       Grammar = [{'A', ['b']},
                  {'B', []},
                  {'C', ['A']},
                  {'D', ['B', 'a']}],
       NonTerms = grammar_non_terms(Grammar),
       {Grammar, ['a', 'b'], NonTerms}
   end,
   fun({Grammar, Terms, NonTerms}) ->
       [?_assertEqual(#non_term{first = ['b']},
                      orddict:fetch(
                        'A',
                        update_prod_first(lists:nth(1, Grammar),
                                          Terms,
                                          NonTerms))),
        ?_assertEqual(#non_term{first = []},
                      orddict:fetch(
                        'B',
                        update_prod_first(lists:nth(2, Grammar),
                                          Terms,
                                          NonTerms))),
        ?_assertEqual(#non_term{first = ['b']},
                      orddict:fetch(
                        'C',
                        update_prod_first(
                          lists:nth(3, Grammar),
                          Terms,
                          orddict:store('A',
                                        #non_term{first = ['b']},
                                        NonTerms)
                          ))),
        ?_assertEqual(#non_term{first = ['a']},
                      orddict:fetch(
                        'D',
                        update_prod_first(
                          lists:nth(4, Grammar),
                          Terms,
                          orddict:store('B',
                                        #non_term{nullable = true},
                                        NonTerms))))
       ]
   end}.

dfa_table_2_test_() ->
  {setup,
   fun() ->
       new([{'S',   ['V', '=', 'E']}, {'S',   ['E']},
            {'E',   ['V']},
            {'V',   ['x']}, {'V', ['*', 'E']}],
           ['*', '=', 'x'],
           ['S'],
           [])
   end,
   fun(#dfa{states = Table}) ->
       [?_assertEqual(10, length(Table)),
        ?_assertMatch(#state{id = 0,
                             items = [{{'E',[?point,'V']},[?eof]},
                                      {{'S',[?point,'E']},[?eof]},
                                      {{'S',[?point,'V','=','E']},[?eof]},
                                      {{'S\'',[?point,'S',?eof]},[]},
                                      {{'V',[?point,'*','E']},['=', ?eof]},
                                      {{'V',[?point,'x']},['=', ?eof]}],
                             items_hash = Hash,
                             edges = [{'*',[4]},
                                      {'E',[2]},
                                      {'S',[3]},
                                      {'V',[1]},
                                      {'x',[5]}]} when is_integer(Hash),
                      lists:nth(1, Table)),
       ?_assertMatch(#state{id = 1,
                             items = [{{'E',['V',?point]},[?eof]},
                                      {{'S',['V',?point,'=','E']},[?eof]}],
                             items_hash = Hash,
                             edges = [{'=',[6]}]} when is_integer(Hash),
                     lists:nth(2, Table)),
       ?_assertMatch(#state{id = 2,
                             items = [{{'S',['E',?point]},[?eof]}],
                             items_hash = Hash,
                             edges = []} when is_integer(Hash),
                                              lists:nth(3, Table)),
        ?_assertMatch(#state{id = 3,
                             items = [{{'S\'',['S',?point,?eof]},[]}],
                             items_hash = Hash,
                             edges = []} when is_integer(Hash),
                     lists:nth(4, Table)),
       ?_assertMatch(#state{id = 4,
                            items = [{{'E',[?point,'V']},['=', ?eof]},
                                     {{'V',['*',?point,'E']},['=', ?eof]},
                                     {{'V',[?point,'*','E']},['=', ?eof]},
                                     {{'V',[?point,'x']},['=', ?eof]}],
                            items_hash = Hash,
                            edges = [{'*',[4]},
                                     {'E',[8]},
                                     {'V',[7]},
                                     {'x',[5]}]} when is_integer(Hash),
                     lists:nth(5, Table)),
        ?_assertMatch(#state{id = 5,
                            items = [{{'V',['x',?point]},['=', ?eof]}],
                            items_hash = Hash,
                            edges = []} when is_integer(Hash),
                     lists:nth(6, Table)),
        ?_assertMatch(#state{id = 6,
                             items = [{{'E',[?point,'V']},[?eof]},
                                      {{'S',['V','=',?point,'E']},[?eof]},
                                      {{'V',[?point,'*','E']},[?eof]},
                                      {{'V',[?point,'x']},[?eof]}],
                             items_hash = Hash,
                             edges = [{'*',[4]},
                                      {'E',[9]},
                                      {'V',[7]},
                                      {'x',[5]}]} when is_integer(Hash),
                     lists:nth(7, Table)),
        ?_assertMatch(#state{id = 7,
                            items = [{{'E',['V',?point]},['=', ?eof]}],
                            items_hash = Hash,
                            edges = []} when is_integer(Hash),
                     lists:nth(8, Table)),
        ?_assertMatch(#state{id = 8,
                            items = [{{'V',['*','E',?point]},['=', ?eof]}],
                            items_hash = Hash,
                            edges = []} when is_integer(Hash),
                     lists:nth(9, Table)),
        ?_assertMatch(#state{id = 9,
                            items = [{{'S',['V','=','E',?point]},[?eof]}],
                            items_hash = Hash,
                            edges = []} when is_integer(Hash),
                     lists:nth(10, Table))
       ]
   end}.

check_test_() ->
  [
   ?_assertEqual(ok, check(#dfa{ states = [#state{id = 1,
                                                  items = [{{'S',['V',?point]},[?eof]}],
                                                  edges = []}]})),

   ?_assertEqual({error, {conflicts, [{shift_reduce, 1}]}},
                 check(#dfa{ states = [#state{id = 1,
                                              items = [{{'S',['V',?point]},['a']},
                                                       {{'S',['V',?point, 'E']},['a']}
                                                      ],
                                                  edges = []}]})),

   ?_assertEqual({error, {conflicts, [{reduce_reduce, 1}]}},
                 check(#dfa{ states = [#state{id = 1,
                                              items = [{{'S',['V',?point]},[?eof]},
                                                       {{'S',['E',?point]},[?eof]}
                                                      ],
                                                  edges = []}]})),

   ?_assertEqual({error, {conflicts, [{reduce_reduce, 1}, {shift_reduce, 1}]}},
                 check(#dfa{ states =
                               [#state{id = 1,
                                       items = [{{'S',['V',?point]},['a']},
                                                {{'S',['E',?point]},['a']},
                                                {{'S',['V',?point, 'E']},['a']}
                                               ],
                                       edges = []}]})),

   ?_assertEqual(ok, check(#dfa{ states =
                                   [#state{id = 1,
                                           items = [{{'S',['V',?point]},[?eof]},
                                                     {{'S',['V',?point]},['E']}],
                                           edges = []}]}))
  ].

init_test_() ->
  [?_assertMatch({ok, 1},
                 start_state(#dfa{start = [{'S', 1}]}, 'S')),
   ?_assertEqual({error, {not_start_symbol, 'S'}},
                 start_state(#dfa{start = []}, 'S'))
  ].

eof_test_() ->
  [
   ?_assertEqual(accept,
                action(#dfa{states =
                              [#state{id = 1,
                                      items = [{{'S',['V', ?point, ?eof]},
                                                [?eof]}]}]},
                       1,
                       ?eof)),
  ?_assertEqual({error, eof},
                action(#dfa{states =
                              [#state{id = 1,
                                      items = [{{'S',['V', ?point, 'a']},
                                                ['a']}]}]},
                       1,
                       ?eof)),
  ?_assertEqual({reduce, {'S', ['V']}},
                action(#dfa{states =
                              [#state{id = 1,
                                      items = [{{'S',['V', ?point]},
                                                [?eof]}]}]},
                       1,
                       ?eof))
  ].

action_test_() ->
  [?_assertEqual({shift, 2},
                 action(#dfa{states = [#state{id = 1,
                                              items = [{{'S',[?point, 'V']},
                                                        [?eof]}],
                                              edges = [{'x', [2]}]}]},
                        1,
                        'x')),
  %% % Only option is to reduce
  ?_assertEqual({reduce, {'S', ['V']}},
                action(#dfa{states = [#state{id = 1,
                                             items = [{{'S',['V', ?point]},
                                                       ['a']}],
                                             edges = []}],
                            precedence = [{'a',         {1, left}},
                                          {{'S',['V']}, {2, left}}]},
                       1,
                       'a')),
  % Rule has higher precedence
  ?_assertEqual({reduce, {'S', ['V']}},
                action(#dfa{states = [#state{id = 1,
                                             items = [{{'S',['V', ?point]},
                                                       ['a']}],
                                             edges = [{'a', [2]}]}],
                            precedence = [{'a',         {1, left}},
                                          {{'S',['V']}, {2, left}}]},
                       1,
                       'a')),
  % Symbol has higher precedence
  ?_assertEqual({shift, 2},
                action(#dfa{states = [#state{id = 1,
                                             items = [{{'S',['V', ?point]},
                                                       ['a']}],
                                             edges = [{'a', [2]}]}],
                            precedence = [{'a',         {2, left}},
                                          {{'S',['V']}, {1, left}}]},
                       1,
                       'a')),
  % Symbol and rule have same precedence, left associative
  ?_assertEqual({reduce, {'S', ['V']}},
                action(#dfa{states = [#state{id = 1,
                                             items = [{{'S',['V', ?point]},
                                                       ['a']}],
                                             edges = [{'a', [2]}]}],
                            precedence = [{'a',         {1, left}},
                                          {{'S',['V']}, {1, left}}]},
                       1,
                       'a')),
  % Symbol and rule have same precedence, right associative
  ?_assertEqual({shift, 2},
                action(#dfa{states = [#state{id = 1,
                                             items = [{{'S',['V', ?point]},
                                                       ['a']}],
                                             edges = [{'a', [2]}]}],
                            precedence = [{'a',         {1, right}},
                                          {{'S',['V']}, {1, right}}]},
                       1,
                       'a')),
  % Symbol has no precedence
  ?_assertEqual({shift, 2},
                action(#dfa{states = [#state{id = 1,
                                             items = [{{'S',['V', ?point]},
                                                       ['a']}],
                                             edges = [{'a', [2]}]}],
                            precedence = [{{'S',['V']}, {2, left}}]},
                       1,
                       'a')),
  % Rule has no precedence
  ?_assertEqual({shift, 2},
                action(#dfa{states = [#state{id = 1,
                                             items = [{{'S',['V', ?point]},
                                                       ['a']}],
                                             edges = [{'a', [2]}]}],
                            precedence = [{'a', {1, left}}]},
                       1,
                       'a')),
  % Neither has precedence
  ?_assertEqual({shift, 2},
                action(#dfa{states = [#state{id = 1,
                                             items = [{{'S',['V', ?point]},
                                                       ['a']}],
                                             edges = [{'a', [2]}]}],
                            precedence = []},
                       1,
                       'a')),
   % Nonassoc declaration triggers a syntax error
   ?_assertEqual({error, {unexpected_token, 'a'}},
                 action(#dfa{states = [#state{id = 1,
                                              items = [{{'S',['V', ?point]},
                                                        ['a']}],
                                              edges = [{'a', [2]}]}],
                             precedence = [{'a',         {1, nonassoc}},
                                           {{'S',['V']}, {1, nonassoc}}]},
                        1,
                        'a')),
   ?_assertEqual({error, {unexpected_token, 'A'}},
                 action(#dfa{states =
                               [#state{id = 1,
                                       items = [{{'B', [?point, 'A']}, ['a']}]}]},
                        1,
                        'A'))
  ].

goto_test_() ->
  [?_assertEqual({ok, 2},
                 goto(#dfa{states =
                             [#state{id = 1,
                                     items = [{{'B', [?point, 'A']}, ['a']}],
                                     edges = [{'A', [2]}]}]},
                      1,
                      'A')),
   ?_assertEqual({error, {unexpected_token, 'B'}},
                 goto(#dfa{states =
                             [#state{id = 1,
                                     items = [{{'B', [?point, 'A']}, ['a']}],
                                     edges = [{'A', [2]}]}]},
                      1,
                      'B'))
  ].

cyclic_dfa_test_() ->
  {setup,
  fun() ->
      new(elx_grammar:new([{'E', ['E', '+', 'E']},
                           {'E', ['1']}],
                          ['1', '+'],
                          ['E'],
                          []))
  end,
  fun(#dfa{states = States}) ->
      [?_assertEqual(5, length(States)),
       ?_assertMatch(#state{id = 0,
                            items = [{{'E',[?point,'1']},['+', ?eof]},
                                     {{'E',[?point,'E','+','E']},['+', ?eof]},
                                     {{'E\'',[?point,'E',?eof]},[]}],
                            edges = [{'1',[1]},
                                     {'E',[2]}]},
                     lists:nth(1, States)),
       ?_assertMatch(#state{id = 1,
                            items = [{{'E',['1',?point]},['+', ?eof]}],
                            edges = []},
                     lists:nth(2, States)),
       ?_assertMatch(#state{id = 2,
                            items = [{{'E',['E',?point,'+','E']},['+', ?eof]},
                                     {{'E\'',['E',?point,?eof]},[]}],
                            edges = [{'+',[3]}]},
                    lists:nth(3, States)),
       ?_assertMatch(#state{id = 3,
                            items = [{{'E',['E','+',?point,'E']},['+', ?eof]},
                                     {{'E',[?point,'1']},['+', ?eof]},
                                     {{'E',[?point,'E','+','E']},['+', ?eof]}],
                            edges = [{'1',[1]},
                                     {'E',[4]}]},
                     lists:nth(4, States)),
       ?_assertMatch(#state{id = 4,
                            items = [{{'E',['E','+','E',?point]},['+', ?eof]},
                                     {{'E',['E',?point,'+','E']},['+', ?eof]}],
                            edges = [{'+',[3]}]},
                    lists:nth(5, States))
      ]
  end}.

reduction_item_test_() ->
  [% Base case
   ?_assertEqual({undefined, undefined},
                reduction_item([], [], [])),
   % Only one item
   ?_assertEqual({undefined, {{'A', ['a', ?point]}, ['b']}},
                reduction_item([{{'A', ['a', ?point]}, ['b']}], [], 'b')),
   % Take first rule if no precedence  specified
   ?_assertEqual({undefined, {{'A', ['a', ?point]}, ['b']}},
                reduction_item([{{'A', ['a', ?point]}, ['b']},
                                {{'B', ['a', ?point]}, ['b']}],
                               [],
                               'b')),
   % Assert that first rule is ignored if it's not a reduction rule
   ?_assertEqual({undefined, {{'B', ['a', ?point]}, ['b']}},
                reduction_item([{{'A', ['a', ?point, 'c']}, ['b']},
                                {{'B', ['a', ?point]}, ['b']}],
                               [],
                               'b')),
   % Assert that first rule is ignored if its lookahead doesn't match
   ?_assertEqual({undefined, {{'B', ['a', ?point]}, ['b']}},
                reduction_item([{{'A', ['a', ?point]}, ['a']},
                                {{'B', ['a', ?point]}, ['b']}],
                               [],
                               'b')),
   % Assert that rule with precedence is chosen over rule with no precedence
   ?_assertEqual({1, {{'B', ['a', ?point]}, ['b']}},
                reduction_item([{{'A', ['a', ?point]}, ['b']},
                                {{'B', ['a', ?point]}, ['b']}],
                               [{{{'B', ['a', ?point]}, ['b']}, 1}],
                               'b')),
   % Assert that rule with highest precedence is chosen
   ?_assertEqual({3, {{'B', ['a', ?point]}, ['b']}},
                reduction_item([{{'A', ['a', ?point]}, ['b']},
                                {{'B', ['a', ?point]}, ['b']},
                                {{'C', ['a', ?point]}, ['b']}],
                               [{{{'A', ['a', ?point]}, ['b']}, 1},
                                {{{'B', ['a', ?point]}, ['b']}, 3},
                                {{{'C', ['a', ?point]}, ['b']}, 2}],
                               'b'))
  ].

merge_closures_test_() ->
  [?_assertEqual([{{'A', ['a']}, ['a', 'b']}],
                merge_closures([{{'A', ['a']}, ['a']}],
                               [{{'A', ['a']}, ['b']}]))
  ].

%%%_* Emacs ====================================================================
%%% Local Variables:
%%% allout-layout: t
%%% erlang-indent-level: 2
%%% End:
