%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%% @doc Lexical analysis framework.
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
-module(elx_lex).

%%%_* Exports ==================================================================
-export([string/2,
         string/3,
         match_group_index/2,
         match_group_string/3,
         match_named_group_index/2,
         match_named_group_string/3]).

-export_type([grammar/0,
              match/0,
              point/0,
              token/0]).

%%%_* Includes =================================================================

-include_lib("eunit/include/eunit.hrl").

%%%_* Defines ==================================================================

%%%_* Types ====================================================================

-opaque grammar() :: [rule()].

-type rule()     :: {matcher(), action()}.
-type matcher()  :: Regexp :: string() |
                    {RegExp :: string(), Options :: [term()]}.
-type action()   :: fun((TokenChars :: string(),
                         TokenStart :: point(),
                         TokenEnd   :: point()) ->
                           token() | skip).


-type point() :: {Position :: non_neg_integer(),
                  Column   :: non_neg_integer(),
                  Line     :: non_neg_integer()}.

-type token()    :: {TokenTerm  :: term(),
                     TokenChars :: string(),
                     TokenStart :: point(),
                     TokenEnd   :: point()}.

-type option() :: {re_groups, numbered_only | named_only} |
                  re_anchored |
                  {re_anchored, boolean()} |
                  re_notempty |
                  {re_notempty, boolean()} |
                  debug |
                  {debug, boolean()} |
                  {debug_fun, fun((string(), [term()]) -> any())}.

-opaque match() :: {atom(), match_index()} | match_index().
-type  match_index() :: {integer, non_neg_integer()}.

%%%_* API ======================================================================

%%------------------------------------------------------------------------------
%% @doc Return the indices of match number Group.
%% @end
-spec match_group_index(Group :: non_neg_integer(),
                        Matches :: [match()]) ->
                           match_index().
%%------------------------------------------------------------------------------
match_group_index(Group, Matches) ->
  case Group + 1 > length(Matches) of
    true  -> erlang:error({no_such_group, {Group, Matches}});
    false -> lists:nth(Group + 1, Matches)
  end.


%%------------------------------------------------------------------------------
%% @doc Return the matching string of Group in String
%% @end
-spec match_group_string(String :: string(),
                         Group :: non_neg_integer(),
                         Matches :: [match()]) ->
                            match_index().
%%------------------------------------------------------------------------------
match_group_string(String, Group, Matches) ->
  case match_group_index(Group, Matches) of
    {-1,    _}   -> {error, nomatch};
    {Start, Len} -> {ok, string:substr(String, Start + 1, Len)}
  end.


%%------------------------------------------------------------------------------
%% @doc Return the indices of named group Group in Matches
%% @end
-spec match_named_group_index(Group :: non_neg_integer(),
                              Matches :: [match()]) ->
                                 match_index().
%%------------------------------------------------------------------------------
match_named_group_index(Group, Matches) ->
  case lists:keyfind(Group, 1, Matches) of
    false          -> erlang:error({no_such_group, {Group, Matches}});
    {Group, Index} -> Index
  end.

%%------------------------------------------------------------------------------
%% @doc Return the matching string of named group Group in String
%% @end
-spec match_named_group_string(String :: string(),
                         Group :: non_neg_integer(),
                         Matches :: [match()]) ->
                            match_index().
%%------------------------------------------------------------------------------
match_named_group_string(String, Group, Matches) ->
  case match_named_group_index(Group, Matches) of
    {-1,    _}   -> {error, nomatch};
    {Start, Len} -> {ok, string:substr(String, Start + 1, Len)}
  end.



%%------------------------------------------------------------------------------
%% @equiv string(String, Grammar, []).
%% @end
-spec string(String :: string(), Grammar :: grammar()) ->
                {ok, [token()]} |
                {error, term()}.
%%------------------------------------------------------------------------------
string(String, Grammar) ->
  string(String, Grammar, []).

%%------------------------------------------------------------------------------
%% @doc
%% Scans String and returns a resulting list of tokens according to
%% Grammar.
%% @end
-spec string(String :: string(), Grammar :: grammar(), Opts :: [option()]) ->
                {ok, [token()]} |
                {error, term()}.
%%------------------------------------------------------------------------------
string(String, Grammar, Opts0) ->
  Opts = expand_opts(Opts0),
  debug("Options are ~p", [Opts], Opts),
  CompiledGrammar = compile_grammar(Grammar, Opts),
  scan_string(String, CompiledGrammar, elx:point(), Opts, []).


%%%_* Internal functions =======================================================

debug(Fmt, Args, Opts) ->
  case lists:keyfind(debug, 1, Opts) of
    {debug, false} -> ok;
    {debug, true}  ->
      {debug_fun, Fun} = lists:keyfind(debug_fun, 1, Opts),
      Fun(Fmt, Args)
  end.

expand_opts(Opts) ->
  expand_opts(Opts, default_opts()).

expand_opts(Opts0, DefaultOpts) ->
  Opts = lists:map(fun({_, _} = Opt) -> Opt;
                      (Opt)          -> {Opt, true}
                   end,
                   Opts0),
  assert_opts(Opts),
  lists:ukeymerge(1,
                  lists:ukeysort(1, Opts),
                  lists:ukeysort(1, DefaultOpts)).

assert_opts(Opts) ->
  Defaults = default_opts(),
  Filter = fun({K, _V}) -> not lists:keymember(K, 1, Defaults) end,
  Illegal = lists:filter(Filter, Opts),
  case Illegal of
    [] -> ok;
    _  -> erlang:error({illegal_options, [K || {K, _V} <- Illegal]})
  end.

default_opts() ->
  [{debug,        false},
   {debug_fun,    fun(Fmt, Args) -> io:format(Fmt, Args) end},
   {re_groups,    numbered_only},
   {re_anchored,  true},
   {re_notempty,  true}
  ].


scan_string([],     _Grammar, _Offset, _Opts, Tokens) ->
  {ok, lists:reverse(Tokens)};
scan_string(String,  Grammar,  Offset, Opts, Tokens) ->
  debug("Scanning token, point is at ~p", [Offset], Opts),
  case next_token(String, Grammar, Offset, Opts) of
    {ok, {NewTokens, MatchEnd, Rest}} ->
      debug("Found tokens ~p", [NewTokens], Opts),
      scan_string(Rest, Grammar, MatchEnd, Opts, NewTokens ++ Tokens);
    {error, _} = Err ->
      Err
  end.

next_token(String, Grammar, Offset, Opts) ->
  case match_action(String, Grammar, Opts) of
    {ok, {{MatchStr, MatchGroups, Action}, Rest}} ->
      MatchEnd = elx:point_shift(Offset, MatchStr),
      case Action(MatchStr, MatchGroups, Offset, MatchEnd) of
        {error, Rsn}    -> {error, {Rsn, {Offset, String}}};
        {ok,    Tokens} -> {ok,    {Tokens, MatchEnd, Rest}}
      end;
    {error, nomatch} ->
      {error, {syntax_error, {Offset, String}}}
  end.

match_action(String, Rules, Opts) ->
  case match_action(String, Rules, Opts, nomatch, 0) of
    {nomatch, 0}   -> {error, nomatch};
    {Match,   Len} -> {ok, {Match, string:substr(String, Len + 1)}}
  end.

match_action(_String, [], _Opts, BestMatch, BestLen) ->
  {BestMatch, BestLen};
match_action(String, [{Pattern, Re, Action}|Rules], Opts, BestMatch, BestLen) ->
  debug("Matching against ~p", [Pattern], Opts),
  GroupNames = re_group_names(Re),
  debug("Pattern group names: ~p", [GroupNames], Opts),
  ReOpts = re_run_opts(Opts, GroupNames),
  debug("re:run options: ~p", [ReOpts], Opts),
  case re:run(String, Re, ReOpts) of
    {match, [{0, MatchLen}|MatchT] = AllMatches} when MatchLen > BestLen ->
      MatchStr = string:substr(String, 1, MatchLen),
      debug("Matched string: ~p", [MatchStr], Opts),
      MatchGroups =
        case lists:keyfind(re_groups, 1, Opts) of
          {re_groups, numbered_only} -> AllMatches;
          {re_groups, named_only}    -> lists:zip(GroupNames, MatchT)
        end,
      debug("Match groups ~p", [MatchGroups], Opts),
      Match = {MatchStr, MatchGroups, Action},
      match_action(String, Rules, Opts, Match, MatchLen);
    {match, [{0, MatchLen}|_]} ->
      debug("Matched string: ~p, but it's not the longest match",
            [string:substr(String, 1, MatchLen)], Opts),
      match_action(String, Rules, Opts, BestMatch, BestLen);
    nomatch ->
      debug("No match", [], Opts),
      match_action(String, Rules, Opts, BestMatch, BestLen)
  end.

re_run_opts(Opts, GroupNames) ->
  lists:foldl(fun(Opt, ReOpts) -> re_run_opts(Opt, GroupNames, ReOpts) end,
             [],
             Opts).

re_run_opts({re_anchored, Anchored}, _GroupNames, ReOpts) ->
  case Anchored of
    true  -> [anchored|ReOpts];
    false -> ReOpts
  end;
re_run_opts({re_notempty, NotEmpty}, _GroupNames, ReOpts) ->
  case NotEmpty of
    true  -> [notempty|ReOpts];
    false -> ReOpts
  end;
re_run_opts({re_groups, Groups}, GroupNames, ReOpts) ->
  Capture = case Groups of
              named_only    -> {capture, [0|GroupNames]};
              numbered_only -> {capture, all}
            end,
  [Capture|ReOpts];
re_run_opts(_, _GroupNames, ReOpts) ->
  ReOpts.

re_group_names(Pattern) ->
  {namelist, Names0} = re:inspect(Pattern, namelist),
  [list_to_atom(binary_to_list(N)) || N <- Names0].

compile_grammar(Grammar, Opts) ->
  debug("Compiling Grammar ~p", [Grammar], Opts),
  F = fun(Rule, Acc) -> [compile_grammar_rule(Rule, Opts)|Acc] end,
  lists:reverse(lists:foldl(F, [], Grammar)).

compile_grammar_rule({{Pattern, PatternOpts}, Action}, Opts) ->
  {CombinedPattern, Re} = compile_pattern(Pattern, PatternOpts, Opts),
  {CombinedPattern, Re, Action};
compile_grammar_rule({Pattern, Action}, Opts) ->
  {CombinedPattern, Re} = compile_pattern(Pattern, [], Opts),
  {CombinedPattern, Re, Action}.

compile_pattern([[_|_]|_] = Patterns, PatternOpts, Opts) ->
  Pattern = "(?:" ++ string:join(Patterns, ")|(?:") ++ ")",
  debug("Combining Patterns ~p", [Patterns], Opts),
  debug("Combined Pattern ~p", [Pattern], Opts),
  compile_pattern(Pattern, PatternOpts, Opts);
compile_pattern(Pattern, PatternOpts, Opts) ->
  debug("Compiling Pattern ~p, with options ~p", [Pattern, PatternOpts], Opts),
  case re:compile(Pattern, PatternOpts) of
    {ok, RE}     -> {Pattern, RE};
    {error, Rsn} -> erlang:error(Rsn)
  end.

%%%_* Tests ====================================================================

longest_match_test_() ->
  {setup,
   fun() ->
       [{"a", dummy_token(0)},
        {"aa", dummy_token(2)},
        {"a*", dummy_token(1)}]
   end,
   fun(Grammar) ->
       [?_assertEqual([elx:token(dummy, aaa_1, "aaa", {1, 1, 1}, {4, 1, 4})],
                      begin
                        {ok, Tokens} = string("aaa", Grammar),
                        Tokens
                      end),
        ?_assertEqual([elx:token(dummy, aa_2, "aa", {1, 1, 1}, {3, 1, 3})],
                      begin
                        {ok, Tokens} = string("aa", Grammar),
                        Tokens
                      end)
       ]
   end}.


multi_pattern_test_() ->
  {setup,
   fun() ->
       [{{["foo", "bar"], [dotall]}, keyword_token()}]
   end,
   fun(Grammar) ->
       [?_assertEqual([elx:token(keyword, foo, "foo", {1, 1, 1}, {4, 1, 4})],
                      begin
                        {ok, Tokens} = string("foo", Grammar),
                        Tokens
                      end),
        ?_assertEqual([elx:token(keyword, bar, "bar", {1, 1, 1}, {4, 1, 4})],
                      begin
                        {ok, Tokens} = string("bar", Grammar),
                        Tokens
                      end)
       ]
   end}.

compile_pattern_test_() ->
  {setup,
   fun() ->
       Pattern = "(?:a)|(?:b)",
       {ok, Re} = re:compile(Pattern),
       {Pattern, Re}
   end,
   fun({Pattern, Re}) ->
       [?_assertEqual({Pattern, Re},
                      compile_pattern(["a", "b"], [], default_opts())),
       ?_assertError(_,
                     compile_pattern("(", [], default_opts()))
       ]
   end}.


string_test_() ->
  {setup,
   fun() ->
       [{"\\s*",    skip()},
        {{"\\\"\(.*\\\\\\\"\)*.*\\\"", [dotall]}, dummy_token(0)},
        {"[0-9]*", dummy_token(1)},
        {"[a-z]*", dummy_token(2)},
        {"[A-Z]*", skip()}]
   end,
   fun(Grammar) ->
       [
        ?_assertEqual([elx:token(dummy, foo_2, "foo", {1, 1, 1}, {4, 1, 4})],
                      begin
                        {ok, Tokens} = string("foo", Grammar),
                        Tokens
                      end),
        ?_assertEqual([elx:token(dummy, foo_2,  "foo", {1, 1, 1}, {4, 1, 4}),
                       elx:token(dummy, '12_1', "12",  {5, 1, 5}, {7, 1, 7})],
                      begin
                        {ok, Tokens} = string("foo 12", Grammar),
                        Tokens
                      end),
        ?_assertEqual([elx:token(dummy, foo_2, "foo", {5, 1, 5}, {8, 1, 8})],
                      begin
                        {ok, Tokens} = string("FOO foo", Grammar),
                        Tokens
                      end),
        ?_assertEqual({ok, []},
                      string("FOO", Grammar))
       ]
   end}.

re_run_opts_test_() ->
  [?_assertEqual([], re_run_opts([], [group_1])),
   ?_assertEqual([], re_run_opts([], [group_1])),

   ?_assertEqual([anchored], re_run_opts([{re_anchored, true}],
                                         [group_1])),
   ?_assertEqual([], re_run_opts([{re_anchored, false}],
                                 [group_1])),

   ?_assertEqual([notempty], re_run_opts([{re_notempty, true}],
                                         [group_1])),
   ?_assertEqual([], re_run_opts([{re_notempty, false}],
                                 [group_1])),

   ?_assertEqual([{capture, all}],
                 re_run_opts([{re_groups, numbered_only}],
                             [group_1])),

   ?_assertEqual([{capture, [0, group_1]}],
                 re_run_opts([{re_groups, named_only}],
                             [group_1])),

   ?_assertEqual([notempty, anchored, {capture, [0, group_1]}],
                 re_run_opts([{re_groups, named_only},
                              {re_anchored, true},
                              {re_notempty, true}],
                             [group_1]))].


string_newline_test_() ->
  {setup,
   fun() ->
       [{"\n", skip()},
        {{"\\\"\(.*\\\\\\\"\)*.*\\\"", [dotall]}, dummy_token(0)},
        {"[0-9]*", dummy_token(1)},
        {"[a-z]*", dummy_token(2)},
        {"[A-Z]*", skip()}
       ]
   end,
   fun(Grammar) ->
       [
        ?_assertEqual([elx:token(dummy, foo_2, "foo", {1, 1, 1}, {4, 1, 4})],
                      begin
                        {ok, Tokens} = string("foo", Grammar),
                        Tokens
                      end),
        ?_assertEqual([elx:token(dummy, foo_2, "foo", {5, 2, 1}, {8, 2, 4})],
                      begin
                        {ok, Tokens} = string("FOO\nfoo", Grammar),
                        Tokens
                      end),
        ?_assertEqual({ok, []},
                      string("FOO\n", Grammar)),
        ?_assertEqual({error, {syntax_error, {{1, 1, 1}, "@"}}},
                      string("@", Grammar))
       ]
   end}.


next_token_test_() ->
  {setup,
   fun() ->
       Grammar1 =
         compile_grammar(
           [{"\\\"\(.*\\\\\\\"\)*.*\\\"", dummy_token(0)},
            {"[0-9]*",                    dummy_token(1)},
            {"[a-z]*",                    skip()},
            {"@*",                        something_illegal()}],
           default_opts()),
       Grammar2 =
         compile_grammar([{"foo", dummy_token(a)}], default_opts()),
       {Grammar1, Grammar2}
   end,
   fun({Grammar1, Grammar2})->
       [
        ?_assertMatch({ok, {[], _, _}},
                      next_token("foo", Grammar1, elx:point(), default_opts())),
        ?_assertEqual({"123", "\nbar"},
                      test_chars(next_token("123\nbar",
                                            Grammar1,
                                            elx:point(),
                                            default_opts()))),
        ?_assertMatch({"\"foo\"", ""},
                      test_chars(next_token("\"foo\"",
                                            Grammar1,
                                            elx:point(),
                                            default_opts()))),
        ?_assertEqual({error, {{something_illegal, "@"}, {{1, 1, 1}, "@"}}},
                      next_token("@", Grammar1, elx:point(), default_opts())),
        ?_assertEqual({error, {syntax_error, {{1, 1, 1}, "Foo"}}},
                      next_token("Foo", Grammar1, elx:point(), default_opts())),
        ?_assertError(badarg,
                      next_token("foo", Grammar2, elx:point(), default_opts()))
       ]
   end}.

match_action_empty_string_test_() ->
  [?_assertEqual({error, nomatch},
                 match_action("",
                              compile_grammar([{"", dummy_token(1)}],
                                              default_opts()),
                              default_opts())),
   ?_assertEqual({error, nomatch},
                 match_action("",
                              compile_grammar([{".*", dummy_token(1)}],
                                              default_opts()),
                              default_opts()))].

match_action_one_rule_test_() ->
  [?_assertEqual({ok, {{"foo", [{0, 3}], dummy_token()}, " b"}},
                 match_action("foo b",
                              compile_grammar([{"foo", dummy_token()}],
                                              default_opts()),
                              default_opts())),
   ?_assertEqual({error, nomatch},
                 match_action("foo",
                              compile_grammar([], default_opts()),
                              default_opts())),
   ?_assertEqual({error, nomatch},
                 match_action("foo",
                              compile_grammar([{"bar", dummy_token()}],
                                              default_opts()),
                              default_opts())),
   ?_assertEqual({error, nomatch},
                 match_action("foo",
                              compile_grammar([{"bfoo", dummy_token()}],
                                              default_opts()),
                              default_opts()))].

match_action_regexp_test_() ->
  [?_assertEqual({ok, {{"foo", [{0, 3}], dummy_token(1)}, ""}},
                 match_action("foo",
                              compile_grammar([{"bar", dummy_token(0)},
                                               {"foo", dummy_token(1)}],
                                              default_opts()),
                              default_opts())),
   ?_assertEqual({ok, {{"foo", [{0, 3}], dummy_token(1)}, ""}},
                 match_action("foo",
                              compile_grammar([{"bar", dummy_token(0)},
                                               {".*", dummy_token(1)}],
                                              default_opts()),
                              default_opts())),
   ?_assertEqual({ok, {{"foo", [{group_1, {0, 3}}], dummy_token(0)}, ""}},
                 match_action("foo",
                              compile_grammar([{"(?<group_1>foo)",
                                                dummy_token(0)}],
                                             default_opts()),
                              expand_opts([{re_groups, named_only}])))
  ].

expand_opts_test_() ->
  [?_assertEqual([{re_anchored, true}], expand_opts([re_anchored], [])),
   ?_assertError({illegal_options, [foo]}, expand_opts([foo]))
  ].

assert_opts_test_() ->
  [?_assertEqual(ok, assert_opts([{re_anchored, true}])),
   ?_assertError({illegal_options, [foo, baz]},
                 assert_opts([{foo, bar}, {baz,  bam}]))
  ].

match_group_index_test_() ->
  {setup,
   fun() ->
       [{0, 1}, {1, 1}]
   end,
   fun(Matches) ->
       [?_assertEqual({1, 1}, match_group_index(1, Matches)),
        ?_assertError({no_such_group, {2, Matches}},
                      match_group_index(2, Matches))
       ]
   end}.

match_group_string_test_() ->
  {setup,
   fun() ->
       [{-1, 0}, {1, 1}]
   end,
   fun(Matches) ->
       [?_assertEqual({ok, "o"}, match_group_string("Foo", 1, Matches)),
        ?_assertEqual({error, nomatch}, match_group_string("Foo", 0, Matches)),
        ?_assertError({no_such_group, {2, Matches}},
                      match_group_string("Foo", 2, Matches))
       ]
   end}.

match_named_group_index_test_() ->
  {setup,
   fun() ->
       [{group_0,    {0, 1}},
        {subgroup_a, {-1, 0}},
        {group_1,     {1, 1}}]
   end,
   fun(Matches) ->
       [?_assertEqual({1, 1},
                      match_named_group_index(group_1, Matches)),
        ?_assertError({no_such_group, {group_3, Matches}},
                      match_named_group_index(group_3, Matches))
       ]
   end}.

match_named_group_string_test_() ->
  {setup,
   fun() ->
       [{group_0,    {0, 1}},
        {subgroup_a, {-1, 0}},
        {group_1,     {1, 1}}]
   end,
   fun(Matches) ->
       [?_assertEqual({ok, "o"},
                      match_named_group_string("Foo", group_1, Matches)),
        ?_assertEqual({error, nomatch},
                      match_named_group_string("Foo", subgroup_a, Matches)),
        ?_assertError({no_such_group, {group_3, Matches}},
                      match_named_group_string("Foo", group_3, Matches))
       ]
   end}.


debug_test() ->
  ?assertEqual(ok, debug("Foo ~p", [bar], [{debug, true}|default_opts()])).

%%%_* Test helpers =============================================================

test_chars({ok, {[Token], _MatchEnd, Rest}}) ->
  {elx:token_symbol(Token), Rest}.

dummy_token() ->
  dummy_token(0).

dummy_token(I) ->
  fun(Chars, _Matches, Start, End) ->
      TokenTerm = list_to_atom(Chars ++ "_" ++ integer_to_list(I)),
      {ok, [elx:token(dummy, TokenTerm, Chars, Start, End)]}
  end.

keyword_token() ->
  fun(Chars, _Matches, Start, End) ->
      {ok, [elx:token(keyword, list_to_atom(Chars), Chars, Start, End)]}
  end.


skip() ->
  fun(_Chars, _Matches, _Start, _End) ->
      {ok, []}
  end.

something_illegal() ->
  fun(Chars, _Matches, __Start, _End) ->
      {error, {something_illegal, Chars}} end.

%%%_* Emacs ====================================================================
%%% Local Variables:
%%% allout-layout: t
%%% erlang-indent-level: 2
%%% End:
