%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%% @doc
%%% @end
%%% @author Thomas Järvstrand <tjarvstrand@gmail.com>
%%% @copyright
%%% Copyright 2012 Thomas Järvstrand <tjarvstrand@gmail.com>
%%%
%%% This file is part of parse_lib.
%%%
%%% parse_lib is free software: you can redistribute it and/or modify
%%% it under the terms of the GNU General Public License as published by
%%% the Free Software Foundation, either version 3 of the License, or
%%% (at your option) any later version.
%%%
%%% parse_lib is distributed in the hope that it will be useful,
%%% but WITHOUT ANY WARRANTY; without even the implied warranty of
%%% MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
%%% GNU General Public License for more details.
%%%
%%% You should have received a copy of the GNU General Public License
%%% along with parse_lib. If not, see <http://www.gnu.org/licenses/>.
%%% @end
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

%%%_* Module declaration =======================================================
-module(parse_lib_scan).

%%%_* Exports ==================================================================
-export([string/2,
         token/5,
         token_chars/1,
         point/0,
         point/3]).

-export_type([grammar/0,
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
                  notempty |
                  {re_notempty, boolean()}.

%%%_* API ======================================================================

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
string(String, Grammar, Opts) ->
  scan_string(String, compile_grammar(Grammar), point(), expand_opts(Opts), []).


%%------------------------------------------------------------------------------
%% @doc Returns a new token.
-spec token(Type  :: term(),
            Term  :: term(),
            Chars :: string(),
            Start :: point(),
            End   :: point()) -> token().
%%------------------------------------------------------------------------------
token(Type, Term, Chars, Start, End) ->
    {Type, Term, Chars, Start, End}.

%%------------------------------------------------------------------------------
%% @doc Returns Token's string representation
-spec token_chars(Token :: token()) -> string().
%%------------------------------------------------------------------------------
token_chars({_Type, _Term, Chars, _Start, _End}) -> Chars.

%%------------------------------------------------------------------------------
%% @doc Returns Token's end point
-spec token_end(Token :: token()) -> point().
%%------------------------------------------------------------------------------
token_end({_Type, _Term, _Chars, _Start, End}) -> End.

%%------------------------------------------------------------------------------
%% @equiv point(1, 1, 1).
-spec point() -> point().
%%------------------------------------------------------------------------------
point() ->
  point(1, 1, 1).

%%------------------------------------------------------------------------------
%% @doc Returns a new point.
-spec point(Pos  :: non_neg_integer(),
            Line :: non_neg_integer(),
            Col  :: non_neg_integer()) -> point().
%%------------------------------------------------------------------------------
point(Pos, Line, Col) ->
  {Pos, Line, Col}.

%%%_* Internal functions =======================================================

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
  [{re_groups,    numbered_only},
   {re_anchored,  true},
   {re_notempty,  true}
  ].

point_shift(Point, String) ->
  Lines = re:split(String, "\\R", [bsr_unicode, {return, list}]),
  point_incr(Point,
        length(String) - 1,
        length(Lines) - 1,
        length(lists:last(Lines)) - 1).


scan_string([],     _Grammar, _Offset, _Opts, Tokens) ->
  {ok, lists:reverse(Tokens)};
scan_string(String,  Grammar,  Offset, Opts, Tokens) ->
  case next_token(String, Grammar, Offset, Opts) of
    {{Res, Token}, Rest} when Res =:= token ->
      NextPoint = point_incr(token_end(Token), 1, 0, 1),
      scan_string(Rest, Grammar, NextPoint, Opts, [Token|Tokens]);
    {{skip, Token}, Rest} ->
      NextPoint = point_incr(token_end(Token), 1, 0, 1),
      scan_string(Rest, Grammar, NextPoint, Opts, Tokens);
    {error, _} = Err ->
      Err
  end.

next_token(String, Grammar, Offset) ->
  next_token(String, Grammar, Offset, default_opts()).

next_token(String, Grammar, Offset, Opts) ->
  case match_action(String, Grammar, Opts) of
    {ok, {MatchStr, Matches, Rest, Action}} ->
      End = point_shift(Offset, MatchStr),
      case Action(MatchStr, Matches, Offset, End) of
        {error, Rsn} -> {error, {Rsn, {Offset, String}}};
        Res          -> {Res, Rest}
      end;
    {error, nomatch} ->
      {error, {syntax_error, {Offset, String}}}
  end.

match_action(_String, Rules) ->
  match_action(_String, Rules, default_opts()).

match_action(_String, [], _Opts) ->
  {error, nomatch};
match_action(String, [{Pattern, Action}|Rules], Opts) ->
  GroupNames = re_group_names(Pattern),
  ReOpts = re_run_opts(Opts, GroupNames),
  case re:run(String, Pattern, ReOpts) of
    {match, [{0, MatchLen}|MatchT] = AllMatches} ->
      {MatchStr, Rest} = lists:split(MatchLen, String),
      MatchGroups =
        case lists:keyfind(re_groups, 1, Opts) of
          {re_groups, numbered_only} -> AllMatches;
          {re_groups, named_only}    -> lists:zip(GroupNames, MatchT)
        end,
      {ok, {MatchStr, MatchGroups , Rest, Action}};
    nomatch -> match_action(String, Rules, Opts)
  end.

re_run_opts(Opts, GroupNames) ->
  re_run_opts(Opts, GroupNames, []).

re_run_opts([], _GroupNames, ReOpts) ->
  lists:reverse(ReOpts);
re_run_opts([{re_anchored, Anchored}|Opts], GroupNames, ReOpts) ->
  case Anchored of
    true  -> re_run_opts(Opts, GroupNames, [anchored|ReOpts]);
    false -> re_run_opts(Opts, GroupNames, ReOpts)
  end;
re_run_opts([{re_notempty, NotEmpty}|Opts], GroupNames, ReOpts) ->
  case NotEmpty of
    true  -> re_run_opts(Opts, GroupNames, [notempty|ReOpts]);
    false -> re_run_opts(Opts, GroupNames, ReOpts)
  end;
re_run_opts([{re_groups, Groups}|Opts], GroupNames, ReOpts) ->
  Capture = case Groups of
              named_only    -> {capture, [0|GroupNames]};
              numbered_only -> {capture, all}
            end,
  re_run_opts(Opts, GroupNames, [Capture|ReOpts]).

re_group_names(Pattern) ->
  {namelist, Names0} = re:inspect(Pattern, namelist),
  [list_to_atom(binary_to_list(N)) || N <- Names0].

compile_grammar(Grammar) ->
  F = fun(Rule, Acc) -> [compile_grammar_rule(Rule)|Acc] end,
  lists:reverse(lists:foldl(F, [], Grammar)).

compile_grammar_rule({{Pattern, Options}, Action}) ->
  {compile_pattern(Pattern, Options), Action};
compile_grammar_rule({Pattern, Action}) ->
  {compile_pattern(Pattern, []), Action}.

compile_pattern([[_|_]|_] = Patterns, Options) ->
  Pattern = "(?:" ++ string:join(Patterns, ")|(?:") ++ ")",
  compile_pattern(Pattern, Options);
compile_pattern(Pattern, Options) ->
  case re:compile(Pattern ++ "(?:\\b|$)", Options) of
    {ok, RE}     -> RE;
    {error, Rsn} -> erlang:error(Rsn)
  end.

point_incr({Pos, Line, Col}, IncrPos, 0, IncrCol) ->
    {Pos + IncrPos, Line, Col + IncrCol};
point_incr({Pos, Line, _Col}, IncrPos, IncrLine, IncrCol) ->
    {Pos + IncrPos, Line + IncrLine, IncrCol + 1}.

%%%_* Tests ====================================================================

multi_pattern_test_() ->
  {setup,
   fun() ->
       [{{["foo", "bar"], [dotall]}, keyword_token()}]
   end,
   fun(Grammar) ->
       [?_assertEqual({ok, [{keyword, foo, "foo", {1, 1, 1}, {3, 1, 3}}]},
                      string("foo", Grammar)),
        ?_assertEqual({ok, [{keyword, bar, "bar", {1, 1, 1}, {3, 1, 3}}]},
                      string("bar", Grammar))
       ]
   end}.

compile_pattern_test_() ->
  [?_assertEqual(re:compile("(?:a)|(?:b)(?:\\b|$)"),
                 {ok, compile_pattern(["a", "b"], [])}),
   ?_assertError(_,
                 compile_pattern("(", []))
  ].


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
       [?_assertEqual({ok, [{dummy, foo_2, "foo", {1, 1, 1}, {3, 1, 3}}]},
                      string("foo", Grammar)),
        ?_assertEqual({ok, [{dummy, foo_2,  "foo", {1, 1, 1}, {3, 1, 3}},
                            {dummy, '12_1', "12",  {5, 1, 5}, {6, 1, 6}}]},
                      string("foo 12", Grammar)),
        ?_assertEqual({ok, [{dummy, foo_2, "foo", {5, 1, 5}, {7, 1, 7}}]},
                      string("FOO foo", Grammar)),
        ?_assertEqual({ok, []},
                      string("FOO", Grammar))
       ]
   end}.

re_run_opts_test_() ->
  [?_assertEqual([], re_run_opts([], [group_1])),
   ?_assertEqual([], re_run_opts([], [group_1])),

   ?_assertEqual([anchored], re_run_opts([{re_anchored, true}], [group_1])),
   ?_assertEqual([], re_run_opts([{re_anchored, false}], [group_1])),

   ?_assertEqual([notempty], re_run_opts([{re_notempty, true}], [group_1])),
   ?_assertEqual([], re_run_opts([{re_notempty, false}], [group_1])),

   ?_assertEqual([{capture, all}],
                 re_run_opts([{re_groups, numbered_only}], [group_1])),

   ?_assertEqual([{capture, [0, group_1]}],
                 re_run_opts([{re_groups, named_only}], [group_1])),

   ?_assertEqual([{capture, [0, group_1]}, anchored, notempty],
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
        ?_assertEqual({ok, [{dummy, foo_2, "foo", {1, 1, 1}, {3, 1, 3}}]},
                      string("foo", Grammar)),
        ?_assertEqual({ok, [{dummy, foo_2, "foo", {5, 2, 1}, {7, 2, 3}}]},
                      string("FOO\nfoo", Grammar)),
        ?_assertEqual({ok, []},
                      string("FOO\n", Grammar)),
        ?_assertEqual({error, {syntax_error, {{1, 1, 1}, "@"}}},
                      string("@", Grammar))
       ]
   end}.


next_token_test_() ->
  {setup,
   fun() ->
       compile_grammar(
         [{"\\\"\(.*\\\\\\\"\)*.*\\\"", dummy_token(0)},
          {"[0-9]*",                    dummy_token(1)},
          {"[a-z]*",                    skip()},
          {"@*",                        something_illegal()}])
   end,
   fun(Grammar)->
       [
        ?_assertMatch({{skip, _}, _},
                      next_token("foo", Grammar, point())),
        ?_assertEqual({"123", "\nbar"},
                      test_chars(next_token("123\nbar", Grammar, point()))),
        ?_assertMatch({"\"foo\"", ""},
                      test_chars(next_token("\"foo\"", Grammar, point()))),
        ?_assertEqual({error, {{something_illegal, "@"}, {{1, 1, 1}, "@"}}},
                      next_token("@", Grammar, point())),
        ?_assertEqual({error, {syntax_error, {{1, 1, 1}, "Foo"}}},
                      next_token("Foo", Grammar, point())),
        ?_assertError(badarg,
                      next_token("foo", [{"foo", dummy_token(a)}], point()))
       ]
   end}.

match_action_empty_string_test_() ->
  [?_assertEqual({error, nomatch},
                 match_action("", compile_grammar([{"", dummy_token(1)}]))),
   ?_assertEqual({error, nomatch},
                 match_action("", compile_grammar([{".*", dummy_token(1)}])))].

match_action_one_rule_test_() ->
  [?_assertEqual({ok, {"foo", [{0, 3}], " b", dummy_token()}},
                 match_action("foo b",
                              compile_grammar([{"foo", dummy_token()}]))),
   ?_assertEqual({error, nomatch},
                 match_action("foo", compile_grammar([]))),
   ?_assertEqual({error, nomatch},
                 match_action("foo",
                              compile_grammar([{"bar", dummy_token()}]))),
   ?_assertEqual({error, nomatch},
                 match_action("foo",
                              compile_grammar([{"bfoo", dummy_token()}])))].

match_action_regexp_test_() ->
  [?_assertEqual({ok, {"foo", [{0, 3}], "", dummy_token(1)}},
                 match_action("foo",
                              compile_grammar([{"bar", dummy_token(0)},
                                               {"foo", dummy_token(1)}]))),
   ?_assertEqual({ok, {"foo", [{0, 3}], "", dummy_token(1)}},
                 match_action("foo",
                              compile_grammar([{"bar", dummy_token(0)},
                                               {".*", dummy_token(1)}]))),
   ?_assertEqual({ok, {"foo", [{group_1, {0, 3}}], "", dummy_token(0)}},
                 match_action("foo",
                              compile_grammar([{"(?<group_1>foo)",
                                                dummy_token(0)}]),
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


%%%_* Test helpers =============================================================

test_chars({{token, Token}, Rest}) ->
  {token_chars(Token), Rest}.

dummy_token() ->
  dummy_token(0).

dummy_token(I) ->
  fun(Chars, _Matches, Start, End) ->
      TokenTerm = list_to_atom(Chars ++ "_" ++ integer_to_list(I)),
      {token, token(dummy, TokenTerm, Chars, Start, End)}
  end.

keyword_token() ->
  fun(Chars, _Matches, Start, End) ->
      {token, token(keyword, list_to_atom(Chars), Chars, Start, End)}
  end.


skip() ->
  fun(Chars, _Matches, Start, End) ->
      {skip, token(dummy, Chars, Chars, Start, End)} end.

something_illegal() ->
  fun(Chars, _Matches, __Start, _End) ->
      {error, {something_illegal, Chars}} end.

%%%_* Emacs ====================================================================
%%% Local Variables:
%%% allout-layout: t
%%% erlang-indent-level: 2
%%% End:
