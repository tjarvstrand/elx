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


%%%_* API ======================================================================

%%------------------------------------------------------------------------------
%% @doc
%% Scans String and returns a resulting list of tokens according to
%% Grammar.
%% @end
-spec string(String :: string(), Grammar :: grammar()) ->
                {ok, [token()]} |
                {error, term()}.
%%------------------------------------------------------------------------------
string(String, Grammar) ->
  scan_string(String, compile_grammar(Grammar), point(), []).

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

point_shift(Point, String) ->
  Lines = re:split(String, "\\R", [bsr_unicode, {return, list}]),
  point_incr(Point,
        length(String) - 1,
        length(Lines) - 1,
        length(lists:last(Lines)) - 1).


scan_string([],     _Grammar, _Offset, Tokens) -> {ok, lists:reverse(Tokens)};
scan_string(String,  Grammar,  Offset, Tokens) ->
  case next_token(String, Grammar, Offset) of
    {{Res, Token}, Rest} when Res =:= token ->
      NextPoint = point_incr(token_end(Token), 1, 0, 1),
      scan_string(Rest, Grammar, NextPoint, [Token|Tokens]);
    {{skip, Token}, Rest} ->
      NextPoint = point_incr(token_end(Token), 1, 0, 1),
      scan_string(Rest, Grammar, NextPoint, Tokens);
    {error, nomatch} ->
      {error, {syntax_error, {Offset, String}}}
  end.


next_token(String, Grammar, Offset) ->
  case match_action(String, Grammar) of
    {ok, {MatchStr, Matches, Rest, Action}} ->
      End = point_shift(Offset, MatchStr),
      try   {Action(MatchStr, Matches, Offset, End), Rest}
      catch error:E -> {error, E}
      end;
    {error, nomatch} = Err -> Err
  end.


match_action(_String, []) ->
  {error, nomatch};
match_action(String, [{Pattern, Action}|Rules]) ->
  case re:run(String, Pattern, [anchored, notempty, {capture, all}]) of
    {match, [{0, MatchLen}|_] = Matches} ->
      {MatchStr, Rest} = lists:split(MatchLen, String),
      {ok, {MatchStr, Matches, Rest, Action}};
    nomatch -> match_action(String, Rules)
  end.


compile_grammar(Grammar) ->
  F = fun(Rule, Acc) -> [compile_grammar_rule(Rule)|Acc] end,
  lists:reverse(lists:foldl(F, [], Grammar)).


compile_grammar_rule({{Pattern, Options}, Action}) ->
  {compile_pattern(Pattern, Options), Action};
compile_grammar_rule({Pattern, Action}) ->
  {compile_pattern(Pattern, []), Action}.

compile_pattern([[_|_]|_] = Patterns, Options) ->
  Pattern = "\(?:" ++ string:join(Patterns, "\)\|\(?:") ++ "\)",
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
         [{"\\\"\(.*\\\\\\\"\)*.*\\\"", dummy_token(0)},
          {"[0-9]*", dummy_token(1)},
          {"[a-z]*", skip()}]
   end,
   fun(Grammar)->
       [
        ?_assertMatch({{skip, _}, _},
                      next_token("foo", Grammar, point())),
        ?_assertEqual({"123", "\nbar"},
                      test_chars(next_token("123\nbar", Grammar, point()))),
        ?_assertMatch({"\"foo\"", ""},
                      test_chars(next_token("\"foo\"", Grammar, point()))),
        ?_assertEqual({error, badarg},
                      next_token("foo", [{"foo", dummy_token(a)}], point())),
        ?_assertEqual({error, nomatch},
                      next_token("foo", [{"foao", dummy_token(a)}], point()))
       ]
   end}.

match_action_empty_string_test_() ->
  [?_assertEqual({error, nomatch},
                 match_action("", [{"", dummy_token(1)}])),
   ?_assertEqual({error, nomatch},
                 match_action("", [{".*", dummy_token(1)}]))].

match_action_one_rule_test_() ->
  [?_assertEqual({ok, {"foo", [{0, 3}], "b", dummy_token()}},
                 match_action("foob", [{"foo", dummy_token()}])),
   ?_assertEqual({error, nomatch},
                 match_action("foo", [])),
   ?_assertEqual({error, nomatch},
                 match_action("foo", [{"bar", dummy_token()}])),
   ?_assertEqual({error, nomatch},
                 match_action("foo", [{"bfoo", dummy_token()}]))].

match_action_regexp_test_() ->
  [?_assertEqual({ok, {"foo", [{0, 3}], "", dummy_token(1)}},
                 match_action("foo", [{"bar", dummy_token(0)},
                                      {"foo", dummy_token(1)}])),
   ?_assertEqual({ok, {"foo", [{0, 3}], "", dummy_token(1)}},
                 match_action("foo", [{"bar", dummy_token(0)},
                                      {".*", dummy_token(1)}]))
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



%%%_* Emacs ====================================================================
%%% Local Variables:
%%% allout-layout: t
%%% erlang-indent-level: 2
%%% End:
