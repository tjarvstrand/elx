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
-module(elx).

%%%_* Exports ==================================================================
-export([token/5,
         token_chars/1,
         token_end/1,
         point/0,
         point/3,
         point_incr/4,
         point_shift/2]).

-export_type([point/0,
              token/0]).

%%%_* Includes =================================================================

-include_lib("eunit/include/eunit.hrl").

%%%_* Defines ==================================================================

%%%_* Types ====================================================================

-type point() :: {Position :: non_neg_integer(),
                  Column   :: non_neg_integer(),
                  Line     :: non_neg_integer()}.

-type token()    :: {TokenTerm  :: term(),
                     TokenChars :: string(),
                     TokenStart :: point(),
                     TokenEnd   :: point()}.

%%%_* API ======================================================================

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



point_incr({Pos, Line, Col}, IncrPos, 0, IncrCol) ->
    {Pos + IncrPos, Line, Col + IncrCol};
point_incr({Pos, Line, _Col}, IncrPos, IncrLine, IncrCol) ->
    {Pos + IncrPos, Line + IncrLine, IncrCol + 1}.

%%%_* Tests ====================================================================

%%%_* Test helpers =============================================================

%%%_* Emacs ====================================================================
%%% Local Variables:
%%% allout-layout: t
%%% erlang-indent-level: 2
%%% End:
