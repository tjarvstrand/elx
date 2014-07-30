%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%% @doc ELX primary interface.
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
         token/6,
         token/7,
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

-record(token, {value          :: term(),
                type           :: atom(),
                chars          :: string(),
                start          :: point(),
                'end'          :: point(),
                children  = [] :: [token()],
                meta           :: term() % For use by the grammar author
               }).

%%%_* Types ====================================================================

-type point() :: {Position :: pos_integer(),
                  Column   :: pos_integer(),
                  Line     :: pos_integer()}.

-type token() :: #token{}.

%%%_* API ======================================================================

%%------------------------------------------------------------------------------
%% @equiv token(Type, Value, Chars, Start, End, []).
%%------------------------------------------------------------------------------
token(Type, Value, Chars, Start, End) ->
    token(Type, Value, Chars, Start, End, []).

%%------------------------------------------------------------------------------
%% @equiv token(Type, Value, Chars, Start, End, Children, []).
%%------------------------------------------------------------------------------
token(Type, Value, Chars, Start, End, Children) ->
    token(Type, Value, Chars, Start, End, Children, []).

%%------------------------------------------------------------------------------
%% @doc Returns a new token.
-spec token(Type     :: term(),
            Value    :: term(),
            Chars    :: string(),
            Start    :: point(),
            End      :: point(),
            Children :: [token()],
            Meta     :: term()) -> token().
%%------------------------------------------------------------------------------
token(Type, Value, Chars, Start, End, Children, Meta) ->
    #token{chars = Chars,
           type = Type,
           value = Value,
           start = Start,
           'end' = End,
           children = Children,
           meta = Meta
          }.

%%------------------------------------------------------------------------------
%% @doc Returns Token's string representation
-spec token_chars(Token :: token()) -> string().
%%------------------------------------------------------------------------------
token_chars(Token) -> Token#token.chars.

%%------------------------------------------------------------------------------
%% @doc Returns Token's end point
-spec token_end(Token :: token()) -> point().
%%------------------------------------------------------------------------------
token_end(Token) -> Token#token.'end'.

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
