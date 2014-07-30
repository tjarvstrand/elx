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
-export([set_token_chars/2,
         set_token_children/2,
         set_token_end/2,
         set_token_meta/2,
         set_token_start/2,
         set_token_type/2,
         set_token_value/2,
         token/0,
         token/3,
         token/4,
         token/5,
         token/6,
         token/7,
         token_chars/1,
         token_children/1,
         token_end/1,
         token_meta/1,
         token_start/1,
         token_type/1,
         token_value/1,
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
                type           :: term(),
                chars          :: string(),
                start          :: point(),
                'end'          :: point(),
                children  = [] :: [token()],
                meta           :: term() % For use by the grammar author
               }).

%%%_* Types ====================================================================

%% A point is between two characters in a file. Points are 1-based so the first
%% point (1,1,1) is before the first characbter, the second (usually 2,1,2)
%% unless the first character is a newline) is after the first character,
%% (3,1,3) is after the last etc.
-type point() :: {Position :: pos_integer(),
                  Column   :: pos_integer(),
                  Line     :: pos_integer()}.


%% The token start point is the point() just before its first character and the
%% end point is the point() just after its last character.
-type token() :: #token{}.

%%%_* API ======================================================================

%%------------------------------------------------------------------------------
%% @equiv token(undefined, undefined, []).
-spec token() -> token().
%%------------------------------------------------------------------------------
token() ->
    token(undefined, undefined, []).

%%------------------------------------------------------------------------------
%% @equiv token(Type, Value, Chars, point()).
-spec token(Type     :: term(),
            Value    :: term(),
            Chars    :: string()) -> token().
%%------------------------------------------------------------------------------
token(Type, Value, Chars) ->
    token(Type, Value, Chars, point()).

%%------------------------------------------------------------------------------
%% @equiv token(Type, Value, Chars, Point, point_shift(Point, Chars)).
-spec token(Type     :: term(),
            Value    :: term(),
            Chars    :: string(),
            Start    :: point()) -> token().
%%------------------------------------------------------------------------------
token(Type, Value, Chars, Start) ->
    token(Type, Value, Chars, Start, point_shift(Start, Chars)).

%%------------------------------------------------------------------------------
%% @equiv token(Type, Value, Chars, Start, End, []).
-spec token(Type     :: term(),
            Value    :: term(),
            Chars    :: string(),
            Start    :: point(),
            End      :: point()) -> token().
%%------------------------------------------------------------------------------
token(Type, Value, Chars, Start, End) ->
    token(Type, Value, Chars, Start, End, []).

%%------------------------------------------------------------------------------
%% @equiv token(Type, Value, Chars, Start, End, Children, []).
-spec token(Type     :: term(),
            Value    :: term(),
            Chars    :: string(),
            Start    :: point(),
            End      :: point(),
            Children :: [token()]) -> token().
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
%% @doc Returns Token's string representation.
-spec token_chars(Token :: token()) -> string().
%%------------------------------------------------------------------------------
token_chars(Token) -> Token#token.chars.

%%------------------------------------------------------------------------------
%% @doc Returns the list Token's child tokens.
-spec token_children(Token :: token()) -> [token()].
%%------------------------------------------------------------------------------
token_children(Token) -> Token#token.children.

%%------------------------------------------------------------------------------
%% @doc Returns Token's end point.
-spec token_end(Token :: token()) -> point().
%%------------------------------------------------------------------------------
token_end(Token) -> Token#token.'end'.

%%------------------------------------------------------------------------------
%% @doc Returns Token's start point.
-spec token_start(Token :: token()) -> point().
%%------------------------------------------------------------------------------
token_start(Token) -> Token#token.start.

%%------------------------------------------------------------------------------
%% @doc Returns Token's semantic type.
-spec token_type(Token :: token()) -> term().
%%------------------------------------------------------------------------------
token_type(Token) -> Token#token.type.

%%------------------------------------------------------------------------------
%% @doc Returns Token's semantic value.
-spec token_value(Token :: token()) -> term().
%%------------------------------------------------------------------------------
token_value(Token) -> Token#token.value.

%%------------------------------------------------------------------------------
%% @doc Returns Token's metadata.
-spec token_meta(Token :: token()) -> term().
%%------------------------------------------------------------------------------
token_meta(Token) -> Token#token.meta.


%%------------------------------------------------------------------------------
%% @doc Returns Token's string representation.
-spec set_token_chars(Token :: token(), Chars :: string()) -> token().
%%------------------------------------------------------------------------------
set_token_chars(Token, Chars) -> Token#token{chars = Chars}.

%%------------------------------------------------------------------------------
%% @doc Returns the list Token's child tokens.
-spec set_token_children(Token :: token(), Children :: [token()]) -> token().
%%------------------------------------------------------------------------------
set_token_children(Token, Children) -> Token#token{children = Children}.

%%------------------------------------------------------------------------------
%% @doc Returns Token's end point.
-spec set_token_end(Token :: token(), End :: point()) -> token().
%%------------------------------------------------------------------------------
set_token_end(Token, End) -> Token#token{'end' = End}.

%%------------------------------------------------------------------------------
%% @doc Returns Token's start point.
-spec set_token_start(Token :: token(), Start :: point()) -> token().
%%------------------------------------------------------------------------------
set_token_start(Token, Start) -> Token#token{start = Start}.

%%------------------------------------------------------------------------------
%% @doc Returns Token's semantic type.
-spec set_token_type(Token :: token(), Type :: term()) -> token().
%%------------------------------------------------------------------------------
set_token_type(Token, Type) -> Token#token{type = Type}.

%%------------------------------------------------------------------------------
%% @doc Returns Token's semantic value.
-spec set_token_value(Token :: token(), Value :: term()) -> token().
%%------------------------------------------------------------------------------
set_token_value(Token, Value) -> Token#token{value = Value}.

%%------------------------------------------------------------------------------
%% @doc Returns Token's metadata.
-spec set_token_meta(Token :: token(), Meta :: term()) -> token().
%%------------------------------------------------------------------------------
set_token_meta(Token, Meta) -> Token#token{meta = Meta}.



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
        length(String),
        length(Lines) - 1,
        length(lists:last(Lines))).



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
