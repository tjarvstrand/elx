%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%% @doc Precedence related tests.
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
-module(elx_precedence_tests).

%%%_* Exports ==================================================================

%%%_* Includes =================================================================
-include_lib("eunit/include/eunit.hrl").

%%%_* Defines ==================================================================

%%%_* Tests ====================================================================

basic_test_() ->
  {setup,
   fun() ->
           elx_grammar:new([{'E', ['E', "+", 'E']},
                            {'E', ["1"]}],
                           ['E'],
                           [])
   end,
   fun(Grammar) ->
       [?_assertEqual({ok, [elx:token('E',
                                      1,
                                      'E',
                                      undefined,
                                      undefined,
                                      [elx:token('E',
                                                 1,
                                                 'E',
                                                 undefined,
                                                 undefined,
                                                 [elx:token('E',
                                                            1,
                                                            'E',
                                                            undefined,
                                                            undefined,
                                                            [elx:token(integer,
                                                                       1,
                                                                       "1")]),
                                                  elx:token(op,
                                                            '+',
                                                            "+",
                                                            undefined,
                                                            undefined,
                                                            []),
                                                  elx:token('E',
                                                            1,
                                                            'E',
                                                            undefined,
                                                            undefined,
                                                            [elx:token(integer,
                                                                       1,
                                                                       "1")])]),
                                      elx:token(op,
                                                '+',
                                                "+",
                                                undefined,
                                                undefined,
                                                []),
                                      elx:token('E',
                                                1,
                                               'E',
                                                undefined,
                                                undefined,
                                                [elx:token(integer,
                                                           1,
                                                           "1")])])]},
                     elx_parse_engine:run(Grammar,
                                         'E',
                                         [elx:token(integer, 1, "1"),
                                          elx:token(op, '+', "+"),
                                          elx:token(integer, 1, "1"),
                                          elx:token(op, '+', "+"),
                                          elx:token(integer, 1, "1")]))
       ]
   end}.

%%%_* Test helpers =============================================================
%%%_* Emacs ====================================================================
%%% Local Variables:
%%% allout-layout: t
%%% erlang-indent-level: 2
%%% End: