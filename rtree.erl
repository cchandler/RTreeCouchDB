%% Copyright (c) 2009 Chris Chandler <chris@chrischandler.name>
%% 
%% Permission is hereby granted, free of charge, to any person
%% obtaining a copy of this software and associated documentation
%% files (the "Software"), to deal in the Software without
%% restriction, including without limitation the rights to use,
%% copy, modify, merge, publish, distribute, sublicense, and/or sell
%% copies of the Software, and to permit persons to whom the
%% Software is furnished to do so, subject to the following
%% conditions:
%% 
%% The above copyright notice and this permission notice shall be
%% included in all copies or substantial portions of the Software.
%% 
%% THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND,
%% EXPRESS OR IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES
%% OF MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND
%% NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT
%% HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY,
%% WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING
%% FROM, OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR
%% OTHER DEALINGS IN THE SOFTWARE.
%% 
%% 
%% @author Chris Chandler <chris@chrischandler.name>
%% @copyright 2009 Chris Chandler
%% @version 0.1alpha
%% @doc The goal server module
%% 
%% This code is available as Open Source Software under the MIT license.
%% 
%% Updates at http://github.com/cchandler/meson/

-module(rtree).

% -behaviour(gen_server).
% -behaviour(gen_mod).

%export for gen_mod
% -export([start_link/2, start/2, stop/0]).
% -export([start_link/2]).
-export([new_tree/0]).
-export([insert/2]).
-export([choose_leaf/1]).
-export([all_combinations/2]).
	
%-define(SERVER, goal-finder).
%-define(PROCNAME, goal_finder).

%-record(state, {host}).
-record(rtree, {root, 
				min_node_entries,
				max_node_entries}).

-record(node, {values=[], children=[], parent}).

% leaf node
% {I (n-dimensional figure), tuple-identifier}
% non-leaf node
% {I, child pointer}
% minimum_node_entries maximum_node_entries, 1 3

% 1. Every leaf node contains between m and M index records unless it is the 
% root Thus, the root can have less entries than m 
% 2. For each index record in a leaf node, I is the smallest rectangle that spatially 
% contains the n-dimensional data ob ject represented by the indicated tuple 
% 3. Every non-leaf node has between m and M children unless it is the root 
% 4. For each entry in a non-leaf node, i is the smallest rectangle that spatially 
% contains the rectangles in the child node 
% 5. The root node has at least two children unless it is a leaf 
% 6. All leaves appear on the same level. That means the tree is balanced

new_tree() -> #rtree{root= #node{}, min_node_entries=1, max_node_entries=3}.

insert(RTree, {}) -> ok;
insert(#rtree{root=RTreeRoot}=RTree, {Figure, Data}=NewRecord) -> 
	Node = choose_leaf(RTreeRoot),
	case has_space(RTree, Node) of
		true -> 
			NewValues = lists:append(Node#node.values, [NewRecord]),
			update_node(RTree,Node,NewValues);
		false -> 
			quadratic_split(lists:append(Node#node.values, [NewRecord])),
			requires_split
	end.
	
%% Clean up the RTree
update_node(RTree,Node,NewValues) ->
	NewNode = Node#node{values=NewValues},
	NewRTree = RTree#rtree{root=NewNode}.

is_leaf(Node) -> 
	if length(Node#node.children) > 0 ->
		false;
	true ->
		true
	end.
	
quadratic_split(Values) -> 
	quadratic_pick_seeds(Values),
	ok.

quadratic_pick_seeds(Values) -> 
	CombinationValues = all_combinations(Values, []).

all_combinations([], Combinations) -> Combinations;
all_combinations([H | T], Combinations) ->
	NewCombinations = lists:map(fun(Elem) -> 
		{H,Elem}
		end, T),
	all_combinations(T, NewCombinations ++ Combinations).

generate_bounding_box(Figure1, Figure2) -> ok.



has_space(RTree,Node) ->
	Max = RTree#rtree.max_node_entries,
	Values = Node#node.values,
	if length(Values) + 1 =< Max ->
		true;
	true ->
		false
		%Requires a new node
	end.

choose_leaf(Node) -> 
	case is_leaf(Node) of
		true -> Node;
		false -> Node
		%Still needs choose-subtree and descent operations
	end.
	