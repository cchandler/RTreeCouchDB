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

-module(rtree).


% -export([start_link/2, start/2, stop/0]).
% -export([start_link/2]).
-export([new_tree/0]).
-export([insert/2]).
% -export([choose_leaf/1]).
% -export([all_combinations/2]).

-record(rtree, {root, 
				min_node_entries,
				max_node_entries}).

-record(node, {boundingbox, values=[], children=[], parent}).

-record(boundingbox, {topleft,topright,bottomleft,bottomright, area}).

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

%% Generate a new basic tree
new_tree() -> #rtree{root= #node{}, min_node_entries=1, max_node_entries=3}.


%% Insert data into the tree
insert(_RTree, {}) -> ok;
insert(#rtree{root=RTreeRoot}=RTree, {Figure, Data}=NewRecord) -> 
	Node = choose_leaf(RTreeRoot),
	case has_space(RTree, Node) of
		true -> 
			NewValues = lists:append(Node#node.values, [Figure]),
			update_node(RTree,Node,NewValues);
		false -> 
			quadratic_split(lists:append(Node#node.values, [Figure]))
	end.
	
%% Clean up the RTree
update_node(RTree,Node,NewValues) ->
	NewNode = Node#node{values=NewValues},
	NewRTree = RTree#rtree{root=NewNode}.

%% Determine if the node in question is a leaf node
is_leaf(Node) -> 
	if length(Node#node.children) > 0 ->
		false;
	true ->
		true
	end.
	
%% Split a leaf node that has exceeded max_node_entries using
%% the quadratic method
quadratic_split(Values) -> 
	{Seed1,Seed2} = quadratic_pick_seeds(Values),
	Clean1 = lists:delete(Seed1, Values),
	Clean2 = lists:delete(Seed2, Clean1),
	Clean2.

%% Choose two elements from the max_node_entries+1 value list
%% by finding the most "wasteful" bounding box of two antipodal figures
quadratic_pick_seeds(Values) -> 
	CombinationValues = all_combinations(Values, []),
	{_, {_, FinalBoundingBox, Seeds} } = lists:mapfoldl(
	fun({Figure1,Figure2}=Elem, {D,_BB,Pair}=Acc) -> 
	    io:format("Figure1 = ~p Figure2 = ~p ~n", [Figure1, Figure2]),
        % BoundingBox = generate_bounding_box(Elem),
        BoundingBox = generate_bounding_box_list([Figure1,Figure2]),
		Figure1Area = figure_area(Figure1),
		Figure2Area = figure_area(Figure2),
		if BoundingBox#boundingbox.area - (Figure1Area - Figure2Area) > D ->
			{Elem, {BoundingBox#boundingbox.area,BoundingBox, {Figure1,Figure2}}};
		true ->
			{Elem, Acc}
		end
	end, {0,#boundingbox{}, {} }, CombinationValues),
	io:format("Seeds = ~p BoundingBox = ~p ~n", [Seeds, FinalBoundingBox]),
	Seeds.

%% Generate all combinations of list pairs
all_combinations([], Combinations) -> Combinations;
all_combinations([H | T], Combinations) ->
	NewCombinations = lists:map(fun(Elem) -> 
		{H,Elem}
		end, T),
	all_combinations(T, NewCombinations ++ Combinations).

%%  Find the Area created by the two dimensional rectangle described by Figure
figure_area(Figure1) ->
	F1rm = rightmost_point(Figure1),
	F1tm = topmost_point(Figure1),
	F1lm = leftmost_point(Figure1),
	F1bm = bottommost_point(Figure1),
	{_F1tm_x,F1tm_y} = F1tm,
	{F1lm_x,_F1lm_y} = F1lm,
	{_F1bm_x,F1bm_y} = F1bm,
	{F1rm_x,_F1rm_y} = F1rm,
	Figure1Area = abs(F1lm_x - F1rm_x) * abs(F1tm_y - F1bm_y).


%%  Generate a bounding box around arbitrary number of rectangles
generate_bounding_box_list(Figures) ->
    %Find the greatest Y coordinate
    {_, {FinalTopY,FinalTopPoint}} = lists:mapfoldl(fun(Figure, {TopYValue, _TopPoint}=Acc) ->
        {X,Y} = topmost_point(Figure),
        if Y > TopYValue ->
            {Figure, {Y, {X,Y}} };
        true ->
            {Figure, Acc}
        end
    end, {0,{}}, Figures),
    
    
    {_, {FinalBottomY,FinalBottomPoint}} = lists:mapfoldl(fun(Figure, {BottomYValue, _BottomPoint}=Acc) ->
        {_X,Y}=NewBottomPoint = bottommost_point(Figure),
        if Y < BottomYValue ->
            {Figure, {Y, NewBottomPoint} };
        true ->
            {Figure, Acc}
        end
    end, {infinity,{}}, Figures),
    
    {_, {FinalLeftX,FinalLeftPoint}} = lists:mapfoldl(fun(Figure, {LeftXValue, _LeftPoint}=Acc) ->
        {X,_Y}=NewLeftPoint = leftmost_point(Figure),
        if X < LeftXValue ->
            {Figure, {X, NewLeftPoint} };
        true ->
            {Figure, Acc}
        end
    end, {infinity,{}}, Figures),
    
    {_, {FinalRightX,FinalRightPoint}} = lists:mapfoldl(fun(Figure, {RightXValue, _RightPoint}=Acc) ->
        {X,_Y}=NewRightPoint = rightmost_point(Figure),
        if X > RightXValue ->
            {Figure, {X, NewRightPoint} };
        true ->
            {Figure, Acc}
        end
    end, {0,{}}, Figures),
    
    TopEdgeLength = abs(FinalLeftX - FinalRightX),
	SideEdgeLength = abs(FinalTopY - FinalBottomY),
	BBArea = TopEdgeLength * SideEdgeLength,
	BoundingBox = #boundingbox{ area=BBArea, 
	    topleft={FinalLeftX,FinalTopY},
	    topright={FinalRightX, FinalTopY}, 
	    bottomright={FinalRightX, FinalBottomY}, 
	    bottomleft={FinalLeftX, FinalBottomY} },
	    
	io:format("Bounding box2 = ~p ~n", [BoundingBox]),
	BoundingBox.

%% Generate a bounding box around two rectangular figures
% generate_bounding_box({Figure1, Figure2}) -> 
%   % {Figure1, Figure2} = H,
%   
%     % io:format("Figure1, Figure2 = ~p ~p ~n", [Figure1, Figure2]),
%   F1rm = rightmost_point(Figure1),
%   F2rm = rightmost_point(Figure2),
%   F1tm = topmost_point(Figure1),
%   F2tm = topmost_point(Figure2),
%   
%   if F1tm > F2tm ->
%       {_,TopCoordinate} = F1tm;
%   true ->
%       {_,TopCoordinate} = F2tm
%   end,
%   
%   if F1rm > F2rm ->
%       {RightCoordinate,_} = F1rm;
%   true ->
%       {RightCoordinate,_} = F2rm
%   end,
%   F1lm = leftmost_point(Figure1),
%   F2lm = leftmost_point(Figure2),
%   F1bm = bottommost_point(Figure1),
%   F2bm = bottommost_point(Figure2),
%   
%   if F1bm < F2bm ->
%       {_,BottomCoordinate} = F1bm;
%   true ->
%       {_,BottomCoordinate} = F2bm
%   end,
%   
%   if F1lm < F2lm ->
%       {LeftCoordinate,_} = F1lm;
%   true ->
%       {LeftCoordinate,_} = F2lm
%   end,
%   
%   TopEdgeLength = abs(LeftCoordinate - RightCoordinate),
%   SideEdgeLength = abs(TopCoordinate - BottomCoordinate),
%   BBArea = TopEdgeLength * SideEdgeLength,
%   BoundingBox = #boundingbox{ area=BBArea, 
%       topleft={LeftCoordinate,TopCoordinate},
%       topright={RightCoordinate, TopCoordinate}, 
%       bottomright={RightCoordinate, BottomCoordinate}, 
%       bottomleft={LeftCoordinate, BottomCoordinate} },
%   
%   io:format("Bounding box = ~p ~n", [BoundingBox]),
%   
%   BoundingBox.	
	
%% Find the right-most point of a two dimensional figure
rightmost_point({Point1,Point2}=_Figure) -> 
	{X1,Y1} = Point1,
	{X2,Y2} = Point2,
	if X1 > X2 ->
		Point1;
	true ->
		Point2
	end.

%% Find the left-most point of a two dimensional figure	
leftmost_point({Point1,Point2}=_Figure) -> 
	{X1,Y1} = Point1,
	{X2,Y2} = Point2,
	if X1 < X2 ->
		Point1;
	true ->
		Point2
	end.

%% Find the top-most point of a two dimensional figure
topmost_point({Point1,Point2}=_Figure) -> 
	{X1,Y1} = Point1,
	{X2,Y2} = Point2,
	if Y1 > Y2 ->
		Point1;
	true ->
		Point2
	end.

%% Find the bottom-most point of a two dimensional figure
bottommost_point({Point1,Point2}=_Figure) -> 
	{X1,Y1} = Point1,
	{X2,Y2} = Point2,
	if Y1 < Y2 ->
		Point1;
	true ->
		Point2
	end.

%% Determine if a given leaf node has space for another value
has_space(RTree,Node) ->
	Max = RTree#rtree.max_node_entries,
	Values = Node#node.values,
	if length(Values) + 1 =< Max ->
		true;
	true ->
		false
		%Requires a new node
	end.

%% Choose a leaf for adding a new value to on insert
choose_leaf(Node) -> 
	case is_leaf(Node) of
		true -> Node;
		false -> Node
		%Still needs choose-subtree and descent operations
	end.
	