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
-export([is_root/2]).
-export([get_root/1]).

% -export([choose_leaf/1]).
% -export([all_combinations/2]).

-record(rtree, {root, 
				min_node_entries,
				max_node_entries}).

-record(node, {boundingbox, values=[], children=[], parent}).

-record(childref, {boundingbox, child}).

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
	NodePath = choose_leaf(RTreeRoot,Figure,[]),
	io:format("Node Path to LeafNode= ~p ~n", [NodePath]),
	Node = lists:last(NodePath),
	case has_space(RTree, Node) of
		true -> 
		    io:format("Space available for insert ~n", []),
			NewValues = lists:append(Node#node.values, [Figure]),
			update_node(RTree,RTree#rtree.root,NodePath,NewValues);
		false -> 
		    io:format("Space NOT available for insert, doing quadratic split ~n", []),
			[Node1, Node2] = quadratic_split(lists:append(Node#node.values, [Figure])),
			case is_root(RTree,Node) of
			    true ->
			    NewRoot = #node{children=[#childref{child=Node1, boundingbox=Node1#node.boundingbox},#childref{child=Node2, boundingbox=Node2#node.boundingbox}]},
			    RTree#rtree{root=NewRoot};
			false ->
			    ok
			    %Not a root split
		    end
	end.
	
adjust_tree(RTree, Node1) ->
    adjust_tree(RTree,Node1,[]).
    
adjust_tree(RTree, Node1, _ ) when RTree#rtree.root == Node1 ->
    root_found;
    
% Addition, but no split was generated from insertion
adjust_tree(RTree, Node1, []) ->
    Parent = Node1#node.parent,
    ChildRef = find_child_ref(Parent,Node1),
    ChildFigures = find_all_descendent_figures(ChildRef),
    NewBB = generate_bounding_box_list(ChildFigures),
    ChildRef1 = ChildRef#childref{boundingbox = NewBB};
adjust_tree(RTree, Node1, Node2) ->
    Parent = Node1#node.parent,
    ChildRef = find_child_ref(Parent,Node1),
    ChildFigures = find_all_descendent_figures(ChildRef),
    NewBB = generate_bounding_box_list(ChildFigures),
    ChildRef1 = ChildRef#childref{boundingbox = NewBB},
    
    ChildFigures2 = find_all_descendent_figures(Node2),
    NewBB2 = generate_bounding_box_list(ChildFigures2),
    ChildRef2 = ChildRef#childref{boundingbox=NewBB2, child=Node2},
    
    case has_child_space(RTree,Parent) of
    true->
        % Add the new children nodes to the parent
        NewParent1 = add_child(Parent,ChildRef1),
        NewParent2 = add_child(Parent, ChildRef2);
    false ->
        % split_node(RTree,Parent),
        split_parent
    end,
    ok.
	
%% Clean up the RTree
update_node(RTree,CurrentNode,NodePath,NewValues) ->
    NewRoot = update_node(RTree#rtree.root, NodePath, NewValues),
    RTree#rtree{root=NewRoot}.

update_node(CurrentNode, [CurrentNode], NewValues) ->
    % Hit a leaf node
    % io:format("Starting update_node CurrentNode= ~p LeafNode= ~p ~n", [CurrentNode, CurrentNode]),
    CurrentNode#node{values=NewValues};
update_node(CurrentNode, [], NewValues) ->
    % io:format("Starting second update_node CurrentNode= ~p ~n", [CurrentNode]),
    CurrentNode#node{values=NewValues};
update_node(CurrentNode,[NextNode | RemainingPath ],NewValues) ->
    % io:format("Starting update_node CurrentNode= ~p NextNode= ~p ~n", [CurrentNode, NextNode]),
    ChildRef = find_child_ref(CurrentNode,NextNode),
    UpdatedChild = update_node(ChildRef#childref.child , RemainingPath, NewValues),
    CurrentWithoutChild = remove_child(CurrentNode,ChildRef),
    CurrentWithNewChild = add_child(CurrentWithoutChild,#childref{child=UpdatedChild}),
    UpdatedBB = CurrentWithNewChild#node{children= refresh_child_ref_boundingboxes(CurrentWithNewChild#node.children)},
    UpdatedBB.
	
%% Add a child reference to a node
add_child(Node, ChildRef) ->
    % io:format("Adding child reference ~p ~p ~n", [Node,ChildRef]),
    NewNode = Node#node{children=Node#node.children ++ [ChildRef]}.
    
%% Remove a child reference from a node
remove_child(Node, ChildRef) ->
    % io:format("Removing child reference ~p ~p ~n", [Node,ChildRef]),
    NewNode = Node#node{children=Node#node.children -- [ChildRef]}.

%% Given a list of child references update their corresponding bounding boxes
refresh_child_ref_boundingboxes(ChildRefList) ->
    lists:map(fun(Elem) -> 
        Figures = find_all_descendent_figures(Elem#childref.child),
        BoundingBox = generate_bounding_box_list(Figures),
        Elem#childref{boundingbox=BoundingBox} 
        end, ChildRefList).

%% Determine if the node in question is a leaf node
is_leaf(Node) -> 
	if length(Node#node.children) > 0 ->
		false;
	true ->
		true
	end.
	
get_root(RTree) ->
    RTree#rtree.root.

is_root(RTree,Node) ->
    RTree#rtree.root == Node.
	
find_child_ref(Parent,Child) ->
    Children = Parent#node.children,
    % {_,Result} = lists:keysearch(Child, 2, Children),
    {Result} = lists:foldl(fun(Elem,Acc) -> 
        % io:format("Looking for child reference ~p Child =~p ~n", [Elem,Child]),
        case Elem#childref.child == Child of
            true ->
                {Elem};
            false ->
                Acc
            end
        end, {lists:nth(1,Children)}, Children),
    Result.
	
%% Split a leaf node that has exceeded max_node_entries using
%% the quadratic method
quadratic_split(Values) -> 
	{Seed1,Seed2} = quadratic_pick_seeds(Values),
	Clean1 = lists:delete(Seed1, Values),
	Clean2 = lists:delete(Seed2, Clean1),
	Group1 = [Seed1],
	Group2 = [Seed2],
	% For each elemen in the remaining values go through and add
	% that point to the group that would require the least increase in
	% area to accomodate 
	% Note: does not fully implement PickNext, uses a heuristic instead
	SplitGroups = lists:foldl(fun(Elem, {{G1,BB1},{G2,BB2}}=Acc) -> 
        % io:format("Starting fold Elem= ~p Acc= ~p ~n", [Elem, Acc]),
        % io:format("G1 ++ Elem = ~p ~n", [G1 ++ Elem]),
	    Group1BB = generate_bounding_box_list(G1 ++ [Elem]),
	    Group2BB = generate_bounding_box_list(G2 ++ [Elem]),
	    if (Group1BB#boundingbox.area - BB1#boundingbox.area) >=  (Group2BB#boundingbox.area - BB2#boundingbox.area) ->
	        {{G1, BB1},{ G2 ++ [Elem], Group2BB}};
	    true ->
	        {{G1 ++ [Elem], Group1BB},{ G2, BB2 }}
            end
	    end, {{Group1, generate_bounding_box_list(Group1)},{Group2, generate_bounding_box_list(Group2)}}, Clean2),
	{{FinalGroup1,FinalGroup1BB },{FinalGroup2, FinalGroup2BB }} = SplitGroups,
	
    % io:format("Final group 1 = ~p Final group 2 = ~p ~n", [FinalGroup1, FinalGroup2]),
	[#node{values=FinalGroup1, boundingbox=FinalGroup1BB },#node{values=FinalGroup2, boundingbox=FinalGroup2BB}].

%% Choose two elements from the max_node_entries+1 value list
%% by finding the most "wasteful" bounding box of two antipodal figures
quadratic_pick_seeds(Values) -> 
	CombinationValues = all_combinations(Values, []),
	{_, {_, FinalBoundingBox, Seeds} } = lists:mapfoldl(
	fun({Figure1,Figure2}=Elem, {D,_BB,Pair}=Acc) -> 
        % io:format("Figure1 = ~p Figure2 = ~p ~n", [Figure1, Figure2]),
        BoundingBox = generate_bounding_box_list([Figure1,Figure2]),
		Figure1Area = figure_area(Figure1),
		Figure2Area = figure_area(Figure2),
		if BoundingBox#boundingbox.area - (Figure1Area - Figure2Area) > D ->
			{Elem, {BoundingBox#boundingbox.area,BoundingBox, {Figure1,Figure2}}};
		true ->
			{Elem, Acc}
		end
	end, {0,#boundingbox{}, {} }, CombinationValues),
    % io:format("Seeds = ~p BoundingBox = ~p ~n", [Seeds, FinalBoundingBox]),
	Seeds.

%% Generate all combinations of list pairs
all_combinations([], Combinations) -> Combinations;
all_combinations([H | T], Combinations) ->
	NewCombinations = lists:map(fun(Elem) -> 
		{H,Elem}
		end, T),
	all_combinations(T, NewCombinations ++ Combinations).
	

% This is when we want all child figures of a specific child entry in an
% interior node
find_all_descendent_figures(ChildRef = #childref{}) ->
    io:format("Processing a child ref = ~p ~n", [ChildRef]),
    % {_,SpecificChildNode} = ChildRef,
    % find_all_descendent_figures(SpecificChildNode);
    find_all_descendent_figures(ChildRef#childref.child);
% All children of a given node
find_all_descendent_figures(InteriorNode = #node{}) when length(InteriorNode#node.children) > 0 ->
    io:format("Processing an interior node = ~p ~n", [InteriorNode]),
    
    lists:foldl(fun(Elem, Acc) -> 
        io:format("Acc = ~p Elem = ~p ~n", [Acc, Elem]),
        Acc1 = Acc ++ find_all_descendent_figures(Elem),
        Acc1
        end, [], InteriorNode#node.children );
% Processing a given leaf
find_all_descendent_figures(LeafNode = #node{}) ->
    io:format("Hit a leaf node = ~p ~n", [LeafNode]),
    find_all_descendent_figures( LeafNode#node.values);
find_all_descendent_figures([]) ->
    io:format("Empty list! ~n", []),
    [];
find_all_descendent_figures([H|T]) ->
    io:format("Processing head = ~p ~n", [H]),
    [H] ++ find_all_descendent_figures(T).

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

area_difference(BoundingBox1=#boundingbox{}, BoundingBox2=#boundingbox{}) ->
    abs(BoundingBox1#boundingbox.area - BoundingBox2#boundingbox.area).


%%  Generate a bounding box around arbitrary number of rectangles
generate_bounding_box_list(Figures) ->

    % io:format("Finding Y coordinate = ~p ~n", [Figures]),
    
    {_, {FinalTopY,FinalTopPoint}} = lists:mapfoldl(fun(Figure, {TopYValue, _TopPoint}=Acc) ->
        {X,Y} = topmost_point(Figure),
        if Y > TopYValue ->
            {Figure, {Y, {X,Y}} };
        true ->
            {Figure, Acc}
        end
    end, {0,{}}, Figures),
    
    % io:format("Finding another coordinate = ~p ~n", [Figures]),
    
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
	    
    % io:format("Bounding box2 = ~p ~n", [BoundingBox]),
	BoundingBox.	
	
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
has_space(RTree,ChildRef=#childref{}) ->
    has_space(RTree,ChildRef#childref.child);
has_space(RTree,Node=#node{}) ->
    io:format("has_space/2 RTree= ~p Node ~p ~n", [RTree, Node]),
	Max = RTree#rtree.max_node_entries,
	Values = Node#node.values,
	if length(Values) + 1 =< Max ->
		true;
	true ->
	    %Requires a new node
		false
	end.
	
has_child_space(RTree,Node) ->
	Max = RTree#rtree.max_node_entries,
	Values = Node#node.children,
	if length(Values) + 1 =< Max ->
		true;
	true ->
		false
		%Requires a new node
	end.

%% Choose a leaf for adding a new value to on insert
%% Returns a complete path from root to leaf with the leaf
%% as the last element in the list
choose_leaf(Node, Figure, Path) -> 
	case is_leaf(Node) of
		true -> Path ++ [Node];
		false ->
		    % Find the entry in
		    {_, NextNode} = lists:foldl(fun(Elem, {Area,_}=Acc) -> 
		        io:format("choose_leaf Elem= ~p Acc= ~p ~n", [Elem, Acc]),
		        AllFigures = find_all_descendent_figures(Elem),
		        BoundingBox = generate_bounding_box_list(AllFigures),
                case area_difference(BoundingBox, Elem#childref.boundingbox) < Area of true ->
                    % io:format("Changed ACC = ~p ~n", [Elem]),
                    {BoundingBox#boundingbox.area, Elem#childref.child};
                _ ->
                    Acc
                    end
		        end, {infinity,[]}, Node#node.children),
		Path ++ choose_leaf(NextNode, Figure, Path)
	end.
	