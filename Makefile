all:
	erlc rtree.erl
run: all
	erl -e "l(rtree). RTree = rtree:new_tree(). rtree:insert({\"123.5\",\"-25.0\"})."
