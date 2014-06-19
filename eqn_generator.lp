#const numLayers = 5.
#const maxChildren	=	3.	% generated nodes can only have so many children
#const maxDepth		=	3.

% define number of nodes per layer
_layer(1..numLayers).
_layerNodes(1, 2).
_layerNodes(2, 6).
_layerNodes(3, 10).
_layerNodes(4, 20).
_layerNodes(5, 20).

% define nodes
_node(_id(Layer, Number))	:-	_layer(Layer), _layerNodes(Layer, NumNodes), Number = 1..NumNodes.

				% expression tree properties
% root nodes are all in first layer, and count as depth 0
_root(_id(1, Number)) :- _node(_id(1, Number)).
_depth(_id(Layer, Number), Layer)	:- _node(_id(Layer, Number)).

% valid children
_validChild(_id(Layer1, Num1), _id(Layer2, Num2))	:-	_node(_id(Layer1, Num1)),
														_node(_id(Layer2, Num2)),
														Layer1 = Layer2 - 1.

				% define node properties
% operator nodes
_type(oper;poly).
_operator(div;mul;add).
_childCount(2..maxChildren).
_side(left; right).
_side(_id(1,1), left).
_side(_id(1,2), right).



% problem generation
_initially(Node, _nodeInfo(active))	:-	_root(Node).

% assigning type to a node
1 { _initially(Node, _nodeInfo(type, Type)) : _type(Type) } 1		:-	_initially(Node, _nodeInfo(active)),
																		_depth(Node, Depth), Depth < maxDepth.
 _initially(Node, _nodeInfo(type, poly))							:-	_initially(Node, _nodeInfo(active)),
																		_depth(Node, Depth), Depth = maxDepth.

% TODO: adjust to prevent parent from having same type
1 { _initially(Node, _nodeInfo(operation, Op)) : _operator(Op) } 1	:-	_initially(Node, _nodeInfo(type, oper)).


% deciding number of children
1 { _initially(Node, _nodeInfo(numchildren, Num)) : _childCount(Num) } 1	:-	_initially(Node, _nodeInfo(operation, Op)),
																			Op != div.
_initially(Node, _nodeInfo(numchildren, 2))						:-	_initially(Node, _nodeInfo(operation, div)).

% generate children and assign ordering
1 { _initially(Parent, _treeInfo(childnum, _num(ChildNo, FreeNode))) 
	: _validChild(Parent, FreeNode)
}	1 
	:-	_initially(Parent, _nodeInfo(numchildren, Num)), ChildNo = 1..Num.

% every numbered child is also an "active child"
_initially(Parent, _treeInfo(activechild, Child))	:-	_initially(Parent, _treeInfo(childnum, _num(ChildNo, Child))).

% each child can have at most one parent
% TODO: figure out if this is the best way to write this rule (write visualizer first)
		%maybe this should be a test
:- 2 { _initially(Parent, _treeInfo(activechild, Child)) : _node(Parent) }, _node(Child).
% each node must have exactly N children
:- _initially(Node, _nodeInfo(numchildren, Num)), 
	not Num { _initially(Node, _treeInfo(activechild, Child)) : _node(Child) } Num.

:- not _initially(_id(1,2), _nodeInfo(operation, mul)).
_initially(Child, _nodeInfo(active))	:-	_initially(Parent, _treeInfo(activechild, Child)).

_numPolyTerms(1..5).
% 
% generate polynomials
1 { _makePolyWithDeg(Node, Deg) : _degree(Deg), Deg <= maxAssignableDegree } 1 	:-	_initially(Node, _nodeInfo(type, poly)).
1 { _makePolyWithCoeff(Node, Coeff) : _coeff(Coeff), Coeff <= maxAssignableCoeff } 1 	:-	_initially(Node, _nodeInfo(type, poly)).
1 { _makePolyWithTerms(Node, NumTerms) : _numPolyTerms(NumTerms) } 1 	:-	_initially(Node, _nodeInfo(type, poly)).

_initially(Node, _nodeInfo(mono, _monoInfo(Num, Mono))) :- _hasMonom(Node, Num, Mono).



#show _initially/2.
