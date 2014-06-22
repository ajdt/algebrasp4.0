% Armando Diaz Tolentino <ajdt@cs.washington.edu> 
% 
% A simple ASP program to generate algebraic equations as an expression tree.
% Equations are represented in an expression tree, where internal nodes are
% operators (add/mul/div) and leaf nodes are polynomials.
% Each polynomial has up to maxTerms monomials, which are assigned an ordering.
% 
% NODES:
% Nodes exist in one of five layers, where any node in layer n can potentially
% become a parent of a node in layer n+1. Facts are used to define the number
% of nodes per layer. A node is identified by its layer, and its number within a layer
% At any given time a node can be either active or not. If active, then the node
% is part of the current expression tree, and has some associated data.
%

% I don't want these constants to be changed, so they're not in gen_param.lp
#const numLayers 	=	5.
#const maxChildren	=	3.	% limit on children of operator nodes
#const maxDepth		=	2.	% limits number of layers used during generation

% define number of nodes per layer
_layer(1..numLayers).
_layerNodes(1, 2).
_layerNodes(2, 6).
_layerNodes(3, 20).
_layerNodes(4, 20).
_layerNodes(5, 10).

% define nodes based on layers and nodes in each layer
_node(_id(Layer, Number))	:-	_layer(Layer), _layerNodes(Layer, NumNodes), Number = 1..NumNodes.

% define a set of temp nodes used for intermediate results
_tempLayer(1..3).
_tempLayerNodes(1,1).
_tempLayerNodes(2,4).
_tempLayerNodes(3,6).
% purposely give temp nodes arity 2, so they're not accidentally used where regular nodes would be
_node(_id(temp, Layer, Number))	:- _tempLayerNodes(Layer, NumNodes), Number = 1..NumNodes.

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%% expression tree properties %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% root nodes are all in first layer, and count as depth 1
_root(_id(1, Number)) :- _node(_id(1, Number)).
_depth(_id(Layer, Number), Layer)	:- _node(_id(Layer, Number)).

% a node can only be a parent of nodes in succeeding layer
_validChild(_id(Layer1, Num1), _id(Layer2, Num2))	:-	_node(_id(Layer1, Num1)),
														_node(_id(Layer2, Num2)),
														Layer1 = Layer2 - 1.
% temp  nodes have children too...
_validChild(_id(temp, Layer1, Num1), _id(temp, Layer2, Num2))	
													:-	_node(_id(temp, Layer1, Num1)),
														_node(_id(temp, Layer2, Num2)),
														Layer1 = Layer2 - 1.

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%% node properties %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
_type(oper;poly).
_operator(div;mul;add).
_childCount(2..maxChildren).
_side(left; right).
_side(_id(1,1), left).
_side(_id(1,2), right).



%%%%%%%%%%%%%%%%%%%%%%%%%%%%%% PROBLEM GENERATION %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
_initially(Node, _nodeInfo(active,yes))	:-	_root(Node).

% assigning type to a node, if we're at max depth node must be a polynomial
1 { _initially(Node, _nodeInfo(type, Type)) : _type(Type) } 1		:-	_initially(Node, _nodeInfo(active,yes)),
																		_depth(Node, Depth), Depth < maxDepth.
 _initially(Node, _nodeInfo(type, poly))							:-	_initially(Node, _nodeInfo(active,yes)),
																		_depth(Node, Depth), Depth = maxDepth.

1 { _initially(Node, _nodeInfo(operation, Op)) : _operator(Op) } 1	:-	_initially(Node, _nodeInfo(type, oper)).


% assign number of children, if you're a division node, num children must be 2
1 { _initially(Node, _nodeInfo(numchildren, Num)) : _childCount(Num) } 1	
											:-	_initially(Node, _nodeInfo(operation, Op)),
												Op != div.
_initially(Node, _nodeInfo(numchildren, 2))						:-	_initially(Node, _nodeInfo(operation, div)).

% generate children for parent node 
_initially(_id(Layer, ParentNum), _treeInfo(activechild, _id(Layer+1, (ParentNum - 1)*maxChildren + ChildNo)))
					:-	_initially(_id(Layer, ParentNum), _nodeInfo(numchildren, Num)), 
						ChildNo = 1..Num.

% indicate child is active also
_initially(Child, _nodeInfo(active,yes))	:-	_initially(Parent, _treeInfo(activechild, Child)).

										% GENERATE POLYNOMIALS
_numPolyTerms(1..2).
% NOTE: degree and leading coef are decided here, so that we can create leadingCoef, and degree predicates for 
% poly nodes if necessary
1 { _makePolyWithDeg(Node, Deg) : _degree(Deg), Deg <= maxAssignableDegree } 1 	
					:-	_initially(Node, _nodeInfo(type, poly)).
1 { _makePolyWithCoeff(Node, Coeff) : _coeff(Coeff), Coeff <= maxAssignableCoeff } 1 	
					:-	_initially(Node, _nodeInfo(type, poly)).
1 { _makePolyWithTerms(Node, NumTerms) : _numPolyTerms(NumTerms) } 1 	
					:-	_initially(Node, _nodeInfo(type, poly)).

_initially(Node, _nodeInfo(coeffof(Num), _coeff(Coeff)))	:- _hasMonom(Node, Num, _monomial(Coeff, Deg)).
_initially(Node, _nodeInfo(degof(Num), _degree(Deg)))		:- _hasMonom(Node, Num, _monomial(Coeff, Deg)).

_initially(Node, _nodeInfo(numterms, NumTerms))			:-	_makePolyWithTerms(Node, NumTerms).

% fractions also have numer/denom fields to alias first and second child
_initially(_id(ParentLayer, ParentNum), _nodeInfo(numer, _id(ChildLayer, FstChildNum)))	
					:-	_initially(_id(ParentLayer, ParentNum), _nodeInfo(operation, div)),
						FstChildNum = (ParentNum -1)*maxChildren + 1,
						ChildLayer = ParentLayer + 1.
_initially(_id(ParentLayer, ParentNum), _nodeInfo(denom, _id(ChildLayer, SndChildNum)))	
					:-	_initially(_id(ParentLayer, ParentNum), _nodeInfo(operation, div)),
						SndChildNum = (ParentNum -1)*maxChildren + 2,
						ChildLayer = ParentLayer + 1.


#show _initially/2.
