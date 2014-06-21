%Operator properties

_isMul(Node, Step)	:-	_holds(Node, _nodeInfo(operation, mul), Step).
_isAdd(Node, Step)	:-	_holds(Node, _nodeInfo(operation, add), Step).
_isDiv(Node, Step)	:-	_holds(Node, _nodeInfo(operation, div), Step).

_numSubExpressions(Node, NumKids, Step)	
					:-	_holds(Node, _nodeInfo(numchildren, NumKids), Step).
_termOf(Parent, Child, Step)	
					:-	_holds(Parent, _treeInfo(activechild, Child), Step).
_numerOf(Fraction, Numer, Step)
					:-	_holds(Fraction, _nodeInfo(numer, Numer), Step).
_denomOf(Fraction, Denom, Step)
					:-	_holds(Fraction, _nodeInfo(denom, Denom), Step).



% are there enough free nodes for tree to expand?
_canGrowTreeFromNode(_id(Layer, Number), Step)	
					:-	_node(_id(Layer, Number)), Layer <= maxDepth, _step(Step).


							%				TREE OPERATIONS
% possible operations

% deleting a monomial
% 
_update(Polynomial, _nodeInfo(Monom, Multiplicity - NumTimes), Step)
					:-	_deleteMonomial(Polynomial, Monom, NumTimes, Step),
						_holds(Poly, _nodeInfo(Monom, Multiplicity), Step),
						Multiplicity > NumTimes.
_destroyMonomial(Polynomial, Monom, Step)
					:-	_deleteMonomial(Polynomial, Monom, NumTimes, Step),
						_holds(Poly, _nodeInfo(Monom, Multiplicity), Step),
						Multiplicity <= NumTimes.
_remove(Poly, _nodeInfo(monom, Monom), Step)
					:-	_destroyMonomial(Poly, Monom, Step).
_remove(Poly, _nodeInfo(Monom, Num), Step)
					:-	_destroyMonomial(Poly, Monom, Step),
						_holds(Poly, _nodeInfo(Monom, Num), Step).
% update the number of terms
_update(Poly, _nodeInfo(numterms, NumTerms - NumTimes), Step)
					:-	_deleteMonomial(Poly, Mono, NumTimes, Step),
						_holds(Poly, _nodeInfo(numterms, NumTerms), Step).

% canceling a term
_deleteNode(Term, Step)	
					:-	_cancelTerm(Expr, Term, Step),
						_node(Term).
_deleteMonomial(Poly, Term, 1, Step)		
					:-	_cancelTerm(Poly, Term, Step),
						not _node(Term).

% deleting a node means to remove all parent pointers, and the entire subtree rooted at that node
% to remove node properties use _clearNode(...)

_deleteChildProperties(Parent, Child, Step)
					:-	_deleteNode(Child, Step),
						_termOf(Parent, Child, Step).	

% update parent's child count
_update(Parent, _nodeInfo(numchildren, NumKids - 1), Step)
					:-	_deleteChildProperties(Parent, Node, Step),
						_holds(Parent, _nodeInfo(numchildren, NumKids), Step).
% remove parent pointer to child
_remove(Parent, _treeInfo(activechild, Term), Step)
					:-	_deleteChildProperties(Parent, Term, Step).
% delete the node
_remove(Node, Info, Step)
					:-	_deleteNode(Node, Step),
						_holds(Node, Info, Step).
% 'recursively' delete all children
_deleteChildrenOf(Node, Step)
					:-	_deleteNode(Node, Step).
_deleteNode(Child, Step)
					:-	_deleteChildrenOf(Parent, Step),
						_termOf(Parent, Child, Step).


% swap node (shallow copy of nodes
_shallowCopy(Node1, Node2, Step)
					:-	_swapTerms(Node1, Node2, Step).
_shallowCopy(Node2, Node1, Step)
					:-	_swapTerms(Node1, Node2, Step).
_update(Copy, Info, Step)
					:-	_shallowCopy(Copy, ToCopy, Step),
						_holds(ToCopy, Info, Step).

% clear a node's values
_remove(Node, Info, Step)
					:-	_clearNode(Node, Step),
						_holds(Node, Info, Step).
_introduce(Node, _nodeInfo(active, yes), Step)		% cleared node is still active
					:-	_clearNode(Node, Step).
_clearNode(Node, Step)
					:- _clearRecursive(Node, Step).
_clearRecursive(Child, Step)
					:-	_clearRecursive(Node, Step),
						_holds(Node, _nodeInfo(activechild, Child), Step).
% setToOne
_deleteChildrenOf(Node, Step)
					:-	_setToOne(Node, Step).
_clearNode(Node, Step)	
					:-	_setToOne(Node, Step).
_setToUnitPoly(Node, Step)	% defined in polynomial class
					:-	_setToOne(Node, Step).
% activateNode
_introduce(Node, _nodeInfo(active, yes), Step)
					:-	_activate(Node, Step).
% copy a node
% copy entire subtree
% acquire a free node

% move subtree down, 
% move children down
% copy subtree, 
% delete subtree, 
% compare subtrees (equality)
% move subtree up

