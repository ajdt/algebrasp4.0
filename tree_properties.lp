%Operator properties

_isMul(Node, Step)	:-	_holds(Node, _nodeInfo(operation, mul), Step).
_isAdd(Node, Step)	:-	_holds(Node, _nodeInfo(operation, add), Step).
_isDiv(Node, Step)	:-	_holds(Node, _nodeInfo(operation, div), Step).

_numSubExpressions(Node, NumKids, Step)	
					:-	_holds(Node, _nodeInfo(numchildren, NumKids), Step).
_termOf(Parent, Child, Step)	
					:-	_holds(Parent, _treeInfo(activechild, Child), Step),
						_validChild(Parent, Child).
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
% NOTE: deleteMonomialOnly does not update numterms; useful if multiple deletes occur 
% leading to multiple updatesto numterms (and a race condition)
_remove(Polynomial, _nodeInfo(coeffof(Term), Coeff), Step)
					:-	_deleteMonomialOnly(Polynomial, Term, Step),
						_holds(Polynomial, _nodeInfo(coeffof(Term), Coeff), Step).
_remove(Polynomial, _nodeInfo(degof(Term), Deg), Step)
					:-	_deleteMonomialOnly(Polynomial, Term, Step),
						_holds(Polynomial, _nodeInfo(degof(Term), Deg), Step).

_deleteMonomialOnly(Poly, Mono, Step)	:-	_deleteMonomial(Poly, Mono, Step).

% shift down monomial term numbers by 1
_shiftDown(Poly, Term+1, 1, Step)			:-	_deleteMonomial(Poly, Term, Step).

% shifting term numbers for polynomials
_introduce(Poly, _nodeInfo(coeffof(Term - Delta), Coeff), Step)
					:-	_shiftDown(Poly, Start, Delta, Step),
						_holds(Poly, _nodeInfo(coeffof(Term), Coeff), Step).
_introduce(Poly, _nodeInfo(degof(Term - Delta), Deg), Step)
					:-	_shiftDown(Poly, Start, Delta, Step),
						_holds(Poly, _nodeInfo(degof(Term), Deg), Step).
_deleteMonomialOnly(Poly, Term, Step)
					:-	_shiftDown(Poly, Start, Delta, Step),
						_holds(Poly, _nodeInfo(coeffof(Term), Coeff), Step),
						Term >= Start.

% update the number of terms
_update(Poly, _nodeInfo(numterms, NumTerms - 1), Step)
					:-	_deleteMonomial(Poly, Mono, Step),
						_holds(Poly, _nodeInfo(numterms, NumTerms), Step).

% canceling a term
_deleteNode(Term, Step)	
					:-	_cancelTerm(Expr, Term, Step),
						_node(Term).
_deleteNode(Term, Step)	
					:-	_cancelTerm(Term, Step).	% TODO: want both versions of cancelTerm for now 
_deleteMonomial(Poly, Term, Step)		
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

% NOTE: shiftChildren should only be called once per step for a node,
% to avoid race condition on updating the children
% 
_shiftChildren(Parent, ChildNum+1, 1, Step)	
					:-	_cancelTerm(Parent, Child, Step),
						_termOf(Parent, Child, Step),
						not _deleteNode(Parent, Step),
						_holds(Parent, _childnum(ChildNum, Child), Step).
_remove(Parent, _childnum(ChildNo, Child), Step)
					:-	_shiftChildren(Parent, Start, Delta, Step),
						_holds(Parent, _childnum(ChildNo, Child), Step),
						ChildNo >= Start.
_introduce(Parent, _childnum(ChildNo - Delta, Child), Step)
					:-	_shiftChildren(Parent, Start, Delta, Step),
						_holds(Parent, _childnum(ChildNo, Child), Step),
						ChildNo >= Start.


% swap node (shallow copy of nodes)
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
% swap numerator and denom
_swapTerms(Numer, Denom, Step)
					:-	_swapNumerDenom(Frac, Step),
						_numerOf(Frac, Numer, Step),
						_denomOf(Frac, Denom, Step).
_update(DivNode, _nodeInfo(operation, mul), Step)
					:-	_convertDivToMul(DivNode, Step).
_removeFracFields(DivNode, Step)
					:-	_convertDivToMul(DivNode, Step).
_remove(DivNode, _nodeInfo(numer, X), Step)
					:-	_removeFracFields(DivNode, Step),
						_holds(DivNode, _nodeInfo(numer, X), Step).
_remove(DivNode, _nodeInfo(denom, X), Step)
					:-	_removeFracFields(DivNode, Step),
						_holds(DivNode, _nodeInfo(denom, X), Step).
% mul node to div node
_introduce(Node, _nodeInfo(numer, Numer), Step)
					:-	_mulToDiv(Node, Numer, Denom, Step).
_introduce(Node, _nodeInfo(denom, Denom), Step)
					:-	_mulToDiv(Node, Numer, Denom, Step).
_update(Node, _nodeInfo(operation, div), Step)
					:-	_mulToDiv(Node, Numer, Denom, Step).


_mapAndCopy(Term1, Step)
					:-	_groupTerms(Term1, Term2, Step).
_mapAndCopy(Term2, Step)
					:-	_groupTerms(Term1, Term2, Step).
_mapNode(Term, Layer+1, Step)
					:-	 _layerOf(Term, Layer),
						_mapAndCopy(Term, Step).
_introduce(NewTerm, _nodeInfo(X,Y), Step)
					:-	_mapAndCopy(Term, Step),
						_mapto(Term, NewTerm, Step),
						_holds(Term, _nodeInfo(X,Y), Step).
_introduce(NewTerm, _childnum(X,Y), Step)
					:-	_mapAndCopy(Term, Step),
						_mapto(Term, NewTerm, Step),
						_holds(Term, _childnum(X,Y), Step).
% a deallocate children of predicate?

% move subtree down, 
% move children down
% copy subtree, 
% delete subtree, 
% compare subtrees (equality)
% move subtree up

