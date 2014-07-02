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


							%				NODE OPERATIONS

% deleting a monomial
% 
% NOTE: deleteMonomialOnly does not update numterms; useful if multiple deletes occur 
% leading to multiple updatesto numterms (and a race condition)
_remove(Polynomial, _nodeInfo(Deg, Coeff), Step)
					:-	_deleteMonomialOnly(Polynomial, Deg, Step),
						_holds(Polynomial, _nodeInfo(Deg, Coeff), Step).

_deleteMonomialOnly(Poly, Mono, Step)	:-	_deleteMonomial(Poly, Mono, Step).

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
% deleting a node also deallocates it
_deallocated(Node, Step)
					:-	_deleteNode(Node, Step).

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
% activateNode
_introduce(Node, _nodeInfo(active, yes), Step)
					:-	_activate(Node, Step).

% copying a polynomial node
_introduce(Copy, _nodeInfo(X,Y), Step)
					:-	_copyNodeInfo(Copy, Orig, Step),
						_holds(Orig, _nodeInfo(X,Y), Step).


							%				CHANGE NODE OPERATOR
% mul node to div node
_introduce(Node, _nodeInfo(numer, Numer), Step)
					:-	_mulToDiv(Node, Numer, Denom, Step).
_introduce(Node, _nodeInfo(denom, Denom), Step)
					:-	_mulToDiv(Node, Numer, Denom, Step).
_update(Node, _nodeInfo(operation, div), Step)
					:-	_mulToDiv(Node, Numer, Denom, Step).
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
_clearNode(Term1, Step)
					:-	_makeProdNode(Term1, Step).
_introduce(Term1, _nodeInfo(type, oper), Step)
					:-	_makeProdNode(Term1, Step).
_introduce(Term1, _nodeInfo(operation, mul), Step)
					:-	_makeProdNode(Term1, Step).
% change node operation
_update(Node, _nodeInfo(operation, Op), Step)
					:-	_changeNodeOp(Node, Op, Step).


							%				RULE HELPERS
% setToOne
_deleteChildrenOf(Node, Step)
					:-	_setToOne(Node, Step).
_clearNode(Node, Step)	
					:-	_setToOne(Node, Step).
_setToUnitPoly(Node, Step)	% defined in polynomial class
					:-	_setToOne(Node, Step).
% swap numerator and denom
_swapTerms(Numer, Denom, Step)
					:-	_swapNumerDenom(Frac, Step),
						_numerOf(Frac, Numer, Step),
						_denomOf(Frac, Denom, Step).
% group terms
_mapDownAndCopy(Term1, Step)
					:-	_groupTerms(Term1, Term2, Step).
_mapDownAndCopy(Term2, Step)
					:-	_groupTerms(Term1, Term2, Step).
_mapNode(Term, Layer+1, Step)
					:-	 _layerOf(Term, Layer),
						_mapDownAndCopy(Term, Step).
_copyNodeInfo(NewTerm, Term, Step)
					:-	_mapDownAndCopy(Term, Step),
						_mapto(Term, NewTerm, Step).

_deleteNode(Term2, Step)
					:-	_groupTerms(Term1, Term2, Step).
_makeProdNode(Term1, Step)
					:-	_groupTerms(Term1, Term2, Step).
% initialize new fields for Term1
_introduce(Term1, _nodeInfo(numchildren, 2), Step)
					:-	_makeProdNode(Term1, Step).
_introduce(Term1, _childnum(1, NewTerm), Step)
					:-	_makeProdNode(Term1, Step),
						_mapto(Term1, NewTerm, Step).
_introduce(Term1, _treeInfo(activechild, NewTerm), Step)
					:-	_makeProdNode(Term1, Step),
						_mapto(Term1, NewTerm, Step).
_introduce(Term1, _childnum(2, NewTerm), Step)
					:-	_groupTerms(Term1, Term2, Step),
						_mapto(Term2, NewTerm, Step).
_introduce(Term1, _treeInfo(activechild, NewTerm), Step)
					:-	_groupTerms(Term1, Term2, Step),
						_mapto(Term2, NewTerm, Step).
% a deallocate children of predicate?

					% 			NODE ALLOCATION
% copy entire subtree
_mapNodeRec(Child, Layer+1, Step)
					:-	_mapNodeRec(Node, Layer, Step),
						_termOf(Node, Child, Step),
						_layer(Layer),
						_node(Node),
						_step(Step).
_mapNode(Node, Layer, Step)
					:-	_mapNodeRec(Node, Layer, Step).

% XXX warning: does not copy childnum info, this info will probably be removed later
_introduce(NewNode, _treeInfo(activechild, NewChild), Step)
					:-	_copyMappedSubtree(Node, Step),
						_termOf(Node, Child, Step),
						_mapto(Node, NewNode, Step),
						_mapto(Child, NewChild, Step).

_copyMappedSubtree(Child, Step)
					:-	_copyMappedSubtree(Node, Step),
						_termOf(Node, Child, Step).
% recursively copy children
_copyMappedSubtree(Child, Step)
					:-	_copyMappedSubtree(Node, Step),
						_termOf(Node, Child, Step).
% moving a subtree down
_deleteChildrenOf(Node, Step)
					:-	_shiftDownSubtree(Node, Step).
_clearNode(Node, Step)
					:-	_shiftDownSubtree(Node, Step).
% move subtree down, 
_mapNodeRec(Node, Layer + 1, Step)
					:-	_shiftDownSubtree(Node, Step),
						_layerOf(Node, Layer).
% set pointer from old root to new root,
_introduce(Node, _treeInfo(activechild, NewRoot))
					:-	_shiftDownSubtree(Node, Step),
						_mapto(Node, NewRoot, Step).
% setup parent/child pointers
_activateTempNode(PolyNum, Step)
:-	_multiplyPolys(Poly1, Poly2, Step),
	_holds(Poly2, _nodeInfo(numterms, Num), Step),
	PolyNum = 1..Num.

% set basic polynomial properties for node
_holds(_id(temp, 1,1), _treeInfo(activechild, _id(temp, 2, PolyNum)), Step)
	:-	_activateTempNode(PolyNum, Step).
_holds(_id(temp, 2,PolyNum), _nodeInfo(active, yes), Step)
	:-	_activateTempNode(PolyNum, Step).
_holds(_id(temp, 2,PolyNum), _nodeInfo(type, poly), Step)
	:-	_activateTempNode(PolyNum, Step).

% copying over the entire subtree
_clearNode(Root, Step)
					:-	_setResultTo(Root, Step).

_mapResultToLayer(Layer+1, Step)
					:-	_setResultTo(_id(Layer, Num), Step).

% TODO: try mapping entire subtree instead
_mapNode(_id(temp, 2, Num), Layer+1, Step)
					:-	_multiplyPolys(Poly1, Poly2, Step),
						_holds(Poly2, _nodeInfo(numterms, Terms), Step),
						Num = 1..Terms,
						_mapResultToLayer(Layer, Step).
% move children down
% copy subtree, 
% delete subtree, 
% compare subtrees (equality)
% move subtree up


				% Arithmetic Operations

				% multiplying polynomials

% store result in temp node, TODO: use existing predicates to change operator 
_tempRootToAdd(Step)
					:-	_multiplyPolys(Poly, Mono, Step).

% temp root is sum of several standard polynomials
_holds(_id(temp, 1,1), _nodeInfo(type, oper), Step)
					:-	_tempRootToAdd(Step).
_holds(_id(temp, 1,1), _nodeInfo(operation, add), Step)
					:-	_tempRootToAdd(Step).
_holds(_id(temp, 1,1), _nodeInfo(active, yes), Step)
					:-	_tempRootToAdd(Step).
% NOTE: a standard polynomial is created for each monomial of Poly2
_holds(_id(temp, 1,1), _nodeInfo(numchildren, Num), Step)
					:-	_tempRootToAdd(Step),
						_multiplyPolys(Poly1, Poly2, Step),
						_numTerms(Poly2, Num, Steps).
% multiply each pair of monomials
_holds(_id(temp, 2, Deg2+1), _nodeInfo(Deg1 + Deg2, Coeff1 * Coeff2), Step)
					:-	_multiplyPolys(Poly1, Poly2, Step),
						_holds(Poly2, _nodeInfo(Deg2, Coeff2), Step),
						_degree(Deg2),
						_holds(Poly1, _nodeInfo(Deg1, Coeff1), Step),
						_degree(Deg1),
						_coeff(Coeff1 * Coeff2),
						_degree(Deg1 + Deg2),
						not _tempNode(Poly1),
						not _tempNode(Poly2).
% set term count for each polynomial
_holds(_id(temp, 2, Poly), _nodeInfo(numterms, NumMonoms), Step)
					:-	_multiplyPolys(Poly1, Poly2, Step),
						_numTerms(Poly1, NumMonoms, Step),
						_numTerms(Poly2, NumStdPolys, Step),
						Poly = 1..NumStdPolys .



% decide which node to assign children to
_setResultTo(Root, Step)
					:-	_multiplyPolys(Poly, Mono, Step),
						_numSubExpressions(Root, 2, Step),
						_termOf(Root, Poly, Step).
_setResultTo(Poly, Step)
					:-	_multiplyPolys(Poly, Mono, Step),
						_numSubExpressions(Root, Num, Step), Num > 2,
						_termOf(Root, Poly, Step).
% if we've set the result to Poly, then Mono must be deleted
_cancelTerm(Mono, Step)
					:-	_multiplyPolys(Poly, Mono, Step),
						_setResultTo(Poly, Step).

_deleteChildrenOf(Root, Step)
					:-	_setResultTo(Root, Step).


_hasFactors(Poly, DCoeff, ECoeff, Step)
					:-	_isQuadratic(Poly, Step),
						_linearMonom(Poly, BCoeff, Step),
						_constMonom(Poly, CCoeff, Step),
						_coeff(DCoeff),
						_coeff(ECoeff),
						BCoeff == DCoeff + ECoeff,
						CCoeff == DCoeff * ECoeff,
						_coeff(BCoeff),
						_coeff(CCoeff).
_isFactorable(Poly, Step)
				:-	_hasFactors(Poly, DCoeff, ECoeff, Step).
%		factoring a quadratic
1 { _factorsOfPoly(Poly, DCoeff, ECoeff, Step) : _hasFactors(Poly, DCoeff, ECoeff, Step) } 1
					:-	_factorPoly(Poly, Step).
						

% set temp root to product of binomials
% TODO: use existing predicates to convert to mul node!
_tempRootToMul(Step)
					:-	_factorPoly(Poly, Step).

% temp root is sum of several standard polynomials
_holds(_id(temp, 1,1), _nodeInfo(type, oper), Step)
					:-	_factorPoly(Poly, Step).
_holds(_id(temp, 1,1), _nodeInfo(operation, mul), Step)
					:-	_factorPoly(Poly, Step).
_holds(_id(temp, 1,1), _nodeInfo(active, yes), Step)
					:-	_factorPoly(Poly, Step).
_holds(_id(temp, 1,1), _nodeInfo(numchildren, 2), Step)
					:-	_factorPoly(Poly, Step).
_setStdPoly(_id(temp, 2, 1), DCoeff, Step)
					:-	_factorsOfPoly(Poly, ECoeff, DCoeff, Step).
_setStdPoly(_id(temp, 2, 2), ECoeff, Step)
					:-	_factorsOfPoly(Poly, ECoeff, DCoeff, Step).
_holds(Node, _nodeInfo(0, Coeff), Step)
					:-	_setStdPoly(Node, Coeff, Step).
_setToPoly(Node, Step)
					:-	_setStdPoly(Node, Coeff, Step).
_holds(Node, _nodeInfo(1, 1), Step)
					:-	_setToPoly(Node, Step).

_holds(Node, _nodeInfo(type, poly), Step)
					:-	_setToPoly(Node, Step).
_holds(Node, _nodeInfo(active, yes), Step)
					:-	_setToPoly(Node, Step).
_holds(Node, _nodeInfo(numterms, 2), Step)
					:-	_setToPoly(Node, Step).

% set the parent/child pointers
_holds(_id(temp, 1,1), _treeInfo(activechild, _id(temp, 2, ChildNo)), Step)
					:-	_factorPoly(Poly, Step),
						ChildNo = 1..2.
% map the nodes. NOTE: This is a good bit of code to DRY up
_mapNode(_id(temp, 2, ChildNo), Layer+1, Step)
					:-	_factorPoly(Poly, Step),
						_layerOf(Poly, Layer),
						ChildNo = 1..2.
% copy over the factored form
_setResultTo(Poly, Step)
					:-	_factorPoly(Poly, Step).


% copy over all node info as appropriate
_copyNodeInfo(NewNode, OldNode, Step)
					:-	_mapto(OldNode, NewNode, Step).
% copy over parent/child links
_introduce(Root, _treeInfo(activechild, RegNode), Step)
					:-	_mapto(TempNode, RegNode, Step),
						_setResultTo(Root, Step),
						_holds(_id(temp,1,1), _treeInfo(activechild, TempNode), Step).

_copyNodeInfo(Root, _id(temp, 1,1), Step)
					:-	_setResultTo(Root, Step).
_update(Poly, _nodeInfo(2, 1), Step)				% fix this later
					:-	_dividePolyBy(Poly, ACoeff, Step).
#show _mapto/3.
#show _mapNode/3.
#show _setToPoly/2.
#show _setStdPoly/3.
