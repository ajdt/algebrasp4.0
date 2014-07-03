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
_nodeOper(delete;deallocate;clear).

_applyNodeOp(Node, Op, Step)
					:-	_applyNodeOpRecursive(Node, Op, Step).
_applyNodeOpRecursive(Child, Op, Step)
					:-	_applyNodeOpRecursive(Node, Op, Step),
						_termOf(Node, Child, Step).

_remove(Node, Info, Step)	% clearing a node
					:-	_applyNodeOp(Node, clear, Step),
						_holds(Node, Info, Step),
						Info != _nodeInfo(active,yes) .

_applyNodeOp(Node, clear, Step)	% deleting a node
					:-	_applyNodeOp(Node, delete, Step).
_applyNodeOp(Node, deallocate, Step)	
					:-	_applyNodeOp(Node, delete, Step).

_deallocated(Node, Step)	% deallocating a node
					:-	_applyNodeOp(Node, deallocate, Step).
_remove(Node, _nodeInfo(active, yes), Step)	
					:-	_applyNodeOp(Node, deallocate, Step).
					%	MISC DELETE PROPERTIES
% deleting a node means to remove all parent pointers, and the entire subtree rooted at that node
_deleteChildReferences(Parent, Child, Step)
					:-	_cancelTerm(Child, Step),	% cancelTerm/2 means term is its own node
						_termOf(Parent, Child, Step).	
% update parent's child count
_update(Parent, _nodeInfo(numchildren, NumKids - 1), Step)
					:-	_deleteChildReferences(Parent, Node, Step),
						_holds(Parent, _nodeInfo(numchildren, NumKids), Step).
% remove parent pointer to child
_remove(Parent, _treeInfo(activechild, Term), Step)
					:-	_deleteChildReferences(Parent, Term, Step).
% 'recursively' delete all children
_applyNodeOp(Child, delete, Step)	% figure out better way to do this
					:-	_deleteChildrenOf(Parent, Step),
						_termOf(Parent, Child, Step).

% deleting a monomial
% 
% NOTE: deleteMonomialOnly does not update numterms; useful if multiple deletes occur 
% leading to multiple updatesto numterms (and a race condition)
_remove(Polynomial, _nodeInfo(Deg, Coeff), Step)
					:-	_deleteMonomial(Polynomial, Deg, Step),
						_degree(Deg), _coeff(Coeff),
						_holds(Polynomial, _nodeInfo(Deg, Coeff), Step).

% update the number of terms
_update(Poly, _nodeInfo(numterms, NumTerms + Delta), Step)
					:-	_changeNumTerms(Poly, Delta, Step),
						Delta <= 5, % TODO: turn these into consts
						Delta >= -5,
						_holds(Poly, _nodeInfo(numterms, NumTerms), Step).

% canceling a term
_deleteMonomial(Poly, Term, Step)		
					:-	_cancelTerm(Poly, Term, Step),
						not _node(Term).
_changeNumTerms(Poly, -1, Step)	% update the number of terms
					:-	_cancelTerm(Poly, Term, Step),
						not _node(Term).

_cancelTerm(Term, Step)	
					:-	_cancelTerm(Expr, Term, Step),
						_node(Term).
_applyNodeOp(Term, delete, Step)	
					:-	_cancelTerm(Term, Step).	% want both versions of cancelTerm for now 


					% Copying a Node
_introduce(Copy, Info, Step)
					:-	_shallowCopy(Copy, Orig, Step),
						_holds(Orig, Info, Step).
_applyNodeOp(Copy, clear, Step)
					:-	_shallowCopy(Copy, Orig, Step).
% copying just nodeInfo
_introduce(Copy, _nodeInfo(X,Y), Step)
					:-	_copyNodeInfo(Copy, Orig, Step),
						_holds(Orig, _nodeInfo(X,Y), Step).
% copying nodeInfo from temp node
_introduce(Copy, _nodeInfo(X,Y), Step)
					:-	_copyNodeInfo(Copy, Orig, Step),
						_tempResult(Orig, _nodeInfo(X,Y), Step).
% swap nodes (nodes become shallow copies of each other)
_shallowCopy(Node1, Node2, Step)
					:-	_swapTerms(Node1, Node2, Step).
_shallowCopy(Node2, Node1, Step)
					:-	_swapTerms(Node1, Node2, Step).


							%				CHANGE NODE OPERATOR
% change node operator
_update(Node, _nodeInfo(operation, Oper), Step)
					:-	_changeOperator(Node, Oper, Step),
						_holds(Node, _nodeInfo(type, oper), Step).

_transformToOper(Node, Oper, Step)
					:-	_changeOperator(Node, Oper, Step),
						not _holds(Node, _nodeInfo(type, oper), Step).

% changing to div requires providing numer and denom fields too
_changeOperator(Node, div, Step)
					:-	_changeToDiv(Node, Numer, Denom, Step).
_introduce(Node, _nodeInfo(numer, Numer), Step)
					:-	_changeToDiv(Node, Numer, Denom, Step).
_introduce(Node, _nodeInfo(denom, Denom), Step)
					:-	_changeToDiv(Node, Numer, Denom, Step).

% removing fractional fields, if necessary
_removeFracFields(Node, Step)
					:-	_changeOperator(Node, Oper, Step),
						_holds(Node, _nodeInfo(operation, div), Step).

_remove(DivNode, _nodeInfo(numer, X), Step)
					:-	_removeFracFields(DivNode, Step),
						_holds(DivNode, _nodeInfo(numer, X), Step).
_remove(DivNode, _nodeInfo(denom, X), Step)
					:-	_removeFracFields(DivNode, Step),
						_holds(DivNode, _nodeInfo(denom, X), Step).

% convert non-operator node to operator
% note: only clears node, doesn't delete any children, doesn't initialize with childcount
_applyNodeOp(Node, clear, Step)
					:-	_transformToOper(Node, Oper, Step).
_introduce(Node, _nodeInfo(type, oper), Step)
					:-	_transformToOper(Node, Oper, Step).
_introduce(Node, _nodeInfo(operation, Oper), Step)
					:-	_transformToOper(Node, Oper, Step).


							%				RULE HELPERS
% setToOne
_deleteChildrenOf(Node, Step)
					:-	_setToOne(Node, Step).
_applyNodeOp(Node, clear, Step)	
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

_applyNodeOp(Term2, delete, Step)
					:-	_groupTerms(Term1, Term2, Step).
_changeOperator(Term1, mul, Step)
					:-	_groupTerms(Term1, Term2, Step).
% initialize new fields for Term1
_introduce(Term1, _nodeInfo(numchildren, 2), Step)
					:-	_changeOperator(Term1, mul, Step).
_introduce(Term1, _treeInfo(activechild, NewTerm), Step)
					:-	_changeOperator(Term1, mul, Step),
						_mapto(Term1, NewTerm, Step).
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

% set parent/child properties for nodes mapped-to 
_introduce(NewNode, _treeInfo(activechild, NewChild), Step)
					:-	_copyMappedSubtree(Node, Step),
						_termOf(Node, Child, Step),
						_mapto(Node, NewNode, Step),
						_mapto(Child, NewChild, Step).

% recursively copy children
_copyMappedSubtree(Child, Step)
					:-	_copyMappedSubtree(Node, Step),
						_termOf(Node, Child, Step).
		% moving a subtree down
_deleteChildrenOf(Node, Step)
					:-	_shiftDownSubtree(Node, Step).
_applyNodeOp(Node, clear, Step)
					:-	_shiftDownSubtree(Node, Step).
% move subtree down, 
_mapNodeRec(Node, Layer + 1, Step)
					:-	_shiftDownSubtree(Node, Step),
						_layerOf(Node, Layer).
% set pointer from old root to new root,
_introduce(Node, _treeInfo(activechild, NewRoot))
					:-	_shiftDownSubtree(Node, Step),
						_mapto(Node, NewRoot, Step).

% copy over all node info as appropriate
_copyNodeInfo(NewNode, OldNode, Step)
					:-	_mapto(OldNode, NewNode, Step).
% copy over parent/child links
_introduce(Root, _treeInfo(activechild, RegNode), Step)
					:-	_mapto(TempNode, RegNode, Step),
						_setResultTo(Root, Step),
						_tempResult(_id(temp,1,1), _treeInfo(activechild, TempNode), Step).

_copyNodeInfo(Root, _id(temp, 1,1), Step)
					:-	_setResultTo(Root, Step).

				% SAVE the result of a binary operation (uses setResultTo)
_setResultTo(Root, Step)	
					:-	_writeBinaryOp(LeftPoly, RightPoly, Step),
						_numSubExpressions(Root, 2, Step),
						_termOf(Root, LeftPoly, Step).
_setResultTo(LeftPoly, Step)
					:-	_writeBinaryOp(LeftPoly, RightPoly, Step),
						_numSubExpressions(Root, Num, Step), Num > 2,
						_termOf(Root, LeftPoly, Step).
% if we've set the result to Poly, then Mono must be deleted
_cancelTerm(RightPoly, Step)
					:-	_writeBinaryOp(LeftPoly, RightPoly, Step),
						_setResultTo(LeftPoly, Step).
_deleteChildrenOf(Root, Step)
					:-	_writeBinaryOp(Root, Step).

					% MULTIPLY POLYNOMIALS 
% setup parent/child pointers
_activateTempNode(PolyNum, Step)
:-	_multiplyPolys(Poly1, Poly2, Step),
	_holds(Poly2, _nodeInfo(numterms, Num), Step),
	PolyNum = 1..Num.

% set basic polynomial properties for node
_tempResult(_id(temp, 1,1), _treeInfo(activechild, _id(temp, 2, PolyNum)), Step)
	:-	_activateTempNode(PolyNum, Step).
_tempResult(_id(temp, 2,PolyNum), _nodeInfo(active, yes), Step)
	:-	_activateTempNode(PolyNum, Step).
_tempResult(_id(temp, 2,PolyNum), _nodeInfo(type, poly), Step)
	:-	_activateTempNode(PolyNum, Step).

% copying over the entire subtree
_applyNodeOp(Root, clear, Step)
					:-	_setResultTo(Root, Step).

_mapResultToLayer(Layer+1, Step)
					:-	_setResultTo(_id(Layer, Num), Step).

% move children down
% copy subtree, 
% delete subtree, 
% compare subtrees (equality)
% move subtree up


				% Setting Temp Operations
_initTempAsOper(Node, Step)				
					:-	_setTempOper(Node, Oper, Step),
						_tempNode(Node).
_tempResult(Node, _nodeInfo(operation, Oper), Step)				
					:-	_setTempOper(Node, Oper, Step),
						_tempNode(Node).
_tempResult(Node, _nodeInfo(type, oper), Step) 
					:-	_initTempAsOper(Node, Step).
_tempResult(Node, _nodeInfo(active, yes), Step) 
					:-	_initTempAsOper(Node, Step).
% setting a temp node to a polynomial
_tempResult(Node, _nodeInfo(type, poly), Step)
					:-	_tempToPoly(Node, Step).
_tempResult(Node, _nodeInfo(active, yes), Step)
					:-	_tempToPoly(Node, Step).
_tempResult(Node, _nodeInfo(active, yes), Step)
					:-	_tempToPoly(Node, Step).

% setting temp node to a binomial
_tempResult(Node, _nodeInfo(0, Coeff), Step)
					:-	_tempToBinomial(Node, Coeff, Step).
_tempResult(Node, _nodeInfo(1, 1), Step)
					:-	_tempToBinomial(Node, Coeff, Step).
_tempToPoly(Node, Step)
					:-	_tempToBinomial(Node, Coeff, Step).

				% Arithmetic Operations

				% multiplying polynomials

% store result in temp node, TODO: use existing predicates to change operator 
_setTempOper(_id(temp, 1,1), add, Step)
					:-	_multiplyPolys(Poly, Mono, Step).

% NOTE: a standard polynomial is created for each monomial of Poly2
_tempResult(_id(temp, 1,1), _nodeInfo(numchildren, Num), Step)
					:-	_multiplyPolys(Poly1, Poly2, Step),
						_numTerms(Poly2, Num, Steps).
% multiply each pair of monomials
_tempResult(_id(temp, 2, Deg2+1), _nodeInfo(Deg1 + Deg2, Coeff1 * Coeff2), Step)
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
_tempResult(_id(temp, 2, Poly), _nodeInfo(numterms, NumMonoms), Step)
					:-	_multiplyPolys(Poly1, Poly2, Step),
						_numTerms(Poly1, NumMonoms, Step),
						_numTerms(Poly2, NumStdPolys, Step),
						Poly = 1..NumStdPolys .


% TODO: try mapping entire subtree instead
_mapNode(_id(temp, 2, Num), Layer+1, Step)
					:-	_multiplyPolys(Poly1, Poly2, Step),
						_holds(Poly2, _nodeInfo(numterms, Terms), Step),
						Num = 1..Terms,
						_mapResultToLayer(Layer, Step).

% save teh resutl of polynom multiplication
_writeBinaryOp(Poly, Mono, Step)
					:-	_multiplyPolys(Poly, Mono, Step).

% factoring version 1
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
_setTempOper(_id(temp, 1,1), mul, Step)
					:-	_factorPoly(Poly, Step).
_tempResult(_id(temp, 1,1), _nodeInfo(numchildren, 2), Step)
					:-	_factorPoly(Poly, Step).

% set two temp nodes to be the first deg binomials of factored form 
_tempToBinomial(_id(temp, 2, 1), DCoeff, Step)
					:-	_factorsOfPoly(Poly, ECoeff, DCoeff, Step).
_tempToBinomial(_id(temp, 2, 2), ECoeff, Step)
					:-	_factorsOfPoly(Poly, ECoeff, DCoeff, Step).

% set the parent/child pointers
_tempResult(_id(temp, 1,1), _treeInfo(activechild, _id(temp, 2, ChildNo)), Step)
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

% dividing by leading coeff
_setTempOper(_id(temp, 1,1), mul, Step)
					:-	_divideByLeadingCoeff(Poly, Step).
_tempToPoly(_id(temp, 2,1), Step)
					:-	_divideByLeadingCoeff(Poly, Step).
_tempToPoly(_id(temp, 2,2), Step)
					:-	_divideByLeadingCoeff(Poly, Step).

_tempResult(_id(temp, 2,2), _nodeInfo(Deg, Coeff/ACoeff), Step)
					:-	_divideByLeadingCoeff(Poly, Step),
						_holds(Poly, _nodeInfo(Deg, Coeff), Step),
						_degree(Deg), _coeff(Coeff),
						_squareMonom(Poly, ACoeff, Step),
						_coeff(ACoeff),
						_coeff(Coeff/ACoeff).
_tempResult(_id(temp, 2,1), _nodeInfo(0, ACoeff), Step)
					:-	_divideByLeadingCoeff(Poly, Step),
						_squareMonom(Poly, ACoeff, Step),
						_coeff(ACoeff).
_tempResult(_id(temp, 1,1), _nodeInfo(activechild, _id(temp, 2, 1)), Step)
					:-	_divideByLeadingCoeff(Poly, Step).
_tempResult(_id(temp, 1,1), _nodeInfo(activechild, _id(temp, 2, 2)), Step)
					:-	_divideByLeadingCoeff(Poly, Step).

%% set num terms for each case
%_tempResult(_id(temp, 2,2), _nodeInfo(numterms, Num), Step)
%					:-	_divideByLeadingCoeff(Poly, Step),
%						_holds(Poly, _nodeInfo(numterms, Num), Step).
%_tempResult(_id(temp, 2,1), _nodeInfo(numterms, 1), Step)
%					:-	_divideByLeadingCoeff(Poly, Step).
%% TODO: this won't work, fix it
_setResultTo(Poly, Step)
					:-	_divideByLeadingCoeff(Poly, Step).



					%	Add Terms
_tempToPoly(_id(temp, 1,1), Step)
					:-	_addTerms(LeftPoly, RightPoly, Step).
_tempResult(_id(temp, 1, 1), _nodeInfo(Deg, Coeff1 + Coeff2), Step)
					:-	_addTerms(LeftPoly, RightPoly, Step),
						_holds(LeftPoly, _nodeInfo(Deg, Coeff1), Step),
						_holds(RightPoly, _nodeInfo(Deg, Coeff2), Step),
						_degree(Deg),
						_coeff(Coeff1 + Coeff2).

% incorporate monomials that don't have a common term
_tempResult(_id(temp, 1, 1), _nodeInfo(Deg, Coeff), Step)
					:-	_addTerms(LeftPoly, RightPoly, Step),
						_holds(LeftPoly, _nodeInfo(Deg, Coeff), Step),
						not	_hasTermWithDeg(RightPoly, Deg, Step),
						_degree(Deg),
						_coeff(Coeff).
_tempResult(_id(temp, 1, 1), _nodeInfo(Deg, Coeff), Step)
					:-	_addTerms(LeftPoly, RightPoly, Step),
						_holds(RightPoly, _nodeInfo(Deg, Coeff), Step),
						not	_hasTermWithDeg(LeftPoly, Deg, Step),
						_degree(Deg),
						_coeff(Coeff).

% count numterms
_commonTerm(Deg, Step)
					:-	_addTerms(LeftPoly, RightPoly, Step),
						_holds(LeftPoly, _nodeInfo(Deg, Coeff1), Step),
						_holds(RightPoly, _nodeInfo(Deg, Coeff2), Step),
						_degree(Deg),
						_coeff(Coeff1 + Coeff2).
% initialize count
_commonTermCount(0, 0, Step)	:-	_step(Step), not _commonTerm(0, Step),
						_addTerms(LeftPoly, RightPoly, Step).
_commonTermCount(0, 1, Step)	:-	_step(Step), _commonTerm(0, Step),
						_addTerms(LeftPoly, RightPoly, Step).

% iterate to get successive counts
 _commonTermCount(Deg+1, Count+1, Step)
 					:-	_commonTermCount(Deg, Count, Step),
						_degree(Deg+1),
						_commonTerm(Deg+1, Step).
 _commonTermCount(Deg+1, Count, Step)
 					:-	_commonTermCount(Deg, Count, Step),
						_degree(Deg+1),
						not _commonTerm(Deg, Step).
% finally record the number of terms in the resultant polynomial
_tempResult(_id(temp, 1, 1), _nodeInfo(numterms, LeftTotal + RightTotal - Count), Step)
					:-	_addTerms(LeftPoly, RightPoly, Step),
						_holds(LeftPoly, _nodeInfo(numterms, LeftTotal), Step),
						_holds(RightPoly, _nodeInfo(numterms, RightTotal), Step),
						_commonTermCount(maxDegree, Count, Step).

% save the result
_writeBinaryOp(LeftPoly, RightPoly, Step)
					:-	_addTerms(LeftPoly, RightPoly, Step).

#show _mapto/3.
#show _mapNode/3.
#show _tempToPoly/2.
#show _tempToBinomial/3.
