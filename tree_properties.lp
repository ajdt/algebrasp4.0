#const tempRoot	= _id(temp,1,1).
%================================================================================
% 			OPERATOR PROPERTIES
%================================================================================

_isMul(Node, Step)	:-	_holds(Node, _nodeInfo(operation, mul), Step).
_isAdd(Node, Step)	:-	_holds(Node, _nodeInfo(operation, add), Step).
_isDiv(Node, Step)	:-	_holds(Node, _nodeInfo(operation, div), Step).
_isOper(Node, Step)	:-	_holds(Node, _nodeInfo(type, oper), Step).

_numSubExpressions(Node, NumKids, Step)	
					:-	_holds(Node, _nodeInfo(numchildren, NumKids), Step).
_termOf(Parent, Child, Step)	
					:-	_holds(Parent, _treeInfo(activechild, Child), Step),
						_validChild(Parent, Child).
_numerOf(Fraction, Numer, Step)
					:-	_holds(Fraction, _nodeInfo(numer, Numer), Step).
_denomOf(Fraction, Denom, Step)
					:-	_holds(Fraction, _nodeInfo(denom, Denom), Step).

% predicates to check if operator's children are all polynomials (leaves)
_hasNonPolynomialChild(Node, Step)
					:-	_node(Node), 
						_step(Step),
						_isOper(Node, Step),
						_termOf(Node, Child, Step),
						not _isPolynomial(Child, Step).
_allChildrenArePolynoms(Node, Step)
					:-	_node(Node), 
						_step(Step),
						_isOper(Node, Step),
						not _hasNonPolynomialChild(Node, Step).

%================================================================================
% 			NODE OPERATIONS
%================================================================================
_nodeOper(delete;deallocate;clear).

_applyNodeOp(Node, Op, Step)
					:-	_applyNodeOpRecursive(Node, Op, Step).
_applyNodeOpRecursive(Child, Op, Step)
					:-	_applyNodeOpRecursive(Node, Op, Step),
						_termOf(Node, Child, Step).

% applying the operations
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
%================================================================================
% 			MISC DELETE PROPERTIES
%================================================================================
% canceling a term
_applyNodeOp(Term, delete, Step)	
					:-	_cancelTerm(Term, Step).	% want both versions of cancelTerm for now (arity 2 and 3)
_cancelTerm(Term, Step)	
					:-	_cancelTerm(Expr, Term, Step),
						_node(Term).

_deleteMonomial(Poly, Term, Step)					% cancelTerm also means removing a monomterm from polynom
					:-	_cancelTerm(Poly, Term, Step),
						not _node(Term).

% canceling a term depends on number of children its parent has
% case "2 children" : we replace parent with it's other child
% case "3 or more children" : just cancel the desired term

_cancelChildReplaceParent(Child, Step)
					:-	_cancelTerm(Child, Step),
						_termOf(Parent, Child, Step),
						_numSubExpressions(Parent, 2, Step).
_cancelChildOnly(Child, Step)
					:-	_cancelTerm(Child, Step),
						_termOf(Parent, Child, Step),
						_numSubExpressions(Parent, NumKids, Step), NumKids > 2.
% deleting a node means to remove all parent pointers, and the entire subtree rooted at that node
_deleteChildReferences(Parent, Child, Step)
					:-	_cancelChildOnly(Child, Step),	% cancelTerm/2 means term is its own node
						_termOf(Parent, Child, Step).	
% update parent's child count
_update(Parent, _nodeInfo(numchildren, NumKids - 1), Step)
					:-	_deleteChildReferences(Parent, Node, Step),
						_holds(Parent, _nodeInfo(numchildren, NumKids), Step).
% remove parent pointer to child
_remove(Parent, _treeInfo(activechild, Term), Step)
					:-	_deleteChildReferences(Parent, Term, Step).

% deleting a monomial
_remove(Polynomial, _nodeInfo(Deg, Coeff), Step)
					:-	_deleteMonomial(Polynomial, Deg, Step),
						_degree(Deg), _coeff(Coeff),
						_holds(Polynomial, _nodeInfo(Deg, Coeff), Step).

% 'recursively' delete all children
_applyNodeOp(Child, delete, Step)	% figure out better way to do this
					:-	_deleteChildrenOf(Parent, Step),
						_termOf(Parent, Child, Step).
% cancelling the child and replacing the parent node
_applyNodeOp(Parent, clear, Step)
					:-	_cancelChildReplaceParent(Child, Step),
						_termOf(Parent, Child, Step).
_shallowCopy(Parent, OtherChild, Step)
					:-	_cancelChildReplaceParent(Child, Step),
						_termOf(Parent, Child, Step),
						_termOf(Parent, OtherChild, Step),
						OtherChild != Child .


%================================================================================
% 			COPYING A NODE
%================================================================================
% NOTE: shallowCopy copies both data and pointers, copyNodeInfo copies
%		only _nodeInfo data
_applyNodeOp(Copy, clear, Step)
					:-	_shallowCopy(Copy, Orig, Step).
_copyChildPtrs(Copy, Orig, Step)
					:-	_shallowCopy(Copy, Orig, Step).
_copyNodeInfo(Copy, Orig, Step)
					:-	_shallowCopy(Copy, Orig, Step).
% copying just child pointers
_introduce(Copy, _treeInfo(activechild, Child), Step)
					:-	_copyChildPtrs(Copy, Orig, Step),
						_termOf(Orig, Child, Step).
% copying just nodeInfo
_introduce(Copy, _nodeInfo(X,Y), Step)
					:-	_copyNodeInfo(Copy, Orig, Step),
						_holds(Orig, _nodeInfo(X,Y), Step),
						_degree(X), _coeff(Y),
						|-Y| <= maxCoeff.	
_introduce(Copy, _nodeInfo(X,Y), Step)
					:-	_copyNodeInfo(Copy, Orig, Step),
						_holds(Orig, _nodeInfo(X,Y), Step),
						not _degree(X).
% copying nodeInfo from temp node
_introduce(Copy, _nodeInfo(X,Y), Step)
					:-	_copyNodeInfo(Copy, Orig, Step),
						_tempResult(Orig, _nodeInfo(X,Y), Step),
						_degree(X), _coeff(Y),
						|-Y| <= maxCoeff.	% TODO: find out why grounding yields coefficients that are beyond preset bounds
_introduce(Copy, _nodeInfo(X,Y), Step)
					:-	_copyNodeInfo(Copy, Orig, Step),
						_tempResult(Orig, _nodeInfo(X,Y), Step),
						not _degree(X). 

% swap nodes (nodes become shallow copies of each other)
_shallowCopy(Node1, Node2, Step)
					:-	_swapTerms(Node1, Node2, Step).
_shallowCopy(Node2, Node1, Step)
					:-	_swapTerms(Node1, Node2, Step).

%================================================================================
% 			CHANGE OPERATOR TYPE
%================================================================================
_update(Node, _nodeInfo(operation, Oper), Step)
					:-	_changeOperator(Node, Oper, Step),
						_isOper(Node, Step).

_transformToOper(Node, Oper, Step)
					:-	_changeOperator(Node, Oper, Step),
						not _isOper(Node, Step).

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
						_isDiv(Node, Step).

% if changing a div operator, remove fractional fields
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


%================================================================================
%				RULE HELPERS
%================================================================================
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
%================================================================================
% 			NODE ALLOCATION
%================================================================================
% NOTE: mapNodeRec just maps a subtree
%		copyMappedSubtree will copy a subtree that has been mapped, to a new tree

	%%%% mapping a subtree or a temp subtree %%%%
_mapNodeRec(Child, Layer+1, Step)
					:-	_mapNodeRec(Node, Layer, Step),
						_termOf(Node, Child, Step),
						_layer(Layer),
						_node(Node),
						_step(Step).

_mapNodeRec(Child, Layer+1, Step)	% separate version for mpaping temp node subtrees
					:-	_mapNodeRec(Node, Layer, Step),
						_tempResult(Node, _treeInfo(activechild, Child), Step),
						_layer(Layer),
						_node(Node),
						_step(Step).
_mapNode(Node, Layer, Step)
					:-	_mapNodeRec(Node, Layer, Step).

	%%%% copying a mapped subtree %%%%
_copyNodeInfo(NewNode, OldNode, Step)
					:-	_mapto(OldNode, NewNode, Step).

% copy pointers
_copyMappedSubtree(Child, Step)		
					:-	_copyMappedSubtree(Node, Step),
						_termOf(Node, Child, Step).
% set parent/child properties for nodes mapped-to 
_introduce(NewNode, _treeInfo(activechild, NewChild), Step)
					:-	_copyMappedSubtree(Node, Step),
						_termOf(Node, Child, Step),
						_mapto(Node, NewNode, Step),
						_mapto(Child, NewChild, Step).
_introduce(NewNode, _treeInfo(activechild, NewChild), Step)
					:-	_copyMappedSubtree(Node, Step),
						_tempResult(Node, _treeInfo(activechild, Child), Step),
						_mapto(Node, NewNode, Step),
						_mapto(Child, NewChild, Step).

	%%%% moving a subtree down %%%%
_applyNodeOp(Node, clear, Step)
					:-	_shiftDownSubtree(Node, Step).
_deleteChildrenOf(Node, Step)
					:-	_shiftDownSubtree(Node, Step).
% map subtree to next layer
_mapNodeRec(Node, Layer + 1, Step)
					:-	_shiftDownSubtree(Node, Step),
						_layerOf(Node, Layer).

	%%%% setting results (saving a temp result) %%%%
% setResultTo() indicates what node to set temp result to (always rooted at _id(temp,1,1) )

% NOTE: all shallow copying for mapped-to nodes is handled elsewhere
_introduce(Root, _treeInfo(activechild, RegNode), Step)
					:-	_mapto(TempNode, RegNode, Step),
						_setResultTo(Root, Step),
						_tempResult(_id(temp,1,1), _treeInfo(activechild, TempNode), Step).

_copyNodeInfo(Root, _id(temp, 1,1), Step)
					:-	_setResultTo(Root, Step).

_applyNodeOpRecursive(Root, delete, Step)
					:-	_setResultTo(Root, Step).
%_applyNodeOpRecursive(Root, delete, Step)	% want to delete entire subtree
_mapNodeRec(Child, Layer+1, Step)	% this is incorrect.
					:-	_setResultTo(_id(Layer, Num), Step),
						_tempResult(_id(temp, 1,1), _treeInfo(activechild, Child), Step).

#show _mapNodeRec/3. % todo: ensure temp,1,1 is mapped to at most one node
#show _mapto/3.
#show _multiplyPolys/3.
%------------------------------ 
	%%%% SAVE the result of a binary operation (uses setResultTo) %%%%
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
% map the temp subtree
_mapto(_id(temp,1,1), Root, Step)
					:-	_setResultTo(Root, Step),
						_tempResult(_id(temp,1,1), _treeInfo(activechild, TempNode), Step).
_mapNodeRec(_id(temp,1,1), Layer, Step)
					:-	_setResultTo(_id(Layer,Num), Step).
					

%================================================================================
% 			SETTING TEMP OPERATIONS
%================================================================================
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

% copying: polynomial to temp node
_tempResult(TempNode, _nodeInfo(Field,Value), Step)
					:-	_copyPolyToTemp(TempNode, Poly, Step),
						_holds(Poly, _nodeInfo(Field,Value), Step),
						_degree(Field).
_setTempToPoly(TempNode, Step)
					:-	_copyPolyToTemp(TempNode, Poly, Step).
_tempResult(TempNode, _nodeInfo(type, poly), Step)
					:-	_setTempToPoly(TempNode, Step).
_tempResult(TempNode, _nodeInfo(active, yes), Step)
					:-	_setTempToPoly(TempNode, Step).

% setting a node to child
_tempResult(Parent, _treeInfo(activechild, Child), Step)
				:-	_setTempChild(Parent, Child, Step).

% setting num children for  a temp Node
_tempResult(TempNode, _nodeInfo(numchildren, ChildCount), Step)
					:-	_setTempNumChildren(TempNode, ChildCount, Step).

% setting temp node to a binomial
_tempResult(Node, _nodeInfo(0, Coeff), Step)
					:-	_tempToBinomial(Node, Coeff, Step).
_tempResult(Node, _nodeInfo(1, 1), Step)
					:-	_tempToBinomial(Node, Coeff, Step).
_tempToPoly(Node, Step)
					:-	_tempToBinomial(Node, Coeff, Step).

				%%%% Arithmetic Operations %%%%

				% ADDING FRACTIONS (SAME DENOM)
% 0. isolate the two fraction terms
_rightFraction(RightFrac, Step)
					:-	_addFrac(LeftFrac, RightFrac, Step).
_leftFraction(LeftFrac, Step)
					:-	_addFrac(LeftFrac, RightFrac, Step).

% 1. set right fraction c/b to just 'b' term
_deleteChildrenOf(RightFrac, Step)
					:-	_rightFraction(RightFrac, Step).
_applyNodeOp(RightFrac, clear, Step)
					:-	_rightFraction(RightFrac, Step).
_copyNodeInfo(RightFrac, BTerm, Step)
					:-	_rightFraction(RightFrac, Step),
						_denomOf(RightFrac, BTerm, Step).
% 2. convert root to div node and add numer/denom fields
_changeToDiv(Root, RightFrac, LeftFrac, Step)
					:-	_rightFraction(RightFrac, Step),
						_leftFraction(LeftFrac, Step),
						_termOf(Root, RightFrac, Step).
% 3. convert left fraction into sum of a and c
_update(LeftFrac, _nodeInfo(operation, add), Step)
					:-	_leftFraction(LeftFrac, Step).
_removeFracFields(LeftFrac, Step)
					:-	_leftFraction(LeftFrac, Step).
% 4. replace left frac's denom with copy of c term
_replaceLeftDenomWithRightNum(LeftDenom, Step)
					:-	_leftFraction(LeftFrac, Step),
						_denomOf(LeftFrac, LeftDenom, Step).

_applyNodeOp(LeftDenom, clear, Step)
					:-	_replaceLeftDenomWithRightNum(LeftDenom, Step).
_copyNodeInfo(LeftDenom, RightNumer, Step)
					:-	_replaceLeftDenomWithRightNum(LeftDenom, Step),
						_rightFraction(RightFrac, Step),
						_numerOf(RightFrac, RightNumer, Step).

				% ADDING FRACTIONS (DIFFERENT DENOM)
% 0. isolate the two fraction terms
_rightDiffFraction(RightFrac, Step)
					:-	_addDiffFrac(LeftFrac, RightFrac, Step).
_leftDiffFraction(LeftFrac, Step)
					:-	_addDiffFrac(LeftFrac, RightFrac, Step).

% 1. set right fraction to (d * c)
_changeOperator(RightFrac, mul, Step)
					:-	_rightDiffFraction(RightFrac, Step).
_applyNodeOp(RightNumer, clear, Step)	% clear numerator and replace it with CTerm
					:-	_rightDiffFraction(RightFrac, Step),
						_numerOf(RightFrac, RightNumer, Step).
_copyNodeInfo(RightNumer, CTerm, Step)
					:-	_rightDiffFraction(RightFrac, Step),
						_numerOf(RightFrac, RightNumer, Step),
						_leftDiffFraction(LeftFrac, Step),
						_denomOf(LeftFrac, CTerm, Step).
% TODO: remove frac fields here and wherever necessary (create separate frac fields thingy)

% 2. convert root to div node and add numer/denom fields
_changeToDiv(Root, RightFrac, LeftFrac, Step)
					:-	_addDiffFrac(LeftFrac, RightFrac, Step),
						_termOf(Root, RightFrac, Step).
%% 3. clear left fraction, set temp result to left fraction
_setResultTo(LeftFrac, Step)
				:-	_leftDiffFraction(LeftFrac, Step).
%% 4. set temp result to (a*d + b*c)
_setTempOper(_id(temp,1,1), add, Step)
					:-	_action(addDiffFrac, Step). 
	% set children
_setTempChild(_id(temp,1,1), _id(temp,2,1), Step)
					:-	_action(addDiffFrac, Step). 
_setTempChild(_id(temp,1,1), _id(temp,2,2), Step)
					:-	_action(addDiffFrac, Step). 

% populate children with proper values
% TODO: refactor this, it's too complex and you'll likely end up reusing the code anyway
% left child is a*d
_setTempOper(_id(temp,2,1), mul, Step)
					:-	_action(addDiffFrac, Step). 
_setTempChild(_id(temp,2,1), _id(temp,3,1), Step)
					:-	_action(addDiffFrac, Step). 
_setTempChild(_id(temp,2,1), _id(temp,3,2), Step)
					:-	_action(addDiffFrac, Step). 
% copy over a and d nodes
_copyPolyToTemp(_id(temp,3,1), LeftNumer, Step)
					:-	_leftDiffFraction(LeftFrac, Step),
						_numerOf(LeftFrac, LeftNumer, Step). 
_copyPolyToTemp(_id(temp,3,2), RightDenom, Step)
					:-	_rightDiffFraction(RightFrac, Step),
						_denomOf(RightFrac, RightDenom, Step). 

% right child is b*c
_setTempOper(_id(temp,2,2), mul, Step)
					:-	_action(addDiffFrac, Step). 
_setTempChild(_id(temp,2,2), _id(temp,3,3), Step)
					:-	_action(addDiffFrac, Step). 
_setTempChild(_id(temp,2,2), _id(temp,3,4), Step)
					:-	_action(addDiffFrac, Step). 
% copy over b and c nodes
_copyPolyToTemp(_id(temp,3,3), LeftDenom, Step)
					:-	_leftDiffFraction(LeftFrac, Step),
						_denomOf(LeftFrac, LeftDenom, Step). 
_copyPolyToTemp(_id(temp,3,4), RightNumer, Step)
					:-	_rightDiffFraction(RightFrac, Step),
						_numerOf(RightFrac, RightNumer, Step). 
% TODO: change so setResultTo initiates copying
_copyMappedSubtree(_id(temp,2,1), Step)
					:-	_action(addDiffFrac, Step).
_copyMappedSubtree(_id(temp,2,2), Step)
					:-	_action(addDiffFrac, Step).

				% multiplying polynomials

% isolate the two operands (makes some groundings smaller
_multipliedPoly(Poly1, Step) 
					:-	_multiplyPolys(Poly1, Poly2, Step).
_multiplier(Poly2, Step) 
					:-	_multiplyPolys(Poly1, Poly2, Step).
% generate one polynomial for each monom term of multiplier
% TODO: warning, second layer must have enough nodes to deal with these polynomials
_setTempToPoly(_id(temp, 2,Deg+1), Step)
:-	_multiplier(Poly2, Step),
	_hasTermWithDeg(Poly2, Deg, Step).

% result is a sum of polynomials, so set root node to 'add' operator
_setTempChild(tempRoot, PolyChild, Step)
	:-	_setTempToPoly(PolyChild, Step).
_setTempOper(tempRoot, add, Step)
					:-	_multiplier(Poly2, Step).

% NOTE: a standard polynomial is created for each monomial of Poly2
% TODO: polySize only defined for polynomials with 3 terms or fewer!
_tempResult(tempRoot, _nodeInfo(numchildren, Size), Step)
					:-	_multiplier(Poly2, Step),
						_polySize(Poly2, Size, Step).

% multiply each pair of monomials
% each poly/coeff pair of Poly2 will become a separate standard poly
_multTermsWith(_id(temp, 2, Deg2+1), Coeff2, Step)
					:-	_multiplier(Poly2, Step),
						_holds(Poly2, _nodeInfo(Deg2, Coeff2), Step),
						_degree(Deg2), _coeff(Coeff2),
						not _tempNode(Poly2).
% multiply each assigned Poly1 term from above with the corresponding monomial
% recall: NodeNum corresponds to degree of multiplier (see multTermsWith above)
_tempResult(_id(temp, 2, NodeNum), _nodeInfo(Deg + NodeNum - 1, Coeff * Multiplier), Step)
					:-	_multipliedPoly(Poly1, Step),
						_holds(Poly1, _nodeInfo(Deg, Coeff), Step),
						_degree(Deg), _coeff(Coeff),
						_multTermsWith(_id(temp, 2, NodeNum), Multiplier, Step).


% save the result of polynom multiplication
_writeBinaryOp(Poly1, Poly2, Step)
					:-	_multiplyPolys(Poly1, Poly2, Step),
						not _isMonomial(Poly2, Step).

% if multiplying by a monomial, then result is a single
% polynomial not a sum of polynomials
_copyNodeInfo(Parent, TempNode, Step) 
					:-	_multiplier(Poly2, Step),
						_isMonomial(Poly2, Step),
						_termOf(Parent, Poly2, Step),
						_setTempToPoly(TempNode, Step).



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
						
% set temp root to product of two binomials
_setTempOper(_id(temp, 1,1), mul, Step)
					:-	_factorPoly(Poly, Step).
_setTempNumChildren(tempRoot, 2, Step)
					:-	_factorPoly(Poly, Step).

% set two temp nodes to be the first deg binomials of factored form 
_tempToBinomial(_id(temp, 2, 1), DCoeff, Step)
					:-	_factorsOfPoly(Poly, ECoeff, DCoeff, Step).
_tempToBinomial(_id(temp, 2, 2), ECoeff, Step)
					:-	_factorsOfPoly(Poly, ECoeff, DCoeff, Step).

% set the parent/child pointers
_tempResult(tempRoot, _treeInfo(activechild, _id(temp, 2, ChildNo)), Step)
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
_setTempOper(tempRoot, mul, Step)
					:-	_divideByLeadingCoeff(Poly, Step).
_tempToPoly(_id(temp, 2,1), Step)
					:-	_divideByLeadingCoeff(Poly, Step).
_tempToPoly(_id(temp, 2,2), Step)
					:-	_divideByLeadingCoeff(Poly, Step).

				% TODO: Restore this later
				%_tempResult(_id(temp, 2,2), _nodeInfo(Deg, Coeff/ACoeff), Step)
				%	:-	_divideByLeadingCoeff(Poly, Step),
				%		_holds(Poly, _nodeInfo(Deg, Coeff), Step),
				%		_degree(Deg), _coeff(Coeff),
				%		_squareMonom(Poly, ACoeff, Step),
				%		ACoeff != 0,
				%		_coeff(ACoeff),
				%		_coeff(Coeff/ACoeff).
_tempResult(_id(temp, 2,1), _nodeInfo(0, ACoeff), Step)
					:-	_divideByLeadingCoeff(Poly, Step),
						_squareMonom(Poly, ACoeff, Step),
						_coeff(ACoeff).
_tempResult(tempRoot, _treeInfo(activechild, _id(temp, 2, 1)), Step)
					:-	_divideByLeadingCoeff(Poly, Step).
_tempResult(tempRoot, _treeInfo(activechild, _id(temp, 2, 2)), Step)
					:-	_divideByLeadingCoeff(Poly, Step).

%% TODO: this won't work, fix it
_setResultTo(Poly, Step)
					:-	_divideByLeadingCoeff(Poly, Step).



					%	Add Terms
_tempToPoly(tempRoot, Step)
					:-	_addTerms(LeftPoly, RightPoly, Step).
_tempResult(tempRoot, _nodeInfo(Deg, Coeff1 + Coeff2), Step)
					:-	_addTerms(LeftPoly, RightPoly, Step),
						_holds(LeftPoly, _nodeInfo(Deg, Coeff1), Step),
						_holds(RightPoly, _nodeInfo(Deg, Coeff2), Step),
						_degree(Deg),
						_coeff(Coeff1 + Coeff2).

% incorporate monomials that don't have a common term
_tempResult(tempRoot, _nodeInfo(Deg, Coeff), Step)
					:-	_addTerms(LeftPoly, RightPoly, Step),
						_holds(LeftPoly, _nodeInfo(Deg, Coeff), Step),
						not	_hasTermWithDeg(RightPoly, Deg, Step),
						_degree(Deg),
						_coeff(Coeff).
_tempResult(tempRoot, _nodeInfo(Deg, Coeff), Step)
					:-	_addTerms(LeftPoly, RightPoly, Step),
						_holds(RightPoly, _nodeInfo(Deg, Coeff), Step),
						not	_hasTermWithDeg(LeftPoly, Deg, Step),
						_degree(Deg),
						_coeff(Coeff).

% a common term exists
_commonTerm(Deg, Step)
					:-	_addTerms(LeftPoly, RightPoly, Step),
						_holds(LeftPoly, _nodeInfo(Deg, Coeff1), Step),
						_holds(RightPoly, _nodeInfo(Deg, Coeff2), Step),
						_degree(Deg),
						_coeff(Coeff1 + Coeff2).

% save the result
_writeBinaryOp(LeftPoly, RightPoly, Step)
					:-	_addTerms(LeftPoly, RightPoly, Step).

#show _mapto/3.
#show _mapNode/3.
#show _tempToPoly/2.
#show _tempToBinomial/3.
