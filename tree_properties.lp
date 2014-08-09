#include "rule_helpers.lp".
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

% deleting a monomial means creating fresh polynomial without the 'deleted' term
_allocatePolyToNode(PolyNode, Step)
	:-	_deleteMonomial(PolyNode, Deg, Step).
_copyPolyExceptDeletedMonom(NewPoly, OldPoly, Deg, Step)
					:-	_assignPolyToNode(NewPoly, Node, Step),
						_holds(Node, _nodeInfo(polynom, OldPoly), Step),
						_deleteMonomial(Node, Deg, Step).
_addTermToNewPoly(NewPoly, PolyDeg, PolyCoeff, Step)
					:-	_copyPolyExceptDeletedMonom(NewPoly, OldPoly, Deg, Step),
						_holds(OldPoly, _polyInfo(PolyDeg, PolyCoeff), Step),
						PolyDeg != Deg.

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
						Orig != Copy,
						_holds(Orig, _nodeInfo(X,Y), Step).
% copying nodeInfo from temp node
_introduce(Copy, _nodeInfo(X,Y), Step)
					:-	_copyNodeInfo(Copy, Orig, Step),
						Orig != Copy,
						_tempResult(Orig, _nodeInfo(X,Y), Step).

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
% 			SETTING TEMP NODE OPERATIONS
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

% copying: polynomial to temp node
_tempResult(TempNode, _nodeInfo(polynom,Poly), Step)
					:-	_copyPolyToTemp(TempNode, PolyNode, Step),
						_holds(PolyNode, _nodeInfo(polynom,Poly), Step).
% setting temp node to poly (no terms)
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
_allocatePolyToNode(Node, Step)
					:-	_tempToBinomial(Node, Coeff, Step).
					
_addTermToNewPoly(Polynom, 0, Coeff, Step)			
					:-	_tempToBinomial(Node, Coeff, Step),
						_assignPolyToNode(Polynom, Node, Step).
_addTermToNewPoly(Polynom, 1, 1, Step)			
					:-	_tempToBinomial(Node, Coeff, Step),
						_assignPolyToNode(Polynom, Node, Step).

