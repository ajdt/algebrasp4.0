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
_multipliedTerm(Deg, Coeff, Step)
					:-	_multipliedPoly(Poly1, Step),
						_holds(Poly1, _nodeInfo(Deg, Coeff), Step),
						_degree(Deg), _coeff(Coeff),
						|Coeff| <= maxAssignableCoeff.
_tempResult(_id(temp, 2, NodeNum), _nodeInfo(Deg + NodeNum - 1, Coeff * Multiplier), Step)
					:-	_multipliedTerm(Deg, Coeff, Step),
						_coeff(Multiplier),
						|Multiplier| <= maxAssignableCoeff, % XXX: won't allow two multiplications exceeding bounds
						_coeff(Coeff * Multiplier),
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

% save the result
_writeBinaryOp(LeftPoly, RightPoly, Step)
					:-	_addTerms(LeftPoly, RightPoly, Step).

#show _mapto/3.
#show _mapNode/3.
#show _tempToPoly/2.
#show _tempToBinomial/3.
