%================================================================================
% group terms
%================================================================================
% NOTE: this rule will only be applied by other rules
%_applicable(_action(group, _data(Term1, Term2)), Step)
%			:-	_isMul(Parent, Step),
%				_termOf(Parent, Term1, Step),
%				_termOf(Parent, Term2, Step),
%				_isPolynomial(Term1, Step),
%				_isPolynomial(Term2, Step),
%				Term1 != Term2, 
%				_numSubExpressions(Parent, NumTerms, Step),	
%				NumTerms > 2.


_groupTerms(Term1, Term2, Step)
			:-	_doAction(_action(group, _data(Term1, Term2)), Step).

%================================================================================
% ignore denominator: a / b = 0 --> a = 0
%================================================================================

_applicable(_action(numerSimp, _data(left_side)), Step)
			:-	_isZero(right_side, Step),
				_isDiv(left_side, Step),
				_numerOf(left_side, Numer, Step), % TODO: remove these last two constraints when rule can handle arbitrary subexpr
				_denomOf(left_side, Denom, Step), 
				_isPolynomial(Denom, Step),
				_isPolynomial(Numer, Step).

% assumes that fraction is poly/poly
_applyNodeOp(FracRoot, clear, Step)
			:-	_doAction(_action(numerSimp, _data(FracRoot)), Step).
_copyNodeInfo(FracRoot, Numer, Step)
			:-	_doAction(_action(numerSimp, _data(FracRoot)), Step),
				_numerOf(FracRoot, Numer, Step).
_applyNodeOp(Denom, delete, Step)
			:-	_doAction(_action(numerSimp, _data(FracRoot)), Step),
				_denomOf(FracRoot, Denom, Step).
			% features for rule
ruleParam(numerSimp, numerSize, 0) 
			:-	_doAction(_action(numerSimp, _data(FracRoot)), Step),
				_numerOf(FracRoot, Numer, Step),
				_isMonomial(Numer, Step).
ruleParam(numerSimp, numerSize, 1) 
			:-	_doAction(_action(numerSimp, _data(FracRoot)), Step),
				_numerOf(FracRoot, Numer, Step),
				_isBinomial(Numer, Step).

%================================================================================
% factorCommTerm:	(ac + bc ) --> (a + b) * c
%================================================================================
_applicable(_action(factorCommTerm, _data(LeftTerm, RightTerm)), Step)
			:-	_isAdd(Root, Step),
				_numSubExpressions(Root, 2, Step),
				_termOf(Root, Left, Step),
				_termOf(Root, Right, Step),
				Left < Right,
				_isMul(Left, Step),
				_isMul(Right, Step),
				_termOf(Left, LeftTerm, Step),
				_termOf(Right, RightTerm, Step),
				_equal(LeftTerm, RightTerm, Step),
				% TODO: make rule more general and remove these conditions later on
				_numSubExpressions(Left, 2, Step),
				_numSubExpressions(Right, 2, Step),
				_isPolynomial(LeftTerm, Step),
				_isPolynomial(RightTerm, Step).

% isolate terms
_leftTerm(LeftTerm, Step)	:-	_doAction(_action(factorCommTerm, _data(LeftTerm, RightTerm)), Step).
_rightTerm(RightTerm, Step)	:-	_doAction(_action(factorCommTerm, _data(LeftTerm, RightTerm)), Step).
_otherRightTerm(OtherRightTerm, Step)
							:-	_rightTerm(RightTerm, Step),
								_termOf(Right, RightTerm, Step),
								_termOf(Right, OtherRightTerm, Step),
								RightTerm != OtherRightTerm.
% TODO: actions must be revised, to copy arbitrary subtrees later on
_applyNodeOp(LeftTerm, clear, Step)
			:-	_leftTerm(LeftTerm, Step).
_applyNodeOp(RightTerm, delete, Step)
			:-	_rightTerm(RightTerm, Step).
_replaceWith(Right, RightTerm, Step)
			:-	_rightTerm(RightTerm, Step),
				_termOf(Right, RightTerm, Step).
% on left side, replace leftTerm with other right side term
_replaceWith(LeftTerm, OtherRightTerm, Step)
			:-	_leftTerm(LeftTerm, Step),
				_otherRightTerm(OtherRightTerm, Step).

_applyNodeOp(Copy, clear, Step)
			:-	_replaceWith(Copy, Orig, Step).
_copyNodeInfo(Copy, Orig, Step)
			:-	_replaceWith(Copy, Orig, Step).

% change lhs operation to add
_changeOperator(Left, add, Step)
			:-	_leftTerm(LeftTerm, Step),
				_termOf(Left, LeftTerm, Step).
% change root op to mul
_changeOperator(Root, mul, Step)
			:-	_leftTerm(LeftTerm, Step),
				_termOf(Left, LeftTerm, Step),
				_termOf(Root, Left, Step).

%================================================================================
% distribute (a + b ) * c --> a*c + b*c
%================================================================================
_applicable(_action(distribute, _data(LeftTerm, RightTerm)), Step)
			:-	_isMul(Root, Step),
				_termOf(Root, LeftTerm, Step),
				_termOf(Root, RightTerm, Step),
				_polySize(LeftTerm, 2, Step),	% temporary restriction used for testing
				_polySize(RightTerm, 2, Step),
				LeftTerm != RightTerm,
				_isPolynomial(LeftTerm, Step),
				_isPolynomial(RightTerm, Step).

_multiplyPolys(LeftTerm, RightTerm, Step)
			:-	_doAction(_action(distribute, _data(LeftTerm, RightTerm)), Step).

% features for the rule
ruleParam(distribute, prodsize, 0) 
			:-	_doAction(_action(distribute, _data(LeftTerm, RightTerm)), Step),
				_termOf(Parent, LeftTerm, Step),
				_numSubExpressions(Parent, 2, Step).
ruleParam(distribute, prodsize, 1) 
			:-	_doAction(_action(distribute, _data(LeftTerm, RightTerm)), Step),
				_termOf(Parent, LeftTerm, Step),
				_numSubExpressions(Parent, Num, Step), Num > 2.
ruleParam(distribute, polysize, Num) 
			:-	_doAction(_action(distribute, _data(LeftTerm, RightTerm)), Step),
				_polySize(LeftTerm, Num, Step).
ruleParam(distribute, degree, 2) 
			:-	_doAction(_action(distribute, _data(LeftTerm, RightTerm)), Step),
				_isQuadratic(LeftTerm).
ruleParam(distribute, degree, 1) 
			:-	_doAction(_action(distribute, _data(LeftTerm, RightTerm)), Step),
				_isLinear(LeftTerm).
ruleParam(distribute, degree, 0) 
			:-	_doAction(_action(distribute, _data(LeftTerm, RightTerm)), Step),
				_isLinear(LeftTerm),
				_isLinear(RightTerm).

%================================================================================
% factor (ax^2 + bx + c) --> (x + e) * (x + d)
%================================================================================
_applicable(_action(factor, _data(Poly)), Step)
			:-	_isQuadratic(Poly, Step),
				_squareMonom(Poly, ACoeff, Step),
				_isFactorable(Poly, Step),
				ACoeff == 1,
				ACoeff <=5,
				ACoeff >= - 5,
				_linearMonom(Poly, BCoeff, Step),
				BCoeff <=5,
				BCoeff >= - 5,
				_constMonom(Poly, CCoeff, Step),
				CCoeff <=5,
				CCoeff >= - 5.
_applicable(_action(factor2, _data(Poly, divideFirst)), Step)
			:-	_quadWithCommonTerm(Poly, Step).

_factorPoly(Poly, Step)
			:-	_doAction(_action(factor, _data(Poly)), Step),
				_squareMonom(Poly, ACoeff, Step),
				ACoeff == 1.
_divideByLeadingCoeff(Poly, Step)
			:-	_doAction(_action(factor, _data(Poly, divideFirst)), Step).
% TODO: create a separate predicate for this
_factorNext(StdPoly, Step+1)
			:-	_divideByLeadingCoeff(Poly, Step),
				_termOf(Poly, StdPoly, Step+1),
				_isQuadratic(StdPoly, Step+1).
				%_isFactorable(StdPoly, Step+1).
%
_doAction(_action(factor, _data(Poly)), Step)
			:-	_factorNext(Poly, Step),
				_step(Step).
_applicable(_action(factor, _data(Poly)), Step)
			:-	_factorNext(Poly, Step),
				_step(Step).
% rule features -- 
% 	perfect square, factor out const, b term is zero?, c term is zero?
#show _divideByLeadingCoeff/2.
#show _tempResult/3.
#show _mapto/3.
#show _mapNodeRec/3.
#show _setResultTo/2.
#show _copyNodeInfo/3.
#show _factorNext/2.
#show _termOf/3.
#show _isQuadratic/2.
#show _isFactorable/2.
#show _hasFactors/4.
#show _applicable/2.
#show _isZero/2.
#show _isMonomial/2.
#show _setTempOper/3.
#show _initTempAsOper/2.
#show _tempNode/1.
#show _introduce/3.
%:- not action(factor).
%:- action(Name), Name != factor2.
% TODO: remove this
%:- _step(Step), not _isMonomial(right_side, Step).
