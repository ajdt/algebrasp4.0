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
_clearNode(FracRoot, Step)
			:-	_doAction(_action(numerSimp, _data(FracRoot)), Step).
_copyNodeInfo(FracRoot, Numer, Step)
			:-	_doAction(_action(numerSimp, _data(FracRoot)), Step),
				_numerOf(FracRoot, Numer, Step).
_deleteNode(Denom, Step)
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

% TODO: actions must be revised, to copy arbitrary subtrees later on
_clearNode(LeftTerm, Step)
			:-	_doAction(_action(factorCommTerm, _data(LeftTerm, RightTerm)), Step).
_deleteNode(RightTerm, Step)
			:-	_doAction(_action(factorCommTerm, _data(LeftTerm, RightTerm)), Step).
_replaceWith(Right, RightTerm, Step)
			:-	_doAction(_action(factorCommTerm, _data(LeftTerm, RightTerm)), Step),
				_termOf(Right, RightTerm, Step).
_clearNode(Copy, Step)
			:-	_replaceWith(Copy, Orig, Step).
_copyNodeInfo(Copy, Orig, Step)
			:-	_replaceWith(Copy, Orig, Step).
% on left side, replace leftTerm with other right side term
_replaceWith(LeftTerm, OtherRightTerm, Step)
			:-	_doAction(_action(factorCommTerm, _data(LeftTerm, RightTerm)), Step),
				_termOf(Right, RightTerm, Step),
				_termOf(Right, OtherRightTerm, Step),
				OtherRightTerm != RightTerm.
% change lhs operation to add
_changeNodeOp(Left, add, Step)
			:-	_doAction(_action(factorCommTerm, _data(LeftTerm, RightTerm)), Step),
				_termOf(Left, LeftTerm, Step).
% change root op to mul
_changeNodeOp(Root, mul, Step)
			:-	_doAction(_action(factorCommTerm, _data(LeftTerm, RightTerm)), Step),
				_termOf(Left, LeftTerm, Step),
				_termOf(Root, Left, Step).

%================================================================================
% distribute (a + b ) * c --> a*c + b*c
%================================================================================
_applicable(_action(distribute, _data(LeftTerm, RightTerm)), Step)
			:-	_isMul(Root, Step),
				_termOf(Root, LeftTerm, Step),
				_termOf(Root, RightTerm, Step),
				LeftTerm != RightTerm,
				_isPolynomial(LeftTerm, Step),
				_isMonomial(RightTerm, Step).

_multiplyPolyWithMonom(LeftTerm, RightTerm, Step)
			:-	_doAction(_action(distribute, _data(LeftTerm, RightTerm)), Step).

:- not action(distribute).
