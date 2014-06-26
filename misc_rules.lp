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
_copyPoly(FracRoot, Numer, Step)
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

:- not action(numerSimp).

