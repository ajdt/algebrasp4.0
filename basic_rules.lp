%================================================================================
% swap terms
%================================================================================
% Don't want solver to use this rule except as a subrecipe
%_applicable(_action(swap, _data(Term1, Term2)), Step)	
%			:-	_termOf(Expr, Term1, Step),
%				_termOf(Expr, Term2, Step),
%				Term1 != Term2.

% no features for this, it's a pretty straightfoward rule (not difficult)
%probParam(group, num_grouped, StopIndex - StartIndex)	
%			:-	_doAction(_action(group, _data(Plus, StartIndex, StopIndex))).

_swapTerms(Term1, Term2, Step)
			:-	_doAction(_action(swap, _data(Term1, Term2)), Step).


%================================================================================
% divIdentity: A / A ----> 1
%================================================================================

_applicable(_action(divIdent, _data(Div)), Step)
			:-	_isDiv(Div, Step),
				_numerOf(Div, Numer, Step),
				_denomOf(Div, Denom, Step),
				not _isZero(Denom, Step),
				_equal(Numer, Denom, Step).


_setToOne(Fraction, Step) 
			:-	_doAction(_action(divIdent, _data(Fraction)), Step).
% problem parameters
ruleParam(divIdent, cancelType, 0) 
			:-	_doAction(_action(divIdent, _data(Fraction)), Step),
				_numerOf(Div, Numer, Step),
				_isPolynomial(Numer, Step).
ruleParam(divIdent, cancelType, 1) 
			:-	_doAction(_action(divIdent, _data(Fraction)), Step),
				_numerOf(Div, Numer, Step),
				not _isPolynomial(Numer, Step).
%================================================================================
% addCommonTerms: a*x^b + c*x^b ----> (a+c)*x^b
%================================================================================
% contains as a special case:		addIdentity: a*x^b + 0 ----> a*x^b 

_applicable(_action(addCommTerms, _data(LeftPoly, RightPoly)), Step)
			:-	_isAdd(Root, Step),
				_termOf(Root, LeftPoly, Step),
				_termOf(Root, RightPoly, Step),
				_isPolynomial(LeftPoly, Step),
				_isPolynomial(RightPoly, Step),
				LeftPoly != RightPoly.


% Rule application: if either term is zero, then we just cancel the term
_addTerms(LeftPoly, RightPoly, Step)
			:-	_doAction(_action(addCommTerms, _data(LeftPoly, RightPoly)), Step),
				not _isZero(RightPoly, Step),
				not _isZero(LeftPoly, Step).
_cancelTerm(Plus, LeftPoly, Step) 
			:-	_doAction(_action(addCommTerms, _data(LeftPoly, RightPoly)), Step),
				_termOf(Plus, LeftPoly, Step),
				_isZero(LeftPoly, Step).
_cancelTerm(Plus, RightPoly, Step) 
			:-	_doAction(_action(addCommTerms, _data(LeftPoly, RightPoly)), Step),
				not _isZero(LeftPoly, Step),		% want @ most one cancellation
				_termOf(Plus, RightPoly, Step),
				_isZero(RightPoly, Step).

% problem parameters
ruleParam(addCommTerms, identityTerm, 0) 
			:-	_cancelTerm(Plus, ZeroTerm, Step).
ruleParam(addCommTerms, identityTerm, 1) 
			:-	_addTerms(LeftPoly, RightPoly, Step).

ruleParam(addCommTerms, polynomsSize, 0) 
			:-	_doAction(_action(addCommTerms, _data(LeftPoly, RightPoly)), Step),
				_isMonomial(LeftPoly, Step),
				_isMonomial(RightPoly, Step).
ruleParam(addCommTerms, polynomsSize, 1) 
			:-	_doAction(_action(addCommTerms, _data(LeftPoly, RightPoly)), Step),
				_isMonomial(LeftPoly, Step),
				not _isMonomial(RightPoly, Step).
ruleParam(addCommTerms, polynomsSize, 2) 
			:-	_doAction(_action(addCommTerms, _data(LeftPoly, RightPoly)), Step),
				not _isMonomial(LeftPoly, Step),
				_isMonomial(RightPoly, Step).
ruleParam(addCommTerms, polynomsSize, 2) 
			:-	_doAction(_action(addCommTerms, _data(LeftPoly, RightPoly)), Step),
				not _isMonomial(LeftPoly, Step),
				not _isMonomial(RightPoly, Step).
