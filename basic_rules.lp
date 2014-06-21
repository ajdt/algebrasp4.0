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
% addIdentity: a*x^b + 0 ----> a*x^b 
%================================================================================

_applicable(_action(addIdent, _data(Plus, ZeroTerm)), Step)
			:-	_isAdd(Plus, Step),
				_termOf(Plus, ZeroTerm, Step),
				_numSubExpressions(Plus, Num, Step), Num >= 2,
				_isZero(ZeroTerm, Step).

_applicable(_action(addIdent, _data(Poly, ZeroTerm)), Step)
			:-	_isPolynomial(Poly, Step),
				_polyTerm(Poly, ZeroTerm, Step),
				not _isMonomial(Poly, Step),
				_isZeroMonomial(ZeroTerm).

_cancelTerm(Plus, ZeroTerm, Step) 
			:-	_doAction(_action(addIdent, _data(Plus, ZeroTerm)), Step).

%================================================================================
% multIdentity: a*x^b * 1 ----> a*x^b 
%================================================================================

_applicable(_action(mulIdent, _data(Mul, UnitTerm)), Step)
			:-	_isMul(Mul, Step),
				_termOf(Mul, UnitTerm, Step),
				_numSubExpressions(Mul, Num, Step), Num >= 2,
				_isOne(UnitTerm, Step).


_cancelTerm(Mul, UnitTerm, Step) 
			:-	_doAction(_action(mulIdent, _data(Mul, UnitTerm)), Step).
% problem parameters
ruleParam(mulIdent, exprSize, 0) 
			:-	_doAction(_action(mulIdent, _data(Mul, UnitTerm)), Step),
				_numSubExpressions(Mul, 2, Step).
ruleParam(mulIdent, exprSize, 1) 
			:-	_doAction(_action(mulIdent, _data(Mul, UnitTerm)), Step),
				_numSubExpressions(Mul, Num, Step), Num > 2.

%================================================================================
% divIdentity: A / A ----> 1
%================================================================================

_applicable(_action(divIdent, _data(Div)), Step)
			:-	_isDiv(Div, Step),
				_numerOf(Div, Numer, Step),
				_denomOf(Div, Denom, Step),
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
% TODO: delete this, only for debugging purposes
%:- not action(divIdent).
%:- action(addIdent).
%:- action(mulIdent).
