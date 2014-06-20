%================================================================================
% swap terms
%================================================================================
_applicable(_action(swap, _data(Term1, Term2)), Step)	
			:-	_termOf(Expr, Term1, Step),
				_termOf(Expr, Term2, Step),
				Term1 != Term2.

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
				_isZero(ZeroTerm, Step).

_applicable(_action(addIdent, _data(Poly, ZeroTerm)), Step)
			:-	_isPolynomial(Poly, Step),
				_polyTerm(Poly, ZeroTerm, Step),
				_isZeroMonomial(ZeroTerm).

_cancelTerm(Plus, ZeroTerm, Step) 
			:-	_doAction(_action(addIdent, _data(Plus, ZeroTerm)), Step).

% TODO: delete this, only for debugging purposes
:- not action(addIdent).
