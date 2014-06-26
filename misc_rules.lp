%================================================================================
% group terms
%================================================================================
_applicable(_action(group, _data(Term1, Term2)), Step)
			:-	_isMul(Parent, Step),
				_termOf(Parent, Term1, Step),
				_termOf(Parent, Term2, Step),
				_isPolynomial(Term1, Step),
				_isPolynomial(Term2, Step),
				Term1 != Term2, 
				_numSubExpressions(Parent, NumTerms, Step),	
				NumTerms > 2.


_groupTerms(Term1, Term2, Step)
			:-	_doAction(_action(group, _data(Term1, Term2)), Step).
:- not action(group).
