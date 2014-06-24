%================================================================================
% fracCancel: a*c/b*c --> a/b
%================================================================================

_applicable(_action(fracCancel, _data(NumerC, DenomC)), Step)
			:-	_isDiv(Frac, Step),
				_numerOf(Frac, Numer, Step),
				_denomOf(Frac, Denom, Step),
				_isMul(Numer, Step),
				_isMul(Denom, Step),
				_termOf(Numer, NumerC, Step),
				_termOf(Denom, DenomC, Step),
				_equal(NumerC, DenomC, Step).
%	performing action
_cancelTerm(NumerC, Step)
			:-	_doAction(_action(fracCancel, _data(NumerC, DenomC)), Step).
_cancelTerm(DenomC, Step)
			:-	_doAction(_action(fracCancel, _data(NumerC, DenomC)), Step).
%	rule features

%================================================================================
% fracDiv: a/c / b/c --> a/b
%================================================================================
_applicable(_action(fracDiv, _data(RootFrac, DenomFrac)), Step)
			:-	_isDiv(RootFrac, Step),
				_numerOf(RootFrac, NumerFrac, Step),
				_denomOf(RootFrac, DenomFrac, Step),
				_isDiv(NumerFrac, Step),
				_isDiv(DenomFrac, Step).

%	performing action
_swapNumerDenom(DenomFrac, Step)
			:-	_doAction(_action(fracDiv, _data(RootFrac, DenomFrac)), Step).
_convertDivToMul(RootFrac, Step)
			:-	_doAction(_action(fracDiv, _data(RootFrac, DenomFrac)), Step).


%================================================================================
% multFrac: a/b * c/d --> (a*c)/(b*d)
%================================================================================
_applicable(_action(multFrac, _data(LeftFrac, RightFrac)), Step)
			:-	_isMul(RootMul, Step),
				_isDiv(LeftFrac, Step),
				_isDiv(RightFrac, Step),
				_termOf(RootMul, LeftFrac, Step),
				_termOf(RootMul, RightFrac, Step),
				LeftFrac < RightFrac,
				_numSubExpressions(RootMul, 2, Step).

%	performing action
_mulToDiv(RootExpr, LeftFrac, RightFrac, Step)
			:-	_doAction(_action(multFrac, _data(LeftFrac, RightFrac)), Step),
				_termOf(RootExpr, LeftFrac, Step).
_swapTerms(LeftDenom, RightNumer, Step)
			:-	_doAction(_action(multFrac, _data(LeftFrac, RightFrac)), Step),
				_denomOf(LeftFrac, LeftDenom, Step),
				_numerOf(RightFrac, RightNumer, Step).
_convertDivToMul(LeftFrac, Step)
			:-	_doAction(_action(multFrac, _data(LeftFrac, RightFrac)), Step).
_convertDivToMul(RightFrac, Step)
			:-	_doAction(_action(multFrac, _data(LeftFrac, RightFrac)), Step).
:- not action(multFrac).
:- action(Name), Name != multFrac.
