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


:- not action(fracDiv).
