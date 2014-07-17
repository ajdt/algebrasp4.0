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
_changeOperator(RootFrac, mul, Step)
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
_changeToDiv(RootExpr, LeftFrac, RightFrac, Step)
			:-	_doAction(_action(multFrac, _data(LeftFrac, RightFrac)), Step),
				_termOf(RootExpr, LeftFrac, Step).
_swapTerms(LeftDenom, RightNumer, Step)
			:-	_doAction(_action(multFrac, _data(LeftFrac, RightFrac)), Step),
				_denomOf(LeftFrac, LeftDenom, Step),
				_numerOf(RightFrac, RightNumer, Step).
_changeOperator(LeftFrac, mul, Step)
			:-	_doAction(_action(multFrac, _data(LeftFrac, RightFrac)), Step).
_changeOperator(RightFrac, mul, Step)
			:-	_doAction(_action(multFrac, _data(LeftFrac, RightFrac)), Step).

%================================================================================
% addSameFrac: a/b + c/b --> (a+c)/b
%================================================================================
_applicable(_action(addSameFrac, _data(LeftFrac, RightFrac)), Step)
			:-	_isAdd(FracSum, Step),
				_termOf(FracSum, LeftFrac, Step),
				_termOf(FracSum, RightFrac, Step),
				LeftFrac < RightFrac,
				_isDiv(LeftFrac, Step),
				_isDiv(RightFrac, Step),
				% compare denominators of both fractions
				_denomOf(LeftFrac, LeftDenom, Step),
				_denomOf(RightFrac, RightDenom, Step),
				_equal(LeftDenom, RightDenom, Step).

%	performing action

%	1. generate temp result -- root is a division operation
%	2. numerator is sum of previous numerators
%	3. denom is common denominator from before
_addFrac(LeftFrac, RightFrac, Step)
			:-	_applicable(_action(addSameFrac, _data(LeftFrac, RightFrac)), Step).

:- not action(addSameFrac).
:- action(Name), Name != addSameFrac.
