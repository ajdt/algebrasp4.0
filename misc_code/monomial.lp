%
% Armando Diaz Tolentino <ajdt@cs.washington.edu> 
% 
% This file contains legacy monomial definitions no longer used,
% but may become useful in the future
%

% monomial definitions
_monomial(Coeff, Deg)		:-	_coeff(Coeff),
								_degree(Deg). 

% monomial properties
_isZeroMonomial(_monomial(0, Deg))		:-	_monomial(0, Deg).
_isUnitMonomial(_monomial(1, Deg))		:-	_monomial(1, Deg).
_isConstMonomial(_monomial(Coeff, 0))	:-	_monomial(Coeff, 0).
