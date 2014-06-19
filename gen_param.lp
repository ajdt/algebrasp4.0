% monomial constants
#const maxAssignableCoeff	=	10.
#const maxCoeff				=	maxAssignableCoeff*2.
#const maxAssignableDegree	=	3.
#const maxDegree			=	maxAssignableDegree*2.

#const maxAssignSquareCoeff		=	5.
#const maxAssignLinearCoeff		=	maxAssignableCoeff.
#const maxAssignConstCoeff		=	maxAssignableCoeff.

% polynomial constants
% maxTerms


% just use constants, don't define facts?
_coeff(-1*maxCoeff..maxCoeff).

% degree
_degree(0..maxDegree).

% monomial definitions
_monomial(Coeff, Deg)		:-	_coeff(Coeff),
								_degree(Deg). 

_hasMonom(Node, _monomial(LeadCoeff, Deg))	:-	_makePolyWithDeg(Node, Deg), 
													_makePolyWithCoeff(Node, LeadCoeff).

% TODO: can be simplified to just select N monomials with a lesser degree than given

_monoType(sameDeg;diffDeg).
1 { _hasMonomType(Node, MonoNum, Type) : _monoType(Type) } 1
											:-	_makePolyWithTerms(Node, NumTerms),
												MonoNum = 2..NumTerms-1.

1 { _hasMonom(Node, _monomial(C,D)) 
	: _monomial(C,D), D < PolyDeg } 1	:-	_hasMonoType(Node, MonoNum, diffDeg), _makePolyWithDeg(Node, PolyDeg).

1 { _hasMonom(Node, _monomial(C,D)) 
	: _monomial(C,D), C < LeadCoeff , D == PolyDeg} 1	
										:-	_hasMonoType(Node, MonoNum, sameDeg), _makePolyWithDeg(Node, PolyDeg),
											_makePolyWithCoeff(Node, LeadCoeff).

% move this to test file??
:-	_makePoly(Node, NumTerms), 
	not NumTerms { _hasMonom(Node, _monomial(C,D)) : _monomial(C,D) } NumTerms.


