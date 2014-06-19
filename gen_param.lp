% monomial constants
#const maxAssignableCoeff	=	10.
#const maxCoeff				=	maxAssignableCoeff*2.
#const maxAssignableDegree	=	2.
#const maxDegree			=	maxAssignableDegree*2.

#const maxAssignSquareCoeff		=	5.
#const maxAssignLinearCoeff		=	maxAssignableCoeff.
#const maxAssignConstCoeff		=	maxAssignableCoeff.


_coeff(-1*maxCoeff..maxCoeff).
_degree(0..maxDegree).

% _baseMonom are used to initialize monomial terms
_baseMonom(Coeff, 2)		:-	coeff(Coeff), Coeff < maxAssignSquareCoeff, Coeff >= 0 .
_baseMonom(Coeff, 2)		:-	coeff(Coeff), -1*Coeff < maxAssignSquareCoeff, -1*Coeff >= 0 .
_baseMonom(Coeff, 1)		:-	coeff(Coeff), Coeff < maxAssignLinearCoeff, Coeff >= 0 .
_baseMonom(Coeff, 1)		:-	coeff(Coeff), -1*Coeff < maxAssignLinearCoeff, -1*Coeff >= 0 .
_baseMonom(Coeff, 0)		:-	coeff(Coeff), Coeff < maxAssignConstCoeff, Coeff >= 0 .
_baseMonom(Coeff, 0)		:-	coeff(Coeff), -1*Coeff < maxAssignConstCoeff, -1*Coeff >= 0 .

% monomial definitions
_monomial(Coeff, Deg)		:-	_coeff(Coeff),
								_degree(Deg). 

% generating a polynomial
_hasMonom(Node, 1, _monomial(LeadCoeff, Deg))	:-	_makePolyWithDeg(Node, Deg), 
													_makePolyWithCoeff(Node, LeadCoeff).

% TODO: can be simplified to just select N monomials with a lesser degree than given

_monoType(sameDeg;diffDeg).
1 { _hasMonomType(Node, MonoNum, Type) : _monoType(Type) } 1
											:-	_makePolyWithTerms(Node, NumTerms),
												MonoNum = 2..NumTerms-1.

1 { _hasMonom(Node, MonoNum, _monomial(C,D)) 
	: _baseMonom(C,D), D < PolyDeg } 1	:-	_hasMonoType(Node, MonoNum, diffDeg), _makePolyWithDeg(Node, PolyDeg).

1 { _hasMonom(Node, MonoNum, _monomial(C,D)) 
	: _baseMonom(C,D), C < LeadCoeff , D == PolyDeg} 1	
										:-	_hasMonoType(Node, MonoNum, sameDeg), _makePolyWithDeg(Node, PolyDeg),
											_makePolyWithCoeff(Node, LeadCoeff).



