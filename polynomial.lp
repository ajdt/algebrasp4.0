% Armando Diaz Tolentino <ajdt@cs.washington.edu> 
% 
% This file defines monomials, generates polynomials, and contains useful
% predicates relating to monomials
%
% expected interface: 
%	monomial(Coefficient, Degree)
%	baseMonomial(Coeff, Degree)
%	
%	Polynomials: isMonomial(Node), isConstant(Node), isZero(Node), isOne(Node),
%				isQuadratic(Node), isBinomial(Node), isLinear(Node)

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%% MONOMIAL DEFINITIONS %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
_coeff(-1*maxCoeff..maxCoeff).
_degree(0..maxDegree).

% _baseMonom are used to initialize polynomials, they're a subset of allowable monomials
_baseMonom(Coeff, 2)		:-	_coeff(Coeff), Coeff < maxAssignSquareCoeff, Coeff >= 0 .
_baseMonom(Coeff, 2)		:-	_coeff(Coeff), -1*Coeff < maxAssignSquareCoeff, -1*Coeff >= 0 .
_baseMonom(Coeff, 1)		:-	_coeff(Coeff), Coeff < maxAssignLinearCoeff, Coeff >= 0 .
_baseMonom(Coeff, 1)		:-	_coeff(Coeff), -1*Coeff < maxAssignLinearCoeff, -1*Coeff >= 0 .
_baseMonom(Coeff, 0)		:-	_coeff(Coeff), Coeff < maxAssignConstCoeff, Coeff >= 0 .
_baseMonom(Coeff, 0)		:-	_coeff(Coeff), -1*Coeff < maxAssignConstCoeff, -1*Coeff >= 0 .

% monomial definitions
_monomial(Coeff, Deg)		:-	_coeff(Coeff),
								_degree(Deg). 

% monomial properties
_isZeroMonomial(_monomial(0, Deg))		:-	_monomial(0, Deg).
_isUnitMonomial(_monomial(1, Deg))		:-	_monomial(1, Deg).
_isConstMonomial(_monomial(Coeff, 0))	:-	_monomial(Coeff, 0).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%% GENERATING POLYNOMIALS %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% generate a polynomial given the leading coefficient and degree of polynomial

_hasMonom(Node, 1, _monomial(LeadCoeff, Deg))	:-	_makePolyWithDeg(Node, Deg), 
													_makePolyWithCoeff(Node, LeadCoeff).

% ensures successive monoms have a lesser degree or lesser coefficient to the leading monomial
_monoType(sameDeg;diffDeg).

% generate a number for each monomial to be generated
1 { _hasMonomType(Node, MonoNum, Type) : _monoType(Type) } 1
											:-	_makePolyWithTerms(Node, NumTerms),
												MonoNum = 2..NumTerms-1.

% generate monomial of lesser degree than leading term
1 { _hasMonom(Node, MonoNum, _monomial(C,D)) 
	: _baseMonom(C,D), D < PolyDeg } 1	:-	_hasMonomType(Node, MonoNum, diffDeg), _makePolyWithDeg(Node, PolyDeg).

% generate monomial of elsser coefficient than leading term
1 { _hasMonom(Node, MonoNum, _monomial(C,D)) 
	: _baseMonom(C,D), C < LeadCoeff , D == PolyDeg} 1	
										:-	_hasMonomType(Node, MonoNum, sameDeg), _makePolyWithDeg(Node, PolyDeg),
											_makePolyWithCoeff(Node, LeadCoeff).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%% POLYNOMIAL PROPERTIES %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
_isMonomial(Poly, Step)	:-	_holds(Poly, _nodeInfo(numterms, 1), Step).
_isBinomial(Poly, Step)	:-	_holds(Poly, _nodeInfo(numterms, 2), Step).
_isTrinomial(Poly, Step)	:-	_holds(Poly, _nodeInfo(numterms, 3), Step).

_hasTermWithDeg(Poly, Deg, Step)	:-	_holds(Poly, _nodeInfo(mono, _monoInfo(Num, _monomial(Coeff, Deg))), Step),
										Coeff != 0.
_hasHighDegreeTerms(Poly, Step)	:-	_holds(Poly, _nodeInfo(mono, _monoInfo(Num, _monomial(Coeff, Deg))), Step),
										Coeff != 0, Deg > 3.

_isZero(Poly, Step)	:-	_isMonomial(Poly, Step),
						_holds(Poly, _nodeInfo(mono, _monoInfo(1, Mono))),
						_isZeroMonomial(Mono).

_isOne(Poly, Step)	:-	_isMonomial(Poly, Step),
						_holds(Poly, _nodeInfo(mono, _monoInfo(1, Mono))),
						_isUnitMonomial(Mono).
_isConst(Poly, Step)	:-	_isMonomial(Poly, Step),
						_holds(Poly, _nodeInfo(mono, _monoInfo(1, Mono))),
						_isConstMonomial(Mono).

% XXX: assumes max assignable degree is 3
_isQuadratic(Poly, Step)	:-	not _hasHighDegreeTerms(Poly, Step),
								not _hasTermWithDeg(Poly, 3, Step),
								_hasTermWithDeg(Poly, 2, Step).
								
_isLinear(Poly, Step)		:-	not _hasHighDegreeTerms(Poly, Step),
								not _hasTermWithDeg(Poly, 3, Step),
								not _hasTermWithDeg(Poly, 2, Step),
								_hasTermWithDeg(Poly, 1, Step).

_isZeroDegree(Poly, Step)	:-	not _hasHighDegreeTerms(Poly, Step),
								not _hasTermWithDeg(Poly, 3, Step),
								not _hasTermWithDeg(Poly, 2, Step),
								not _hasTermWithDeg(Poly, 1, Step),
								_hasTermWithDeg(Poly, 0, Step).
