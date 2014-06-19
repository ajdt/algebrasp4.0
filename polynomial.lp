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
_baseMonom(Coeff, 2)		:-	coeff(Coeff), Coeff < maxAssignSquareCoeff, Coeff >= 0 .
_baseMonom(Coeff, 2)		:-	coeff(Coeff), -1*Coeff < maxAssignSquareCoeff, -1*Coeff >= 0 .
_baseMonom(Coeff, 1)		:-	coeff(Coeff), Coeff < maxAssignLinearCoeff, Coeff >= 0 .
_baseMonom(Coeff, 1)		:-	coeff(Coeff), -1*Coeff < maxAssignLinearCoeff, -1*Coeff >= 0 .
_baseMonom(Coeff, 0)		:-	coeff(Coeff), Coeff < maxAssignConstCoeff, Coeff >= 0 .
_baseMonom(Coeff, 0)		:-	coeff(Coeff), -1*Coeff < maxAssignConstCoeff, -1*Coeff >= 0 .

% monomial definitions
_monomial(Coeff, Deg)		:-	_coeff(Coeff),
								_degree(Deg). 

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
	: _baseMonom(C,D), D < PolyDeg } 1	:-	_hasMonoType(Node, MonoNum, diffDeg), _makePolyWithDeg(Node, PolyDeg).

% generate monomial of elsser coefficient than leading term
1 { _hasMonom(Node, MonoNum, _monomial(C,D)) 
	: _baseMonom(C,D), C < LeadCoeff , D == PolyDeg} 1	
										:-	_hasMonoType(Node, MonoNum, sameDeg), _makePolyWithDeg(Node, PolyDeg),
											_makePolyWithCoeff(Node, LeadCoeff).


