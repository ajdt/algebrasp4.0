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
% pick a monomial at random from set of base monomials
1 { _hasMonom(Node, Num, _monomial(C,D)) : _baseMonom(C,D) } 1 
			:-	_makePolyWithTerms(Node, NumTerms), Num = 1..NumTerms.

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%% POLYNOMIAL PROPERTIES %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
_polyTerm(Poly, Mono, Step)	:-	_holds(Poly, _nodeInfo(monom, Mono), Step).
_isPolynomial(Poly, Step)	:-	_holds(Poly, _nodeInfo(type, poly), Step).
_isMonomial(Poly, Step)	:-	_holds(Poly, _nodeInfo(numterms, 1), Step).
_isBinomial(Poly, Step)	:-	_holds(Poly, _nodeInfo(numterms, 2), Step).
_isTrinomial(Poly, Step)	:-	_holds(Poly, _nodeInfo(numterms, 3), Step).

_hasTermWithDeg(Poly, Deg, Step)	:-	_holds(Poly, _nodeInfo(mono, _monoInfo(Num, _monomial(Coeff, Deg))), Step),
										Coeff != 0.
_hasHighDegreeTerms(Poly, Step)	:-	_holds(Poly, _nodeInfo(mono, _monoInfo(Num, _monomial(Coeff, Deg))), Step),
										Coeff != 0, Deg > 3.

_isZero(Poly, Step)	:-	_isMonomial(Poly, Step),
						_holds(Poly, _nodeInfo(monom, Mono), Step),
						_isZeroMonomial(Mono).

_isOne(Poly, Step)	:-	_isMonomial(Poly, Step),
						_holds(Poly, _nodeInfo(monom, Mono), Step),
						_isUnitMonomial(Mono).
_isConst(Poly, Step)	:-	_isMonomial(Poly, Step),
						_holds(Poly, _nodeInfo(mono, Mono), Step),
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

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%% DEFINED POLYNOMIAL CONSTANTS %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
_introduce(Node, _nodeInfo(type, poly), Step)
							:-	_setToUnitPoly(Node, Step).
_introduce(Node, _nodeInfo(numterms, 1), Step)
							:-	_setToUnitPoly(Node, Step).
_introduce(Node, _nodeInfo(monom, _monomial(1,0)), Step)
							:-	_setToUnitPoly(Node, Step).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%% POLYNOMS EQUALITY %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
_unequal(Poly1, Poly2, Step)
							:-	_holds(Poly1, _nodeInfo(monom, Monom), Step),
								_holds(Poly2, _nodeInfo(type, poly), Step),
								not _holds(Poly2, _nodeInfo(monom, Monom), Step).
_unequal(Poly2, Poly1, Step)
							:-	_unequal(Poly1, Poly2, Step).
_equal(Poly1, Poly2, Step)
							:-	_holds(Poly1, _nodeInfo(type, poly), Step),
								_holds(Poly2, _nodeInfo(type, poly), Step),
								Poly1 != Poly2,
								not _unequal(Poly1, Poly2, Step).
