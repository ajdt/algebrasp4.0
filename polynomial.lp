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
%_sameDegree(_monomial(Coeff1, Deg), _monomial(Coeff2, Deg)) 			% unnecessary??
%							:-	_monomial(Coeff1, Deg),
%								_monomial(Coeff2, Deg).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%% GENERATING POLYNOMIALS %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% pick a monomial at random from set of base monomials
1 { _hasMonom(Node, Num, _monomial(C,D)) : _baseMonom(C,D) } 1 
			:-	_makePolyWithTerms(Node, NumTerms), Num = 1..NumTerms.

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%% POLYNOMIAL PROPERTIES %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
_sameDegree(Poly, Term1, Term2, Step)
							:-	_holds(Poly, _nodeInfo(degof(Term1), _degree(Deg)), Step),
								_holds(Poly, _nodeInfo(degof(Term2), _degree(Deg)), Step),
								Term1 < Term2. % note all predicates that provide a set of polynomials will list the smallest first

_polyTerm(Poly, Term, Step)	:-	_holds(Poly, _nodeInfo(numterms, Num), Step),
								_numPolyTerms(Term),
								Term <= Num.
_isPolynomial(Poly, Step)	:-	_holds(Poly, _nodeInfo(type, poly), Step).
_isMonomial(Poly, Step)	:-	_holds(Poly, _nodeInfo(numterms, 1), Step).
_isBinomial(Poly, Step)	:-	_holds(Poly, _nodeInfo(numterms, 2), Step).
_isTrinomial(Poly, Step)	:-	_holds(Poly, _nodeInfo(numterms, 3), Step).

_hasTermWithDeg(Poly, Deg, Step)	:-	_holds(Poly, _nodeInfo(degof(Term), _degree(Deg)), Step),
										_holds(Poly, _nodeInfo(coeffof(Term), _coeff(Coeff)), Step),
										Coeff != 0.
_hasHighDegreeTerms(Poly, Step)	:-	_hasTermWithDeg(Poly, Deg, Step),
									Deg > 3.

_isZero(Poly, Step)	:-	_isMonomial(Poly, Step),
						_holds(Poly, _nodeInfo(coeffof(Term), _coeff(0)), Step). % remove _isZeroMonomial?

_isOne(Poly, Step)	:-	_isMonomial(Poly, Step),
						_holds(Poly, _nodeInfo(coeffof(Term), _coeff(1)), Step), % remove _isUnitMonomial?
						_holds(Poly, _nodeInfo(degof(Term), _degree(0)), Step). 
_isConst(Poly, Step)	:-	_isMonomial(Poly, Step),
						_holds(Poly, _nodeInfo(degof(Term), _degree(0)), Step). % remove _isConstMonomial?

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
_introduce(Node, _nodeInfo(coeffof(1), _coeff(1)), Step)
							:-	_setToUnitPoly(Node, Step).
_introduce(Node, _nodeInfo(degof(1), _degree(0)), Step)
							:-	_setToUnitPoly(Node, Step).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%% POLYNOMS EQUALITY %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% when two polynomials have the same value for a term
_equalOnTerm(Poly1, Poly2, Term, Step)
							:-	_holds(Poly1, _nodeInfo(coeffof(Term), _coeff(Coeff)), Step),
								_holds(Poly1, _nodeInfo(degof(Term), _degree(Deg)), Step),
								_holds(Poly2, _nodeInfo(coeffof(Term), _coeff(Coeff)), Step),
								_holds(Poly2, _nodeInfo(degof(Term), _degree(Deg)), Step),
								Poly1 < Poly2.
% unequal if have different values at the same term position
_unequal(Poly1, Poly2, Step)
							:-	_numPolyTerm(Term),
								_isPolynomial(Poly1, Step),
								_isPolynomial(Poly2, Step),
								_holds(Poly1, _nodeInfo(numterms, TermCount), Step),
								_holds(Poly2, _nodeInfo(numterms, TermCount), Step),
								Term <= TermCount,
								not _equalOnTerm(Poly1, Poly2, Term, Step),
								Poly1 < Poly2.

% unequal if different numbers of terms
_unequal(Poly1, Poly2, Step)
							:-	_holds(Poly1, _nodeInfo(numterms, Terms1), Step),
								_holds(Poly2, _nodeInfo(numterms, Terms2), Step),
								Poly1 < Poly2,
								Terms1 != Terms2.
_unequal(Poly2, Poly1, Step)
							:-	_unequal(Poly1, Poly2, Step).
_equal(Poly1, Poly2, Step)
							:-	_holds(Poly1, _nodeInfo(type, poly), Step),
								_holds(Poly2, _nodeInfo(type, poly), Step),
								not _unequal(Poly1, Poly2, Step).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%% POLYNOMIAL OPERATIONS %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

_update(Poly, _nodeInfo(coeffof(Term1), _coeff(Coeff1+Coeff2)), Step)
							:-	_addTerms(Poly, Term1, Term2, Step),
								_holds(Poly, _nodeInfo(coeffof(Term1), _coeff(Coeff1)), Step),
								_holds(Poly, _nodeInfo(coeffof(Term2), _coeff(Coeff2)), Step).
_cancelTerm(Poly, Term2, Step)
							:-	_addTerms(Poly, Term1, Term2, Step).

