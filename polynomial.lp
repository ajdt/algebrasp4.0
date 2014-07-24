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
_baseMonom(Coeff, 2)		:-	_coeff(Coeff), |Coeff| < maxAssignSquareCoeff.
_baseMonom(Coeff, 1)		:-	_coeff(Coeff), |Coeff| < maxAssignLinearCoeff.
_baseMonom(Coeff, 0)		:-	_coeff(Coeff), |Coeff| < maxAssignConstCoeff.


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%% GENERATING POLYNOMIALS %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% given order (degree) of polynomial to generate,
% pick exactly one monomial of given order, and at most one monomial for each 
% lesser degree
1 { _hasMonom(Node, Order, Coeff) : _coeff(Coeff), _baseMonom(Coeff,Order) } 1 
			:-	_makePolyWithOrder(Node, Order).
0 { _hasMonom(Node, Deg, Coeff) : _coeff(Coeff), _baseMonom(Coeff,Deg) } 1 
			:-	_makePolyWithOrder(Node, Order), _degree(Deg), Deg < Order.

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%% POLYNOMIAL PROPERTIES %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
_quadWithCommonTerm(Poly, Step)
			:-	_isQuadratic(Poly, Step),
				_squareMonom(Poly, ACoeff, Step),
				_isFactorable(Poly, Step),
				ACoeff != 1,
				|ACoeff| > 0,
				|ACoeff| <= 5,
				_linearMonom(Poly, BCoeff, Step),
				%(BCoeff \ ACoeff) == 0, % TODO: why do these cause a floating point error?
				%(CCoeff \ ACoeff) == 0,
				BCoeff <=5,
				BCoeff >= - 5,
				_constMonom(Poly, CCoeff, Step),
				CCoeff <=5,
				CCoeff >= - 5.

_isPolynomial(Poly, Step)	:-	_holds(Poly, _nodeInfo(type, poly), Step).
_isMonomial(Poly, Step)		:-	_step(Step),
								_node(Poly), 
								1 { _holds(Poly, _nodeInfo(Deg, Coeff), Step) : _degree(Deg), _coeff(Coeff)} 1.
_isBinomial(Poly, Step)		:-	_step(Step),
								_node(Poly), 
								2 { _holds(Poly, _nodeInfo(Deg, Coeff), Step) : _degree(Deg), _coeff(Coeff)} 2.
_isTrinomial(Poly, Step)	:-	_step(Step),
								_node(Poly), 
								3 { _holds(Poly, _nodeInfo(Deg, Coeff), Step) : _degree(Deg), _coeff(Coeff)} 3.
_polySize(Poly, 3, Step)	:-	_isTrinomial(Poly, Step).
_polySize(Poly, 2, Step)	:-	_isBinomial(Poly, Step).
_polySize(Poly, 1, Step)	:-	_isMonomial(Poly, Step).

_hasZeroTerm(Poly, Step)			:-	_holds(Poly, _nodeInfo(Deg, 0), Step),
										_degree(Deg).
_hasTermWithDeg(Poly, Deg, Step)	:-	_holds(Poly, _nodeInfo(Deg, Coeff), Step),
										_degree(Deg),
										Coeff != 0.
_hasHighDegreeTerms(Poly, Step)	:-	_hasTermWithDeg(Poly, Deg, Step),
									Deg > 3.

_isZero(Poly, Step)	:-	_isMonomial(Poly, Step),
						_degree(Deg),
						_holds(Poly, _nodeInfo(Deg, 0), Step). % remove _isZeroMonomial?
% a polynomial is zero if it's reducible to zero as well
_isZero(Poly, Step)	:-	_isPolynomial(Poly, Step),
						not _notReducibleToZero(Poly, Step).
_notReducibleToZero(Poly, Step)	
					:-	_isPolynomial(Poly, Step),
						_degree(Deg),
						_holds(Poly, _nodeInfo(Deg, Coeff), Step),
						Coeff != 0.

_isOne(Poly, Step)	:-	_isMonomial(Poly, Step),
						_holds(Poly, _nodeInfo(0, 1), Step). % remove _isUnitMonomial?
_isConst(Poly, Step)	:-	_isMonomial(Poly, Step),
						_hasTermWithDeg(Poly, 0, Step).
_isConst(Poly, Step)	:-	_isMonomial(Poly, Step),	% handles case where monomial is just 0
							_hasZeroTerm(Poly, Step).
_isXTerm(Poly, Step)	:-	_isMonomial(Poly, Step),
						_holds(Poly, _nodeInfo(1, 1), Step). 

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

% coefficients of second, first, and zero degree
_squareMonom(Poly, Coeff, Step)
							:-	_holds(Poly, _nodeInfo(2, Coeff), Step).
_linearMonom(Poly, Coeff, Step)
							:-	_holds(Poly, _nodeInfo(1, Coeff), Step).
_constMonom(Poly, Coeff, Step)
							:-	_holds(Poly, _nodeInfo(0, Coeff), Step).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%% DEFINED POLYNOMIAL CONSTANTS %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
_introduce(Node, _nodeInfo(type, poly), Step)
							:-	_setToUnitPoly(Node, Step).
_introduce(Node, _nodeInfo(0, 1), Step)
							:-	_setToUnitPoly(Node, Step).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%% POLYNOMS EQUALITY %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% NOTE: only care about equality comparisons when nodes are in the same layer
_unequal(Poly1, Poly2, Step)
							:-	_node(Poly1),	
								_node(Poly2),
								not _tempNode(Poly1),
								not _tempNode(Poly2),
								_holds(Poly1, _nodeInfo(Deg, Coeff), Step),
								not _holds(Poly2, _nodeInfo(Deg, Coeff), Step),
								_layerOf(Poly1, Layer),
								_layerOf(Poly2, Layer).
								%Poly1 < Poly2.
_equal(Poly1, Poly2, Step)
							:-	_holds(Poly1, _nodeInfo(type, poly), Step),
								_holds(Poly2, _nodeInfo(type, poly), Step),
								not _unequal(Poly1, Poly2, Step), % didn't want to include separate _unequal rule for symmetry
								not _unequal(Poly2, Poly1, Step).

