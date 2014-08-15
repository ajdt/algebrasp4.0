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


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%% POLYNOMIAL NODES %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
#const numPolynomials	=	10.
_polynomial(_id(poly, NodeNum))
			:-	NodeNum = 0..numPolynomials+1.
_activePolynom(Polynom, Step)
			:-	_holds(Polynom, allocated, Step).

_inactivePolynom(Polynom, Step)	% any node that is not allocated is free
			:-	_polynomial(Polynom),
				_step(Step),
				not _activePolynom(Polynom, Step).

% allocating polynomials initially (works differently)
_polyNotAllocatedTwice(Poly)	
			:-	_polynomial(Poly), 0 { _assignPolyToNode(Poly, Node) : _node(Node) } 1 .
:-	_polynomial(Poly), not _polyNotAllocatedTwice(Poly).

% same logic but for time steps
_polyNotAllocatedTwice(Poly, Step)	
			:-	_polynomial(Poly),
				_step(Step),
				0 { _assignPolyToNode(Poly, Node, Step) : _node(Node) } 1 .
:-	_step(Step),
	_polynomial(Poly), 
	not _polyNotAllocatedTwice(Poly, Step).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%% GENERATING POLYNOMIALS %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% given order (degree) of polynomial to generate,
% pick exactly one monomial of given order, and at most one monomial for each 
% lesser degree
1 { _assignPolyToNode(Poly, Node)	:	_polynomial(Poly), not _polyConst(Poly)	} 1
			:-	_assignToPolyWithOrder(Node, Order).
_initPolyWithOrder(Poly, Order)
			:-	_assignToPolyWithOrder(Node, Order),
_assignPolyToNode(Poly, NOde).

1 { _initially(Poly, _polyInfo(Order, Coeff)) : _coeff(Coeff), |Coeff| <= maxInitialCoeff, |Coeff| > 0} 1 
			:-	_initPolyWithOrder(Poly, Order).
0 { _initially(Poly, _polyInfo(Deg, Coeff)) : _coeff(Coeff), |Coeff| <= maxInitialCoeff} 1 
			:-	_initPolyWithOrder(Poly, Order), _degree(Deg), Deg < Order.

% TODO: change this later, so hasMonom(...) directly adds monomials to polynomials
_initially(Poly, allocated)
			:-	_assignPolyToNode(Poly, Node).
% garbage collecting polynomials
_garbageCollectPoly(Poly, Step)				%	apply GC to every poly that doesn't have any pointers to it anymore
			:-	_polynomial(Poly),
				_holds(Poly, allocated, Step),
				not _polyConst(Poly),
				_step(Step),
				0 { _holds(Node, _nodeInfo(polynom, Poly), Step) : _node(Node) } 0.
_remove(Poly, Info, Step)
			:-	_garbageCollectPoly(Poly, Step),
				_polynomial(Poly),
				_holds(Poly, Info, Step).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%% POLYNOMIAL ALLOCATION %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% code for creating a new poly, and adding terms to it
1 { _assignPolyToNode(Polynom, Node, Step)	:	_inactivePolynom(Polynom, Step) } 1
			:-	_allocatePolyToNode(Node, Step).
_introduce(Polynom, allocated, Step)
			:-	_assignPolyToNode(Polynom, Node, Step).

% update treeNode's polynom references (different for temp and regular nodes)
_introduce(Node, _nodeInfo(polynom, Polynom), Step)
			:-	_assignPolyToNode(Polynom, Node, Step), not _tempNode(Node).
_remove(Node, _nodeInfo(polynom, OldPoly), Step)
			:-	_assignPolyToNode(Polynom, Node, Step), not _tempNode(Node),
				_holds(Node, _nodeInfo(polynom, OldPoly), Step).
_tempResult(Node, _nodeInfo(polynom, Polynom), Step)
			:-	_assignPolyToNode(Polynom, Node, Step), _tempNode(Node).
% adding terms
_introduce(Polynom, _polyInfo(Deg, Coeff), Step)
			:-	_addTermToNewPoly(Polynom, Deg, Coeff, Step),
				_polynomial(Polynom).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%% POLYNOMIAL PROPERTIES %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
_quadWithCommonTerm(Poly, Step)
			:-	_polyProperty(Poly, is_quadratic, Step),
				_polyProperty(Poly, is_factorable, Step),
				_squareMonom(Poly, ACoeff, Step),
				ACoeff != 1,
				|ACoeff| > 0,
				|ACoeff| <= 5,
				_linearMonom(Poly, BCoeff, Step),
				%(BCoeff \ ACoeff) == 0, % TODO: why do these cause a floating point error?
				%(CCoeff \ ACoeff) == 0,
				|BCoeff| <=5,
				_constMonom(Poly, CCoeff, Step),
				|CCoeff| <=5.

%% polynomial properties
_polyProperty(Poly, is_monomial, Step)
							:-	_step(Step),
								_polynomial(Poly), 
								1 { _holds(Poly, _polyInfo(Deg, Coeff), Step) : _degree(Deg), _coeff(Coeff)} 1.
_polyProperty(Poly, is_binomial, Step)
							:-	_step(Step),
								_polynomial(Poly), 
								2 { _holds(Poly, _polyInfo(Deg, Coeff), Step) : _degree(Deg), _coeff(Coeff)} 2.
_polyProperty(Poly, is_trinomial, Step)
							:-	_step(Step),
								_polynomial(Poly), 
								3 { _holds(Poly, _polyInfo(Deg, Coeff), Step) : _degree(Deg), _coeff(Coeff)} 3.

% some basic size predicates: used in lieu of having an actual size field (more expensive)
_polySize(Poly, 3, Step)	:-	_polyProperty(Poly, is_trinomial, Step).
_polySize(Poly, 2, Step)	:-	_polyProperty(Poly, is_binomial, Step).
_polySize(Poly, 1, Step)	:-	_polyProperty(Poly, is_monomial, Step).

_polyProperty(Poly, has_zero_term, Step)			
							:-	_holds(Poly, _polyInfo(Deg, 0), Step),
								_degree(Deg).
_polyProperty(Poly, has_term_with_deg(Deg), Step)			
							:-	_holds(Poly, _polyInfo(Deg, Coeff), Step),
								_degree(Deg).
_polyProperty(Poly, has_nonzero_term_with_deg(Deg), Step)			
							:-	_holds(Poly, _polyInfo(Deg, Coeff), Step),
								_degree(Deg),
								Coeff != 0.
_polyProperty(Poly, has_high_deg_terms, Step)			
							:-	_polyProperty(Poly, has_nonzero_term_with_deg(Deg), Step),
								Deg > 3.

_polyProperty(Poly, is_zero, Step)			
							:-	_polyProperty(Poly, is_monomial, Step),
								_degree(Deg),
								_holds(Poly, _polyInfo(Deg, 0), Step). 
% a polynomial is zero if it's reducible to zero as well
_polyProperty(Poly, is_zero, Step)
							:-	_polynomial(Poly),
								_step(Step),
								not _polyProperty(Poly, not_reducible_to_zero, Step).
_polyProperty(Poly, not_reducible_to_zero, Step)	
							:-	_polynomial(Poly),
								_degree(Deg),
								_holds(Poly, _polyInfo(Deg, Coeff), Step),
								Coeff != 0.

_polyProperty(Poly, is_one, Step)	
							:-	_polyProperty(Poly, is_monomial, Step),
								_holds(Poly, _polyInfo(0, 1), Step). 
_polyProperty(Poly, is_const, Step)
							:-	_polyProperty(Poly, is_monomial, Step),
								_polyProperty(Poly, has_nonzero_term_with_deg(0), Step).
_polyProperty(Poly, is_const, Step)
							:-	_polyProperty(Poly, is_monomial, Step),	% handles case where monomial is zero coeff but higher degree
								_polyProperty(Poly, has_zero_term, Step).
_polyProperty(Poly, is_xterm, Step)
							:-	_polyProperty(Poly, is_monomial, Step),
								_holds(Poly, _polyInfo(1, 1), Step). 

% XXX: assumes max assignable degree is 3
_polyProperty(Poly, is_quadratic, Step)	
							:-	not _polyProperty(Poly, has_high_deg_terms, Step),
								not _polyProperty(Poly, has_nonzero_term_with_deg(3), Step),
								_polyProperty(Poly, has_nonzero_term_with_deg(2), Step).
								
_polyProperty(Poly, is_linear, Step)	
							:-	not _polyProperty(Poly, has_high_deg_terms, Step),
								not _polyProperty(Poly, has_nonzero_term_with_deg(3), Step),
								not _polyProperty(Poly, has_nonzero_term_with_deg(2), Step),
								_polyProperty(Poly, has_nonzero_term_with_deg(1), Step).

_polyProperty(Poly, is_zero_deg, Step)	
							:-	not _polyProperty(Poly, has_high_deg_terms, Step),
								not _polyProperty(Poly, has_nonzero_term_with_deg(3), Step),
								not _polyProperty(Poly, has_nonzero_term_with_deg(2), Step),
								not _polyProperty(Poly, has_nonzero_term_with_deg(1), Step),
								_polyProperty(Poly, has_nonzero_term_with_deg(0), Step).

% coefficients of second, first, and zero degree
% NOTE: not polyproperties b/c we don't want these to be inherited by treeNodes
_squareMonom(Poly, Coeff, Step)
							:-	_holds(Poly, _polyInfo(2, Coeff), Step).
_linearMonom(Poly, Coeff, Step)
							:-	_holds(Poly, _polyInfo(1, Coeff), Step).
_constMonom(Poly, Coeff, Step)
							:-	_holds(Poly, _polyInfo(0, Coeff), Step).

%% poly properties for treeNodes
_isPolynomial(Node, Step)
							:-	_holds(Node, _nodeInfo(type, poly), Step).
_polyProperty(Node, Property, Step)
							:-	_polyProperty(Poly, Property, Step),
								_holds(Node, _nodeInfo(polynom, Poly), Step).



							%% ** left off here


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%% DEFINED POLYNOMIAL CONSTANTS %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
#const zero	= _id(poly, 0).
#const one	= _id(poly, 1).
_polyConst(zero ; one).

_initially(zero, _polyInfo(0,0)).
_initially(one, _polyInfo(0,1)).
_initially(Const, allocated)		:-	_polyConst(Const).

% setting a treeNode to a constant poly
_introduce(Node, _nodeInfo(type, poly), Step)
							:-	_setToUnitPoly(Node, Step).
_introduce(Node, _nodeInfo(polynom, one), Step)
							:-	_setToUnitPoly(Node, Step).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%% POLYNOMS EQUALITY %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% NOTE: only care about equality comparisons when nodes are in the same layer
_unequal(Poly1, Poly2, Step)
							:-	_polynomial(Poly1),	
								_polynomial(Poly2),
								Poly1 != Poly2,
								_holds(Poly1, _polyInfo(Deg, Coeff), Step),
								not _holds(Poly2, _polyInfo(Deg, Coeff), Step).
								%Poly1 < Poly2.
_equal(Poly1, Poly2, Step)
							:-	_activePolynom(Poly1, Step),	% don't care about equality for unallocated nodes
								_activePolynom(Poly2, Step),
								Poly1 != Poly2,
								_step(Step),
								not _unequal(Poly1, Poly2, Step), % didn't want to include separate _unequal rule for symmetry
								not _unequal(Poly2, Poly1, Step).
_equal(TreeNode1, TreeNode2, Step)
							:-	_polynomOf(TreeNode1, Poly1, Step),
								_polynomOf(TreeNode2, Poly2, Step),
								TreeNode1 != TreeNode2,
								_equal(Poly1, Poly2, Step).
_polynomOf(TreeNode, Poly, Step)
							:-	_holds(TreeNode, _nodeInfo(polynom, Poly), Step).
