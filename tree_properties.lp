%Operator properties

_isMul(Node, Step)	:-	_holds(Node, _nodeInfo(operation, mul), Step).
_isAdd(Node, Step)	:-	_holds(Node, _nodeInfo(operation, add), Step).
_isDiv(Node, Step)	:-	_holds(Node, _nodeInfo(operation, div), Step).

_numChildren(Node, NumKids, Step)	
					:-	_holds(Node, _nodeInfo(numchildren, NumKids), Step).
_termOf(Parent, Child, Step)	
					:-	_holds(Parent, _nodeInfo(activechild, Child), Step).



% are there enough free nodes for tree to expand?
_canGrowTreeFromNode(_id(Layer, Number), Step)	
					:-	_node(_id(Layer, Number)), Layer <= maxDepth, _step(Step).


							%				TREE OPERATIONS
% possible operations

% deleting a monomial
% 
_remove(Polynomial, _nodeInfo(monom, Monom), Step)
					:-	_deleteMonomial(Polynomial, Monom, Step).
% shift down all monomials
_shiftDownMonom(Parent, Num +1, 1, Step)
					:-	_deleteMonomial(Parent, Term, Step),
						_holds(Parent, _child(Num, Term), Step).
_remove(Parent, _term(Num, Term), Step)
					:-	_shiftDownMonom(Parent, Start, Delta, Step),
						_holds(Parent, _term(Num, Term), Step), Num >=Start.
_introduce(Parent, _term(Num - Delta, Term), Step)
					:-	_shiftDownMonom(Parent, Start, Delta, Step),
						_holds(Parent, _term(Num, Term), Step), Num >=Start.

% update the number of terms
_update(Poly, _nodeInfo(numterms, NumTerms - 1), Step)
					:-	_deleteMonomial(Poly, Mono, Step),
						_holds(Poly, _nodeInfo(numterms, NumTerms), Step).

% canceling a term
_deleteNode(Term, Step)	:-	_cancelTerm(Term, Step).
_deleteMonomial(Polynomial, Monom, Step)		% TODO: write this
					:-	_cancelTerm(Monom, Step),
						_polyTerm(Polynomial, Monom, Step).

% deleting a node means to remove all parent pointers, and the entire subtree rooted at that node
% to remove node properties use _clearNode(...)

_deleteChildProperties(Parent, Child, Step)
						:-	_deleteNode(Child, Step),
							_termOf(Parent, Child, Step).	

% update parent's child count
_update(Parent, _nodeInfo(numchildren, NumKids - 1), Step)
					:-	_deleteChildProperties(Parent, Node, Step),
						_holds(Parent, _nodeInfo(numchildren, NumKids), Step).
% remove parent pointers to child
_remove(Parent, _nodeInfo(activechild, Term), Step)
					:-	_deleteChildProperties(Parent, Term, Step).
_remove(Parent, _child(Num, Term), Step)
					:-	_deleteChildProperties(Parent, Term, Step),
						_holds(Parent, _child(Num, Term), Step).
% shift down all remaining children
_shiftDownChildren(Parent, Num +1, 1)
					:-	_deleteChildProperties(Parent, Term, Step),
						_holds(Parent, _child(Num, Term), Step).
_remove(Parent, _child(Num, Term), Step)
					:-	_shiftDownChildren(Parent, Start, Delta),
						_holds(Parent, _child(Num, Term), Step), Num >=Start.
_introduce(Parent, _child(Num - Delta, Term), Step)
					:-	_shiftDownChildren(Parent, Start, Delta),
						_holds(Parent, _child(Num, Term), Step), Num >=Start.
% delete the node
_remove(Node, Info, Step)
					:-	_deleteNode(Node, Step),
						_holds(Node, Info, Step).

% swap node (shallow copy of nodes
_shallowCopy(Node1, Node2, Step)
					:-	_swapTerms(Node1, Node2, Step).
_shallowCopy(Node2, Node1, Step)
					:-	_swapTerms(Node1, Node2, Step).
_update(Copy, Info, Step)
					:-	_shallowCopy(Copy, ToCopy, Step),
						_holds(ToCopy, Info, Step).
% delete a subtree
% copy a node
% copy entire subtree
% acquire a free node

% move subtree down, 
% move children down
% copy subtree, 
% delete subtree, 
% compare subtrees (equality)
% move subtree up

