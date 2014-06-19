#!/usr/bin/env python
#
# Author:	Armando Diaz Tolentino <ajdt@cs.washington.edu> 
#
# Desc:		A simple visualizer for the equations generated by the ASP program, eqn_generator.lp
#
# NOTE: 
#		requires asp output in json format. As of gringo4 this is possible with
#		clingo --outf=2 <gringo_file.lp>
#		
#		expects output from stdin, pipe clingo output to this program

import sys
import json
import re
import sympy as sp
from collections import defaultdict
import pdb
from pyparsing import Word, alphas, nums, ParseException


# values is a list of dictionaries, each dictionary contains one solution.
# each dictionary has one key called 'Value' which refers to a list of predicates and their values

def wrapWithPredicate(parser, pred='nodeInfo('):
	return pred + parser + ')'
def wrapFact(parser):
	return wrapWithPredicate( node_parser + ',' + parser, 'initially(')

node_parser		=	'id(' + Word(nums) + ',' + Word(nums) + ')'
mono_parser		=	'monoInfo(' + Word(nums) +',' +'monomial(' + Word(nums) + ',' + Word(nums) + ')' + ')'

type_parser		=	wrapFact(wrapWithPredicate(Word(alphas) + ',' + Word(alphas)))
oper_parser		=	wrapFact(wrapWithPredicate(Word(alphas) + ',' + Word(alphas)))
child_parser 	= 	wrapFact(wrapWithPredicate(Word(alphas) + ',' + node_parser, 'treeInfo('))
poly_parser		=	wrapFact(wrapWithPredicate(Word(alphas) +',' + mono_parser ))
op_symbols 		= 	{'add' : '+' , 'div' : '/' , 'mul' : '*' }



all_parsers = [ node_parser, mono_parser, type_parser, oper_parser,	child_parser, poly_parser ]

def findParserMatchingPredicate(predicate):
	for parser in all_parsers:
		try:
			parse_output = parser.parseString(predicate)
		except ParseException:
			continue
		return (parser, parse_output)
	return (None, [])

def parseNodeAndInfo(tokens):
	node		=	''.join(tokens[1:6])
	node_info	=	tokens[7:-1]
	node_info	=	node_info[1:-1]
	field		=	node_info[0]
	data		=	node_info[2:]
	return (node, field, data)
def parseMonoInfo(tokens):
	return tokens[4], tokens[6]

def formEqnString(predicates_list):
	# one dictionary per predicate type
	types, operator			= {}, {} 		# key is node id in all cases
	mono					= defaultdict(list)
	children 				= defaultdict(list)

	# parse predicate list for info first
	for predicate in predicates_list:
		parser, tokens = findParserMatchingPredicate(predicate)
		if parser == None or tokens == [] :
			continue
		node, field, data = parseNodeAndInfo(tokens)

		if field == 'type':
			types[node] = ''.join(data)
		elif field == 'operation':
			operator[node] = ''.join(data)
		elif field == 'activechild':
			child = ''.join(data)
			children[node].append(child)
		elif field == 'mono':
			coef, deg = parseMonoInfo(data)
			mono[node].append(coef + 'x^' + deg)
		else :
			continue
	#print 'types', types, '\n\n'
	#print 'operator', operator, '\n\n'
	#print 'mono', mono, '\n\n'
	#print 'children', children, '\n\n'
	# print 
	return eqnString(types, operator, mono, children)

# form the full equation string given dictionaries with data
def eqnString(types, operator,mono, children, in_latex=False):
	left	= formPolyString(types, operator,mono, children, 'id(1,1)')
	right	= formPolyString(types, operator,mono, children, 'id(1,2)')
	if in_latex:
		string =  '$$' + sp.latex( sp.sympify(left, evaluate=False)) + '=' + sp.latex( sp.sympify(right, evaluate=False)) + '$$'
	else:
		string = left[1:-1] + '=' + right[1:-1] # NOTE: slicing to avoid outermost parens
	#print string
	return string
	

def formPolyString(types, operator, mono, children, root):
	if types[root] == 'poly':
		return '(' + makePolynomial(root, mono) + ')'

	child_strings = []
	for child in children[root]:
		child_strings.append( formPolyString(types, operator, mono, children, child) )
	return '(' + op_symbols[operator[root]].join(child_strings) + ')'

def makePolynomial(nodeName, mono):
	return '+'.join(mono[nodeName])

def main():
	clasp_output = ''.join(sys.stdin.xreadlines())
	decoded = json.loads(clasp_output)
	all_soln = decoded['Call'][0]['Witnesses']
	for solution in all_soln:
		print formEqnString(solution['Value'])

if __name__ == "__main__":
	main()
