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

def wrapWithPredicate(parser, left='nodeInfo(', right=')'):
	return left + parser + right
def wrapFact(parser, left='initially(', right=')'):
	return wrapWithPredicate( node_parser + ',' + parser, left, right)

node_parser		=	'id(' + Word(nums) + ',' + Word(nums) + ')'
coeff			=	Word(nums + '-')
deg				=	Word(nums)

type_parser		=	wrapFact(wrapWithPredicate(Word(alphas) + ',' + Word(alphas)))
oper_parser		=	wrapFact(wrapWithPredicate(Word(alphas) + ',' + Word(alphas)))
child_parser 	= 	wrapFact(wrapWithPredicate(Word(alphas) + ',' + node_parser, 'treeInfo('))
mono_parser		=	wrapFact(wrapWithPredicate(deg + ',' + coeff ))
op_symbols 		= 	{'add' : '+' , 'div' : '/' , 'mul' : '*' }



all_parsers = [ node_parser, mono_parser, type_parser, oper_parser,	child_parser ]

step_type_parser		=	wrapFact(wrapWithPredicate(Word(alphas) + ',' + Word(alphas)), 'holds(', ',' + Word(nums) + ')' )
step_oper_parser		=	wrapFact(wrapWithPredicate(Word(alphas) + ',' + Word(alphas)), 'holds(', ',' + Word(nums) + ')' )
step_child_parser 		= 	wrapFact(wrapWithPredicate(Word(alphas) + ',' + node_parser, 'treeInfo('), 'holds(', ',' + Word(nums) + ')' )
step_mono_parser		=	wrapFact(wrapWithPredicate(deg + ',' + coeff), 'holds(', ',' + Word(nums) + ')' )

step_parsers = [ step_type_parser, step_oper_parser, step_child_parser, step_mono_parser]

def findParserMatchingPredicate(predicate, parser_list=all_parsers):
	for parser in parser_list:
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
	data		=	node_info[1:]
	return (node, field, data)
def parseStepInfo(tokens):
	step = int(tokens[-2])
	node, field, data = parseNodeAndInfo(tokens[:-2])
	return (node, field, data, step)
def parseMonoInfo(tokens):
	return tokens[1], tokens[3]

# used as constructor to defaultdict that returns another default dict
def makeDefDict(const=list):
	return defaultdict(const)
def makeDictDict():
	return makeDefDict(dict)
def formSolutionString(predicates_list):
	# one dictionary per predicate type
	types, operator			= defaultdict(dict), defaultdict(dict)
	monom					= defaultdict(makeDefDict)
	children 				= defaultdict(makeDefDict)

	# parse predicate list for info first
	for predicate in predicates_list:
		parser, tokens = findParserMatchingPredicate(predicate, step_parsers)
		if parser == None or tokens == [] :
			continue
		node, field, data, step = parseStepInfo(tokens)

		if field == 'type':
			types[step][node] = ''.join(data[1:])
		elif field == 'operation':
			operator[step][node] = ''.join(data[1:])
		elif field == 'activechild':
			child = ''.join(data[1:])
			children[step][node].append(child)
		elif field in '0123456789': 
			coeff = data[1]
			deg = field
			monom[step][node].append((deg, coeff))
	#print 'types', types, '\n\n'
	#print 'operator', operator, '\n\n'
	#print 'mono', mono, '\n\n'
	#print 'children', children, '\n\n'
	# print 
	all_steps = []
	for solve_step in sorted(types.keys()):
		all_steps.append( str(solve_step) + ': ' + eqnString(types[solve_step], operator[solve_step], monom[solve_step], children[solve_step]))
	return '\n'.join(all_steps) 


def formEqnString(predicates_list):
	# one dictionary per predicate type
	types, operator			= {}, {} 		# key is node id in all cases
	monom					= defaultdict(list)
	children 				= defaultdict(list)

	# parse predicate list for info first
	for predicate in predicates_list:
		parser, tokens = findParserMatchingPredicate(predicate)
		if parser == None or tokens == [] :
			continue
		node, field, data, step = parseStepInfo(tokens)

		if field == 'type':
			types[node] = ''.join(data[1:])
		elif field == 'operation':
			operator[node] = ''.join(data[1:])
		elif field == 'activechild':
			child = ''.join(data[1:])
			children[node].append(child)
		elif field in '0123456789': 
			coeff = data[1]
			deg = field
			monom[node].append((deg, coeff))
	return eqnString(types, operator, monom, children)

# form the full equation string given dictionaries with data
def eqnString(types, operator,monom, children, in_latex=False):
	left	= formPolyString(types, operator,monom, children, 'id(1,1)')
	right	= formPolyString(types, operator,monom, children, 'id(1,2)')
	if in_latex:
		string =  '$$' + sp.latex( sp.sympify(left, evaluate=False)) + '=' + sp.latex( sp.sympify(right, evaluate=False)) + '$$'
	else:
		string = left[1:-1] + '=' + right[1:-1] # NOTE: slicing to avoid outermost parens
	#print string
	return string
	

def formPolyString(types, operator, monom, children, root):
	if types[root] == 'poly':
		return '(' + makePolynomial(root, monom) + ')'

	child_strings = []
	for child in children[root]:
		child_strings.append( formPolyString(types, operator, monom, children, child) )
	return '(' + op_symbols[operator[root]].join(child_strings) + ')'

def makePolynomial(nodeName, monom):
	all_terms = []
	for (deg, coeff) in monom[nodeName]:
		mono_term = ''
		if coeff == '0':
			mono_term = '0'
		elif deg == '0':
			mono_term = coeff
		else:
			mono_term =  coeff + 'x^' + deg

		all_terms.append(mono_term)
	return '+'.join(all_terms)


def printEqns(all_soln):
	for solution in all_soln:
		print formEqnString(solution['Value'])
def printEqnSolns(all_soln):
	for solution in all_soln:
		print formSolutionString(solution['Value'])
def main():
	clasp_output = ''.join(sys.stdin.xreadlines())
	decoded = json.loads(clasp_output)
	all_soln = decoded['Call'][0]['Witnesses']
	if len(sys.argv) > 1 and sys.argv[1] == '--steps':
		printEqnSolns(all_soln)
	else:
		printEqns(all_soln)

if __name__ == "__main__":
	main()
