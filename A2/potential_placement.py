from __future__ import annotations
from ast import Constant
from typing import Dict, List, Set, Tuple, Optional
from analysis.available_expressions import AvailableExpressions
from analysis.partially_available_expressions import PartiallyAvailableExpressions
from analysis.fixed_point import fixed_point
from lang.utils import getVarsUsedInExpression, getExpressionsInCFG, getExpressionsInStatement, getExpressionsInExpression
from .analysis import Analysis
from lang.cfg import Entry, Exit, InnerNode, Node, CFG
from lang.ast import Assignment, Statement, Guard, Variable, Expression, BinaryExpression, UnaryExpression, ConstantExpression, BooleanConstant, IntegerConstant

AnalysisType = Set[Expression] 

class PotentialPlacement(Analysis[AnalysisType]):
    def __init__(self, CFG: CFG):
            self.AllExpressions = getExpressionsInCFG(CFG)
            self.A_In, self.A_Out = fixed_point(CFG, AvailableExpressions(CFG))
            self.PA_In, self.PA_Out = fixed_point(CFG, PartiallyAvailableExpressions(CFG))
            self.successor_nodes = {}
            for node in CFG.nodes:
                self.successor_nodes[node] = CFG.next[node]

    def initial_in(self, node: Node) -> AnalysisType:
            return set()

    def initial_out(self, node: Node) -> AnalysisType:
            return set()
            
    def get_new_values(self, node: Node, predecessors_out: List[AnalysisType], successors_in: List[AnalysisType], curr_out: Dict[Node, AnalysisType], curr_in: Dict[Node, AnalysisType]) -> Tuple[Dict[Node, AnalysisType], Dict[Node, AnalysisType]]: 
            Gen = set() 
            Kill = self.AllExpressions
            Out = self.AllExpressions
            for snode in self.successor_nodes[node]:
                Out = Out.intersection(self.A_In[snode])
            Out = Out.union(self.AllExpressions.intersection(*successors_in))
            
            if (isinstance(node, Entry)):
                pass
            elif (isinstance(node, Exit)):
                pass
            elif (isinstance(node, InnerNode)):
                if (isinstance(node.statement, Guard)):
                    Gen = getExpressionsInStatement(node.statement)
                elif (isinstance(node.statement, Assignment)):
                    WrittenVar = node.statement.variable
                    Used = getExpressionsInExpression(node.statement.value)
                    Kill = self.PA_In[node].union(self.PA_Out[node]).difference(set(filter(lambda expression: WrittenVar in getVarsUsedInExpression(expression), Out)))
                    Gen = Used.difference(set(filter(lambda expression: (WrittenVar in getVarsUsedInExpression(expression)), Used)))
                else: 
                    raise Exception(
                    f"InnerNode {node} with statement of type {type(node.statement)} not supported in {type(self).__name__}'s get_new_values method.")
                pass
            else: 
                raise Exception(
                f"Node {node} with statement of type {type(node.statement)} not supported in {type(self).__name__}'s get_new_values method.")

            In = Out.intersection(Kill).union(Gen)
            return (In, Out)

def insert(program:CFG) -> Dict[Node, AnalysisType]:
    PP_In, PP_Out = fixed_point(program, PotentialPlacement(program))
    insertSet = {}
    for node in PP_In.keys():
        insertSet[node] = PP_Out[node].difference(PP_In[node])

    return insertSet


def delete(program:CFG) -> Dict[Node, AnalysisType]:
    PP_In, PP_Out = fixed_point(program, PotentialPlacement(program))
    deleteSet = {}
    for node in PP_In.keys():
        Used = set()
        if (isinstance(node, InnerNode)):
            if (isinstance(node.statement, Guard)):
                Used = getExpressionsInStatement(node.statement)
            else:
                Used = getExpressionsInExpression(node.statement.value)
        deleteSet[node] = Used.difference(PP_Out[node].difference(PP_In[node]))

    return deleteSet
        