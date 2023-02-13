from __future__ import annotations
from ast import Constant
from typing import Dict, List, Set, Tuple, Optional
from lang.utils import getExpressionsInStatement, getVarsUsedInExpression, getExpressionsInCFG, getExpressionsInExpression
from .analysis import Analysis
from lang.cfg import Entry, Exit, InnerNode, Node, CFG
from lang.ast import Assignment, Statement, Guard, Variable, Expression, BinaryExpression, UnaryExpression, ConstantExpression, BooleanConstant, IntegerConstant

AnalysisType = Set[Expression] 

#forward analysis
#may analysis
#union
class PartiallyAvailableExpressions(Analysis[AnalysisType]):
        def initial_in(self, node: Node) -> AnalysisType:
            return set() 

        # boundary for OUT[Entry] is also {}
        def initial_out(self, node: Node) -> AnalysisType:
            return set()
  
        def get_new_values(self, node: Node, predecessors_out: List[AnalysisType], successors_in: List[AnalysisType], curr_out: Dict[Node, AnalysisType], curr_in: Dict[Node, AnalysisType]) -> Tuple[AnalysisType, AnalysisType]:

            """ 
            Return tuple (In, Out), 
            computed using this node's predessors' Outs (`predecessors_out`)
            """
            Gen = set() 
            Kill = set() 
            In = set()
            Out = set()
            if isinstance(node, Entry):
                pass
            else:
                if isinstance(node, Exit):
                    # no action to gen and kill set
                    In = set().union(*predecessors_out)
                elif isinstance(node.statement, Guard):
                    In = set().union(*predecessors_out)
                    Gen = getExpressionsInStatement(node.statement)
                elif isinstance(node.statement, Assignment):
                    In = set().union(*predecessors_out)
                    WrittenVar = node.statement.variable  
                    Used = getExpressionsInExpression(node.statement.value)
                    Kill = set(filter(lambda expression: WrittenVar in getVarsUsedInExpression(expression), In))
                    Gen = Used.difference(set(filter(lambda expression: (WrittenVar in getVarsUsedInExpression(expression)), Used)))
                else: 
                    raise Exception(
                    f"Node {node} with statement of type {type(node.statement)} not supported in {type(self).__name__}'s get_new_values method.")

            # calculate OUT[B] by F(IN[B])
            Out = In.difference(Kill).union(Gen)
            
            return (In, Out)
