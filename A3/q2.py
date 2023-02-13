#!/usr/bin/env python3
"""
CSC410 Assignment 2 - SAT and SMT.
Problem 2: Solving Hidato with a SMT Solver.
by Victor Nicolet
"""
# You cannot import any other modules. Put all your helper functions in this file
# You cannot use Bool from z3, only these functions
from operator import pos
from z3 import Solver, Int, Xor, And, Or, Not, BoolRef, ArithRef
from itertools import combinations
from typing import *
from time import time
import sys

# ================================================================================
#  ⚠️ Do not modify above!
# ================================================================================


def solve(grid: List[List[Union[str, int]]]) -> List[List[Union[str, int]]]:
    """
    This function solves the Hidato puzzle with the initial configuration stored in grid.
    You should ouput a grid in the same format, but where all the '-' have been replaced
    by numbers.
    """
    # TODO : solve the Hidato puzzle using Z3. grid[i][j] is either "-", "*" or an integer.
    # You must use SMT. The import forces you to use integers (Int(..))
    # IMPORTANT:
    # - You are not allowed to create more variables than there are cells on the grid.
    # - Your python code should be at most O(n^4) where n is the length of the longest
    # side of the grid.

    # Return the completed grid if a solution exists. Otherwise, return None.
    s = Solver()
    m = len(grid)
    n = len(grid[0])
    minVal = float('inf')
    maxVal = -float('inf')
    directions = [[-1,0],[1,0],[0,-1],[0,1],[1,1],[-1,1],[-1,-1],[1,-1]]
    board = [[None] * n for _ in range(m)] 
    fillInPositions = []
    # list for all clauses 
    clauses = []
    # create Integer for places 
    for r in range(m):
        for c in range(n):
            if type(grid[r][c]) == type(1):
                # given integer 
                # update min and max values in the grid 
                minVal = min(minVal, grid[r][c])
                maxVal = max(maxVal, grid[r][c])
                # create variable
                board[r][c] = Int(f"Board{r},{c}")
                fillInPositions.append([r,c])
                # add clause for this fixed value
                clauses.append(board[r][c] == grid[r][c])
            elif grid[r][c] == '-':
                # create variable
                board[r][c] = Int(f"Board{r},{c}")
                fillInPositions.append([r,c])
    
    # constraint # 1: 
    # number == min --> has one neighbor that is min + 1
    # number == max --> has one neighbor that is max - 1
    # min < number < max --> has one neighbor that is min + 1 and one neighbor that is max - 1
    
    for r in range(m):
        for c in range(n):
            if type(grid[r][c]) == type(1) or grid[r][c] == '-':
                # constraint # 2:
                # each number should be in range [minVal, maxVal]
                clauses.append(And(board[r][c] >= minVal, board[r][c] <= maxVal))
                
                # find all valid neighbors for grid[r][c]
                validNeighbors = []
                for dx, dy in directions:
                    newX = r + dx
                    newY = c + dy
                    if 0 <= newX < m and 0 <= newY < n and grid[newX][newY] != '*':
                        # not blocked and valid position on the grid
                        validNeighbors.append([newX, newY])
                
                
                if grid[r][c] == minVal:
                    valPlusOne = [] 
                    for x, y in validNeighbors:
                        valPlusOne.append(board[r][c] == board[x][y] - 1)
                    clauses.append(Or(valPlusOne))
                elif grid[r][c] == maxVal:
                    valMinusOne = []
                    for x, y in validNeighbors:
                        valMinusOne.append(board[r][c] == board[x][y] + 1)
                    clauses.append(Or(valMinusOne))
                else:
                    # a blank waited to be filed 
                    # or 
                    # a given number 
                    valPlusOne = [] 
                    valMinusOne = []
                    for x, y in validNeighbors:
                        valPlusOne.append(board[r][c] == board[x][y] - 1)
                        valMinusOne.append(board[r][c] == board[x][y] + 1)
                    clauses.append(And(Or(valPlusOne), Or(valMinusOne)))
    
    # constraint # 3:        
    # each cell has a unique value 
    fileInVars = [board[r][c] for r, c in fillInPositions]
    pairs = list(combinations(fileInVars,2))
    noDuplicates = []
    for cell1, cell2 in pairs:
        noDuplicates.append(cell1 != cell2)
    clauses.append(And(noDuplicates))
    # constriant # 4: 
    # max - min + 1 == length of fillInPositions 
    clauses.append(maxVal - minVal + 1 == len(fillInPositions))
    # adding all constraints to the solver 
    s = Solver()
    for clause in clauses:
        s.add(clause)
    
    if str(s.check()) == 'sat':
        model = s.model()
        ans = [['*'] * n for _ in range(m)]
        for row in range(m):
            for col in range(n):
                if grid[row][col] != '*':
                    ans[row][col] = model.evaluate(board[row][col])
        return ans
    else:
        return None


# ================================================================================
#  ⚠️ Do not modify below!
# ================================================================================

def check(raw_grid: List[List[str]]) -> List[List[Union[str, int]]]:
    """
    Check that the grid is well defined.
    It return a grid with integers or the strings "*" or "-",
    or None if the grid is not well defined.
    """
    n = len(raw_grid)
    assert n > 1
    m = len(raw_grid[0])
    assert m > 1

    grid = []
    # Compute min and max in the grid
    max_value = 1
    min_value = 1
    # Compute the number of blocked cells
    blocked_cells = 0
    for i in range(n):
        grid.append([])
        if not len(raw_grid[i]) == m:
            print(
                f"Line {i+1} has only {len(raw_grid[i])} cells, it should have {m}.")
            return None

        for j, elt in enumerate(raw_grid[i]):
            if elt == '*':
                blocked_cells += 1
                grid[i].append(elt)
            elif elt == '-':
                grid[i].append(elt)
            else:
                try:
                    value = int(elt)
                    max_value = max(value, max_value)
                    min_value = min(value, min_value)
                    grid[i].append(int(elt))
                except:
                    print(
                        f"Cell {i+1},{j+1} is {elt}: this is not the right format.")
                    return None

    # Check the min and max values w.r.t to then number of blocked cells
    if min_value < 1:
        print("The smallest value allowed, which is 1, should appear on the grid.")
        return None

    largest_value_allowed = (n * m - blocked_cells)
    if max_value != largest_value_allowed:
        print(
            f"The largest value should be {largest_value_allowed}, but the max value on the grid is {max_value}.")
        return None

    return grid


def print_solution(grid: List[List[Union[str, int]]]) -> None:
    for line in grid:
        if '-' not in line:
            print(" ".join([f"{str(x):>3s}" for x in line]))
        else:
            print("Solution incomplete!")


def main(argv: List[str]) -> None:
    if len(argv) < 2:
        print("Usage: python3 q2.py INPUT_FILE")
        print("\tHint: test_input contains valid input files for Hidato.")
        print("\tThe inputs that are unsat are suffixed _unsat.txt, the others are sat.")
        exit(1)

    raw_grid = []
    with open(argv[1], 'r') as input_grid:
        for line in input_grid.readlines():
            if not line.startswith("#"):
                raw_grid.append(line.strip().split())

        grid = check(raw_grid)
        if grid:
            # Call the encoding function on the input.
            start = time()
            solution = solve(grid)
            elapsed = time() - start
            if solution:
                print_solution(solution)

            print(f"ELAPSED: {elapsed: 4.4f} seconds.")

            exit(0)
        else:
            # Grid is none: this means there is no solution!
            print("The input file does not define a valid problem.")
            exit(1)


if __name__ == '__main__':
    main(sys.argv)
