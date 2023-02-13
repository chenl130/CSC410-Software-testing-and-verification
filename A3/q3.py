#!/usr/bin/env python3
"""
CSC410 Assignment 2 - SAT and SMT.
Problem 2: Solving Hidato with a SMT Solver.
by Victor Nicolet
"""
# You cannot import any other modules. Put all your helper functions in this file
# You can only use Bool and propositional logic
from z3 import Solver, Bool, And, Xor, Or, Not, BoolRef
from itertools import combinations
from typing import *
from time import time
from math import log
import sys


# ================================================================================
#  ⚠️ Do not modify above!
# ================================================================================
def get_all_pairs(lst: Iterable):
    return [(d1, d2) for i, d1 in enumerate(lst) for d2 in lst[i + 1:]]

def get_neighbors(vars: List[List[BoolRef]], i: int, j: int, c: int, width: int, height: int):
    neighbors = []
    for x in range(-1, 2):
        for y in range(-1, 2):
            if (x != 0 or y != 0) and 0 <= i+x < height and 0 <= j+y < width:
                idx = (i+x) * width + j + y
                neighbors.append(vars[idx][c])

    return neighbors


def solve(grid: List[List[Union[str, int]]]) -> List[List[Union[str, int]]]:
    """
    This function solves the Hidato puzzle with the initial configuration stored in grid.
    You should ouput a grid in the same format, but where all the '-' have been replaced
    by numbers.
    """
    # TODO : solve the Hidato puzzle using Z3. grid[i][j] is either "-", "*" or an integer.
    # You must use SAT, i.e. only booleans and propositional logic!
    # IMPORTANT:
    # - Your python code should be polynomial in the size of the grid.
    #   You cannot use any search algorithm or backtracking.

    # Return the completed grid if a solution exists. Otherwise, return None.
    width = len(grid[0])
    variables = [[] for _ in range(len(grid)*width)]
    n = 0
    s = Solver()
    clauses = []
    # Count number of filled and unfilled cells in grid
    for i in range(len(grid)):
        for j in range(len(grid[i])):
            if grid[i][j] != "*":
                n += 1

    # Generate boolean variables
    for i in range(len(grid)):
        for j in range(len(grid[i])):
            variables[i*width + j] = [Bool("b%d%d%d" % (i, j, k)) for k in range(n+1)]

    # Each integer can only appear once in the grid (not including 0)
    for k in range(1, n+1):
        for (idx1, idx2) in get_all_pairs([i for i in range(len(variables))]):
            clauses.append(Or(Not(variables[idx1][k]), Not(variables[idx2][k])))
            
    for i in range(len(grid)):
        for j in range(len(grid[i])):
            idx = i * width + j
            if isinstance(grid[i][j], int):
                # Include hints to propositional logic formula
                clauses.append(variables[idx][grid[i][j]])
            elif grid[i][j] == "-":
                # Every unfilled cell needs an integer from 1 to n
                clauses.append(Or([variables[idx][k] for k in range(1, n+1)]))
            else:
                # Every blocked cell has value 0
                clauses.append(variables[idx][0])
            
            # Every cell can only have one integer value
            for (d1, d2) in get_all_pairs([i for i in range(n+1)]):
                clauses.append(Or(Not(variables[idx][d1]), Not(variables[idx][d2])))

            for k in range(1, n+1):
                if k != 1:
                    # One of this cell's neighbors must have value k-1
                    neighbors = get_neighbors(variables, i, j, k-1, width, len(grid))
                    clauses.append(Or(neighbors + [Not(variables[idx][k])]))
                if k != n:
                    # One of this cell's neighbors must have value k+1
                    neighbors = get_neighbors(variables, i, j, k+1, width, len(grid))
                    clauses.append(Or(neighbors + [Not(variables[idx][k])]))
    
    for clause in clauses:
        s.add(clause)

    #print(clauses)

    resp = s.check()
    print(resp)
    if str(resp) == "sat":
        m = s.model()
        solution = [[] for _ in range(len(grid))]
        for i in range(len(grid)):
            for j in range(len(grid[i])):
                for k in range(n+1):
                    if m.evaluate(variables[i*width+j][k]):
                        if k == 0:
                            solution[i].append("*")
                        else:
                            solution[i].append(k)

        return solution
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
            break


def main(argv: List[str]) -> None:
    if len(argv) < 2:
        print("Usage: python3 q3.py INPUT_FILE")
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
