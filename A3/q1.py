#!/usr/bin/env python3
"""
CSC410 Assignment 2 - SAT and SMT.
Problem 1: Encodings of At-Most-k
by Victor Nicolet
"""
# You cannot import any other modules. Put all your helper functions in this file
import time
from z3 import *
import itertools
import sys
from typing import *

# ================================================================================
# ⚠️ Do not modify above!
# Your task is to write the functions 'naive' and 'sequential_counter' below.
# Also, don't forget to add your performance comparison in the comments.
# If you want to write your own automated tests, you can import this file into
# another file.
# Good luck!
# ================================================================================

def all_k_combinations_util(n: int, left: int, k: int) -> List[List[int]]:
    # Prerequisites: n >= k >= 0 and n >= left >= 1
    # Return all combinations of the digits left to n - 1 of size k
    combinations = []
    if (k == 0):
        return []
    else:
        for i in range(left, n - k + 1): #n - i >= k
            prev_combinations = all_k_combinations_util(n, i + 1, k - 1)
            if (len(prev_combinations) == 0 and k == 1):
                combinations.append([i])
            else:
                combinations.extend([[i] + c for c in prev_combinations])
        
    return combinations


def all_k_combinations(n: int, k: int) -> List[List[int]]:
    # Prerequisites: n >= k >= 0
    # Return all combinations of the digits 0 to n - 1 of size k
    return all_k_combinations_util(n, 0, k)
    

def naive(literals: List[BoolRef], k: int, c: int = 0) -> List[BoolRef]:
    """
    Design your naive encoding of the at-most-k constraint.
    You are not allowed to create new variables for this encoding.
    The function returns the list of clauses that encode the at-most-k contraint.
    NOTE:
    The parameter c can be used to store temporary information that needs to be
    passed onto the next call of sequential_counter (see the test function.)
    Using it is not mandatory. c can only be an integer.
    """
    clauses = []
    combinations = all_k_combinations(len(literals), k+1)
    for combination in combinations:
        clauses.append(Or([Not(literals[i]) for i in combination]))
            
    return clauses, c


def sequential_counter(literals: List[BoolRef], k: int, c: int = 0) -> List[BoolRef]:
    """
    Implement the sequential counter encoding of the at-most-k constraint.
    You have to create new variables for this encoding.
    The function returns the list of clauses that encode the at-most-k constraint.
    NOTE:
    The parameter c can be used to store temporary information that needs to be
    passed onto the next call of sequential_counter (see the test function).
    Using it is not mandatory. c can only be an integer.
    """
    clauses = []
    if k == 0:
        clauses.append(And([Not(x) for x in literals]))
        if c == 0:
            return clauses, 1
        else:
            return clauses, c
        
    n = len(literals)
    tempLiterals = [None] + literals
    if c == 0:
        varRs = [[Bool(f"R{i},{j}") for j in range(k + 1)] for i in range(n + 1)]
        c = 1
    else:
        varRs = [[Bool(f"RR{i},{j}") for j in range(k + 1)] for i in range(n + 1)]
        
    c1 = Or(Not(tempLiterals[1]), varRs[1][1])
    c2 = And([Not(varRs[1][j]) for j in range(2, k+1)])
    c3 = And([Or(Not(tempLiterals[i]), varRs[i][1]) for i in range(2, n)])
    c4 = And([Or( Not(varRs[i-1][1]), varRs[i][1] ) for i in range(2, n)])
    c5 = And([Or(Not(tempLiterals[i]), Not(varRs[i-1][j-1]), varRs[i][j]) for j in range(2, k+1) for i in range(2, n)])
    c6 = And([Or(Not(varRs[i-1][j]),varRs[i][j]) for j in range(2, k+1) for i in range(2, n)])
    c7 = And([Or(Not(tempLiterals[i]), Not(varRs[i-1][k])) for i in range(2, n)])
    c8 = Or(Not(tempLiterals[n]), Not(varRs[n-1][k]))
    clauses.append(c1)
    clauses.append(c2)
    clauses.append(c3)
    clauses.append(c4)
    clauses.append(c5)
    clauses.append(c6)
    clauses.append(c7)
    clauses.append(c8)
    return clauses, c

# ===
# - Is the performance difference between the two encodings significant?
# TODO : your response in comments here.
# The naive approach is much slower at converging to a solution than the sequential counter method.
# For exmple, for n = 20 and k = 10 the naive encoding solved the SAT problem in 0.869 seconds but the sequential
# counter encoding solved it in 0.00392 seconds.
# This is because the naive approach computes n choose k+1 clauses whereas the sequential counter method computes 2nk + n - 3k - 1 clauses.
# Even though the sequential counter encoding adds O(nk) more variables, the reduction in the number of clauses from
# n choose k+1 to O(nk) dramatically improved the SAT solver's performance.
# ===

# ================================================================================
#  ⚠️ Do not modify below!
# ================================================================================


def test(encoding_function, n: int, k: int) -> None:
    """
    The following test encodes the constraint of having exactly k variables true by
    encoding at-most-k over (X_1, .., X_n) and at-least-k:
    - at-most-k is encoded by the encoding function given as argument.
    - at-least-k is encoded by encoding at-most-(n-k) on the negation of the variables.
    """
    X = []
    for i in range(n):
        X += [Bool("b%d" % i)]
    s = Solver()
    at_most_k, c = encoding_function(X, k)
    # Parameter c returned in previous call is passed as argument in next call.
    # Use it if you need it - but you cannot modify this code.
    at_least_k, c = encoding_function([Not(x) for x in X], n - k, c)
    # Add all the clauses to the solver
    for clause in at_most_k + at_least_k:
        s.add(clause)
    # Should print sat
    start = time.time()
    resp = s.check()
    end = time.time()
    print(resp)
    if str(resp) == "sat":
        m = s.model()
        count_true = 0
        for x in X:
            try:
                if m.evaluate(x):
                    count_true += 1
            except Z3Exception:
                pass
        if count_true == k:
            print("PASSED in %fs" % (end - start))
        else:
            print("FAILED")
    else:
        print("FAILED")


def usage():
    print("Usage: python3 q1.py E N K")
    print("      - E is 0 to use naive encoding or 1 to use sequential counter encoding.")
    print("      - K and N two integers such that N >= K > 2.")


def main(argv):
    if len(argv) < 4:
        usage()
        exit(1)
    e, n, k = int(argv[1]) == 0, int(argv[2]), int(argv[3])
    if not (n >= k > 2):
        usage()
        exit(1)
    if e:
        test(naive, n, k)
    else:
        test(sequential_counter, n, k)


if __name__ == '__main__':
    main(sys.argv)
