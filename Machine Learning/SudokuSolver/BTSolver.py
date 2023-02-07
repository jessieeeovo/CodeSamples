import SudokuBoard
import Variable
import Domain
import Trail
import Constraint
import ConstraintNetwork
import time
import random


class BTSolver:

    # ==================================================================
    # Constructors
    # ==================================================================

    def __init__(self, gb, trail, val_sh, var_sh, cc):
        self.network = ConstraintNetwork.ConstraintNetwork(gb)
        self.hassolution = False
        self.gameboard = gb
        self.trail = trail

        self.varHeuristics = var_sh
        self.valHeuristics = val_sh
        self.cChecks = cc

    # ==================================================================
    # Consistency Checks
    # ==================================================================

    # Basic consistency check, no propagation done
    def assignmentsCheck(self):
        for c in self.network.getConstraints():
            if not c.isConsistent():
                return False
        return True

    """
        Part 1: Implement the Forward Checking Heuristic

        This function will do both Constraint Propagation and check
        the consistency of the network

        (1) If a variable is assigned then eliminate that value from
            the square's neighbors.

        Return: a tuple of a dictionary and a bool. The dictionary contains all MODIFIED variables, mapped to their MODIFIED domain.
                The bool is true if assignment is consistent, false otherwise.
    """

    def forwardChecking(self):
        dic = {}
        assigned_variables = []
        for var in self.network.getVariables():
            if var.isAssigned():
                assigned_variables.append(var)
        while assigned_variables != []:
            var = assigned_variables.pop(0)
            neighbors = self.network.getNeighborsOfVariable(var)
            for neighbor in neighbors:
                if var.getAssignment() in neighbor.getValues():
                    self.trail.push(neighbor)
                    neighbor.removeValueFromDomain(var.getAssignment())
                    if len(neighbor.getValues()) == 0:
                        return (dic, False)
                    if len(neighbor.getValues()) == 1:
                        neighbor.assignValue(neighbor.getValues()[0])
                        assigned_variables.append(neighbor)
                    dic[neighbor] = neighbor.getDomain()
        return (dic, True)

    # =================================================================
    # Arc Consistency
    # =================================================================
    def arcConsistency(self):
        assignedVars = []
        for c in self.network.constraints:
            for v in c.vars:
                if v.isAssigned():
                    assignedVars.append(v)
        while len(assignedVars) != 0:
            av = assignedVars.pop(0)
            for neighbor in self.network.getNeighborsOfVariable(av):
                if neighbor.isChangeable and not neighbor.isAssigned() and neighbor.getDomain().contains(
                        av.getAssignment()):
                    neighbor.removeValueFromDomain(av.getAssignment())
                    if neighbor.domain.size() == 1:
                        neighbor.assignValue(neighbor.domain.values[0])
                        assignedVars.append(neighbor)

    """
        Part 2: Implement both of Norvig's Heuristics

        This function will do both Constraint Propagation and check
        the consistency of the network

        (1) If a variable is assigned then eliminate that value from
            the square's neighbors.

        (2) If a constraint has only one possible place for a value
            then put the value there.

        Return: a pair of a dictionary and a bool. The dictionary contains all variables 
		        that were ASSIGNED during the whole NorvigCheck propagation, and mapped to the values that they were assigned.
                The bool is true if assignment is consistent, false otherwise.
    """

    def norvigCheck(self):
        dic = {}
        _, isConsistent = self.forwardChecking()
        if not isConsistent:
            return ({}, False)

        for constraint in self.network.getConstraints():
            counter = [0] * self.gameboard.N
            for i in range(self.gameboard.N):
                for var in constraint.vars:
                    for k in var.getValues():
                        counter[i] += 1
            for i in range(self.gameboard.N):
                if counter[i] == 1:
                    for var in constraint.vars:
                        if not var.isAssigned():
                            for val in var.getValues():
                                if val == i + 1:
                                    self.trail.push(var)
                                    var.assignValue(val)
        return (dic, True)

    def getTournCC(self):
        return self.norvigCheck()

    # ==================================================================
    # Variable Selectors
    # ==================================================================

    # Basic variable selector, returns first unassigned variable
    def getfirstUnassignedVariable(self):
        for v in self.network.variables:
            if not v.isAssigned():
                return v

        # Everything is assigned
        return None

    """
        Part 1: Implement the Minimum Remaining Value Heuristic

        Return: The unassigned variable with the smallest domain
    """

    def getMRV(self):
        unassignedVars = [x for x in self.network.getVariables() if not x.isAssigned()]
        if len(unassignedVars) == 0:
            return None
        mrv = unassignedVars.pop(0)
        for var in unassignedVars:
            if var.size() < mrv.size():
                mrv = var
        return mrv

    """
        Part 2: Implement the Minimum Remaining Value Heuristic
                       with Degree Heuristic as a Tie Breaker

        Return: The unassigned variable with the smallest domain and affecting the  most unassigned neighbors.
                If there are multiple variables that have the same smallest domain with the same number of unassigned neighbors, add them to the list of Variables.
                If there is only one variable, return the list of size 1 containing that variable.
    """

    def MRVwithTieBreaker(self):
        dic = {}
        result = 0
        variables = [x for x in self.network.getVariables() if not x.isAssigned()]
        if len(variables) == 1:
            return variables
        elif len(variables) == 0:
            return [None]
        for var in variables:
            if var.size() not in dic:
                dic[var.size()] = [var]
            else:
                dic[var.size()].append(var)
        domain_lst = []
        for key in dic:
            domain_lst.append(key)
        small_num = 100000000000000
        for num in domain_lst:
            if num < small_num:
                small_num = num
        if len(dic[small_num]) == 1:
            return dic[small_num]
        else:
            big_num = 0
            for var in dic[small_num]:
                if len(self.network.getNeighborsOfVariable(var)) > big_num:
                    big_num = len(self.network.getNeighborsOfVariable(var))
                    result = var
            return [result]

    def getTournVar(self):
        return self.MRVwithTieBreaker()[0]

    # ==================================================================
    # Value Selectors
    # ==================================================================

    # Default Value Ordering
    def getValuesInOrder(self, v):
        values = v.domain.values
        return sorted(values)

    """
        Part 1: Implement the Least Constraining Value Heuristic

        The Least constraining value is the one that will knock the least
        values out of it's neighbors domain.

        Return: A list of v's domain sorted by the LCV heuristic
                The LCV is first and the MCV is last
    """

    def getValuesLCVOrder(self, v):
        lst = []
        dic = {}
        neighbors = self.network.getNeighborsOfVariable(v)
        for var in v.domain.values:
            dic[var] = 0
            for neighbor in neighbors:
                if not neighbor.isAssigned() and neighbor.getDomain().contains(var):
                    dic[var] += 1
        sorted_lst = sorted(dic.items(), key=lambda x: (x[1], x[0]))
        for item in sorted_lst:
            lst.append(item[0])
        return lst

    def getTournVal(self, v):
        return self.getValuesLCVOrder(v)

    # ==================================================================
    # Engine Functions
    # ==================================================================

    def solve(self, time_left=600):
        if time_left <= 60:
            return -1

        start_time = time.time()
        if self.hassolution:
            return 0

        # Variable Selection
        v = self.selectNextVariable()

        # check if the assigment is complete
        if (v == None):
            # Success
            self.hassolution = True
            return 0

        # Attempt to assign a value
        for i in self.getNextValues(v):

            # Store place in trail and push variable's state on trail
            self.trail.placeTrailMarker()
            self.trail.push(v)

            # Assign the value
            v.assignValue(i)

            # Propagate constraints, check consistency, recur
            if self.checkConsistency():
                elapsed_time = time.time() - start_time
                new_start_time = time_left - elapsed_time
                if self.solve(time_left=new_start_time) == -1:
                    return -1

            # If this assignment succeeded, return
            if self.hassolution:
                return 0

            # Otherwise backtrack
            self.trail.undo()

        return 0

    def checkConsistency(self):
        if self.cChecks == "forwardChecking":
            return self.forwardChecking()[1]

        if self.cChecks == "norvigCheck":
            return self.norvigCheck()[1]

        if self.cChecks == "tournCC":
            return self.getTournCC()

        else:
            return self.assignmentsCheck()

    def selectNextVariable(self):
        if self.varHeuristics == "MinimumRemainingValue":
            return self.getMRV()

        if self.varHeuristics == "MRVwithTieBreaker":
            return self.MRVwithTieBreaker()[0]

        if self.varHeuristics == "tournVar":
            return self.getTournVar()

        else:
            return self.getfirstUnassignedVariable()

    def getNextValues(self, v):
        if self.valHeuristics == "LeastConstrainingValue":
            return self.getValuesLCVOrder(v)

        if self.valHeuristics == "tournVal":
            return self.getTournVal(v)

        else:
            return self.getValuesInOrder(v)

    def getSolution(self):
        return self.network.toSudokuBoard(self.gameboard.p, self.gameboard.q)
