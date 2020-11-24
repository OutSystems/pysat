#!/usr/bin/env python
#-*- coding:utf-8 -*-
##
## lsu.py
##
##  Created on: Aug 29, 2018
##      Author: Miguel Neves
##      E-mail: neves@sat.inesc-id.pt
##

"""
    ===============
    List of classes
    ===============

    .. autosummary::
        :nosignatures:

        LSU
        LSUPlus

    ==================
    Module description
    ==================

    The module implements a prototype of the known *LSU/LSUS*, e.g. *linear
    (search) SAT-UNSAT*, algorithm for MaxSAT, e.g. see [1]_.  The
    implementation is improved by the use of the *iterative totalizer encoding*
    [2]_. The encoding is used in an incremental fashion, i.e. it is created
    once and reused as many times as the number of iterations the algorithm
    makes.

    .. [1] António Morgado, Federico Heras, Mark H. Liffiton, Jordi Planes,
        Joao Marques-Silva. *Iterative and core-guided MaxSAT solving: A
        survey and assessment*. Constraints 18(4). 2013. pp. 478-534

    .. [2] Ruben Martins, Saurabh Joshi, Vasco M. Manquinho, Inês Lynce.
        *Incremental Cardinality Constraints for MaxSAT*. CP 2014. pp. 531-548

    The implementation can be used as an executable (the list of available
    command-line options can be shown using ``lsu.py -h``) in the following
    way:

    ::

        $ xzcat formula.wcnf.xz
        p wcnf 3 6 4
        1 1 0
        1 2 0
        1 3 0
        4 -1 -2 0
        4 -1 -3 0
        4 -2 -3 0

        $ lsu.py -s glucose3 -m -v formula.wcnf.xz
        c formula: 3 vars, 3 hard, 3 soft
        o 2
        s OPTIMUM FOUND
        v -1 -2 3 0
        c oracle time: 0.0000

    Alternatively, the algorithm can be accessed and invoked through the
    standard ``import`` interface of Python, e.g.

    .. code-block:: python

        >>> from pysat.examples.lsu import LSU
        >>> from pysat.formula import WCNF
        >>>
        >>> wcnf = WCNF(from_file='formula.wcnf.xz')
        >>>
        >>> lsu = LSU(wcnf, verbose=0)
        >>> lsu.solve()  # set of hard clauses should be satisfiable
        True
        >>> print(lsu.cost) # cost of MaxSAT solution should be 2
        >>> 2
        >>> print(lsu.model)
        [-1, -2, 3]

    ==============
    Module details
    ==============
"""

#
#==============================================================================
from __future__ import print_function
import getopt
from pysat.card import ITotalizer
from pysat.pb import EncType, PBEnc
from pysat.formula import CNF, WCNF, WCNFPlus, IDPool
from pysat.solvers import Solver
from threading import Timer
import os
import sys
import re


# TODO: support weighted MaxSAT
#==============================================================================
class LSU:
    """
        Linear SAT-UNSAT algorithm for MaxSAT [1]_. The algorithm can be seen
        as a series of satisfiability oracle calls refining an upper bound on
        the MaxSAT cost, followed by one unsatisfiability call, which stops the
        algorithm. The implementation encodes the sum of all selector literals
        using the *iterative totalizer encoding* [2]_. At every iteration, the
        upper bound on the cost is reduced and enforced by adding the
        corresponding unit size clause to the working formula. No clauses are
        removed during the execution of the algorithm. As a result, the SAT
        oracle is used incrementally.

        .. warning:: At this point, :class:`LSU` supports only
            **unweighted** problems.

        The constructor receives an input :class:`.WCNF` formula, a name of the
        SAT solver to use (see :class:`.SolverNames` for details), and an
        integer verbosity level.

        :param formula: input MaxSAT formula
        :param solver: name of SAT solver
        :param pb_enc_type: PB encoding type to use for solving weighted problems
        :param expect_interrupt: whether or not an :meth:`interrupt` call is expected
        :param verbose: verbosity level

        :type formula: :class:`.WCNF`
        :type solver: str
        :type expect_interrupt: bool
        :type verbose: int
    """

    def __init__(self, formula, solver='g4', pb_enc_type=EncType.best, expect_interrupt=False, verbose=0):
        """
            Constructor.
        """

        self.verbose = verbose
        self.solver = solver
        self.pb_enc_type = pb_enc_type
        self.expect_interrupt = expect_interrupt
        self.formula = formula
        self.vpool = IDPool(occupied=[(1, formula.nv)])     # variable pool used for managing card/PB encodings
        self.sels = []                                      # soft clause selector variables
        self.is_weighted = False                            # auxiliary flag indicating if it's a weighted problem
        self.tot = None                                     # totalizer encoder for the cardinality constraint
        self._init(formula)                                 # initialize SAT oracle

    def _init(self, formula):
        """
            SAT oracle initialization. The method creates a new SAT oracle and
            feeds it with the formula's hard clauses. Afterwards, all soft
            clauses of the formula are augmented with selector literals and
            also added to the solver. The list of all introduced selectors is
            stored in variable ``self.sels``.

            :param formula: input MaxSAT formula
            :type formula: :class:`WCNF`
        """

        self.oracle = Solver(name=self.solver, bootstrap_with=formula.hard,
                incr=True, use_timer=True)

        for i, cl in enumerate(formula.soft):
            # TODO: if clause is unit, use its literal as selector
            # (ITotalizer must be extended to support PB constraints first)
            selv = self.vpool._next()
            cl.append(selv)
            self.oracle.add_clause(cl)
            self.sels.append(selv)
        self.is_weighted = any(w > 1 for w in formula.wght)

        if self.verbose > 1:
            print('c formula: {0} vars, {1} hard, {2} soft'.format(formula.nv, len(formula.hard), len(formula.soft)))

    def __del__(self):
        """
            Destructor.
        """

        self.delete()

    def __enter__(self):
        """
            'with' constructor.
        """

        return self

    def __exit__(self, exc_type, exc_value, traceback):
        """
            'with' destructor.
        """

        self.delete()

    def delete(self):
        """
            Explicit destructor of the internal SAT oracle and the
            :class:`.ITotalizer` object.
        """

        if self.oracle:
            self.oracle.delete()
            self.oracle = None

        if self.tot:
            self.tot.delete()
            self.tot = None

    def solve(self):
        """
            Computes a solution to the MaxSAT problem. The method implements
            the LSU/LSUS algorithm, i.e. it represents a loop, each iteration
            of which calls a SAT oracle on the working MaxSAT formula and
            refines the upper bound on the MaxSAT cost until the formula
            becomes unsatisfiable.

            Returns ``True`` if the hard part of the MaxSAT formula is
            satisfiable, i.e. if there is a MaxSAT solution, and ``False``
            otherwise.

            :rtype: bool
        """

        is_sat = False

        while self.oracle.solve_limited(expect_interrupt=self.expect_interrupt):
            is_sat = True
            self.model = self.oracle.get_model()
            self.cost = self._get_model_cost(self.formula, self.model)
            if self.verbose:
                print('o {0}'.format(self.cost))
                sys.stdout.flush()
            if self.cost == 0:      # if cost is 0, then model is an optimum solution
                break
            self._assert_lt(self.cost)

        if is_sat:
            self.model = filter(lambda l: abs(l) <= self.formula.nv, self.model)
            if self.verbose:
                if self.found_optimum():
                    print('s OPTIMUM FOUND')
                else:
                    print('s SATISFIABLE')
        elif self.verbose:
            print('s UNSATISFIABLE')

        return is_sat

    def get_model(self):
        """
            This method returns a model obtained during a prior satisfiability
            oracle call made in :func:`solve`.

            :rtype: list(int)
        """

        return self.model

    def found_optimum(self):
        """
            Checks if the optimum solution was found in a prior call to
            :func:`solve`.

            :rtype: bool
        """

        return self.oracle.get_status() is not None

    def _get_model_cost(self, formula, model):
        """
            Given a WCNF formula and a model, the method computes the MaxSAT
            cost of the model, i.e. the sum of weights of soft clauses that are
            unsatisfied by the model.

            :param formula: an input MaxSAT formula
            :param model: a satisfying assignment

            :type formula: :class:`.WCNF`
            :type model: list(int)

            :rtype: int
        """

        model_set = set(model)
        cost = 0

        for cl, w in zip(formula.soft, formula.wght):
            cost += w if all(l not in model_set for l in filter(lambda l: abs(l) <= self.formula.nv, cl)) else 0

        return cost

    def _assert_lt(self, cost):
        """
            The method enforces an upper bound on the cost of the MaxSAT
            solution. For unweighted problems, this is done by encoding the sum
            of all soft clause selectors with the use the iterative totalizer
            encoding, i.e. :class:`.ITotalizer`. Note that the sum is created
            once, at the beginning. Each of the following calls to this method
            only enforces the upper bound on the created sum by adding the
            corresponding unit size clause. For weighted problems, the PB
            encoding given through the :meth:`__init__` method is used.
            Each such clause is added on the fly with no restart of the
            underlying SAT oracle.

            :param cost: the cost of the next MaxSAT solution is enforced to be
                *lower* than this current cost

            :type cost: int
        """

        if self.is_weighted:
            # TODO: use incremental PB encoding
            self.oracle.append_formula(PBEnc.leq(self.sels, weights=self.formula.wght, bound=cost-1, vpool=self.vpool))
        else:

            if self.tot is None:
                self.tot = ITotalizer(lits=self.sels, ubound=cost-1, top_id=self.vpool.top)
                self.vpool.top = self.tot.top_id

                for cl in self.tot.cnf.clauses:
                    self.oracle.add_clause(cl)

            self.oracle.add_clause([-self.tot.rhs[cost-1]])

    def interrupt(self):
        """
            Interrupt the current execution of LSU's :meth:`solve` method.
            Can be used to enforce time limits using timer objects. The
            interrupt must be cleared before running the LSU algorithm again
            (see :meth:`clear_interrupt`).
        """

        self.oracle.interrupt()

    def clear_interrupt(self):
        """
            Clears an interruption.
        """

        self.oracle.clear_interrupt()

    def oracle_time(self):
        """
            Method for calculating and reporting the total SAT solving time.
        """

        return self.oracle.time_accum()


#
#==============================================================================
class LSUPlus(LSU, object):
    """
        LSU-like algorithm extended for :class:`.WCNFPlus` formulas (using
        :class:`.Minicard`).

        :param formula: input MaxSAT formula in WCNF+ format
        :param pb_enc_type: PB encoding type to use for solving weighted problems
        :param expect_interrupt: whether or not an :meth:`interrupt` call is expected
        :param verbose: verbosity level

        :type formula: :class:`.WCNFPlus`
        :type expect_interrupt: bool
        :type verbose: int
    """

    def __init__(self, formula, pb_enc_type=EncType.best, expect_interrupt=False, verbose=0):
        """
            Constructor.
        """

        super(LSUPlus, self).__init__(formula, solver='mc', pb_enc_type=pb_enc_type,
                expect_interrupt=expect_interrupt, verbose=verbose)

        # adding atmost constraints
        for am in formula.atms:
            self.oracle.add_atmost(*am)

    def _assert_lt(self, cost):
        """
            Overrides _assert_lt of :class:`.LSU` in order to use Minicard's
            native support for cardinality constraints

            :param cost: the cost of the next MaxSAT solution is enforced to
                be *lower* than this current cost

            :type cost: int
        """

        if self.is_weighted:
            super()._assert_lt(cost)
        else:
            self.oracle.add_atmost(self.sels, cost-1)


#
#==============================================================================
def parse_options():
    """
        Parses command-line options.
    """

    try:
        opts, args = getopt.getopt(sys.argv[1:], 'hms:e:t:v', ['help', 'model', 'solver=', 'pb-enc=', 'timeout=', 'verbose'])
    except getopt.GetoptError as err:
        sys.stderr.write(str(err).capitalize())
        print_usage()
        sys.exit(1)

    solver = 'g4'
    pb_enc = EncType.best
    verbose = 1
    print_model = False
    timeout = None

    for opt, arg in opts:
        if opt in ('-h', '--help'):
            print_usage()
            sys.exit(0)
        elif opt in ('-m', '--model'):
            print_model = True
        elif opt in ('-s', '--solver'):
            solver = str(arg)
        elif opt in ('-e', '--pb-enc'):
            pb_enc = int(arg)
        elif opt in ('-t', '--timeout'):
            if str(arg) != 'none':
                timeout = float(arg)
        elif opt in ('-v', '--verbose'):
            verbose += 1
        else:
            assert False, 'Unhandled option: {0} {1}'.format(opt, arg)

    return print_model, solver, pb_enc, timeout, verbose, args


#
#==============================================================================
def print_usage():
    """
        Prints usage message.
    """

    print('Usage: ' + os.path.basename(sys.argv[0]) + ' [options] dimacs-file')
    print('Options:')
    print('        -h, --help               Show this message')
    print('        -m, --model              Print model')
    print('        -s, --solver=<string>    SAT solver to use')
    print('                                 Available values: g3, g4, mc, m22, mgh (default = g4)')
    print('        -e, --pb-enc=<int>       PB encoding to use for weighted MaxSAT solving')
    print('                                 Available values: 0=best, 1=bdd, 2=seqcounter, 3=sortnetwork, 4=adder, 5=binmerge (default = 0)')
    print('        -t, --timeout=<float>    Set time limit for MaxSAT solver')
    print('                                 Available values: [0 .. FLOAT_MAX], none (default: none)')
    print('        -v, --verbose            Be verbose')


#
#==============================================================================
if __name__ == '__main__':
    print_model, solver, pb_enc, timeout, verbose, files = parse_options()

    if files:
        # reading standard CNF or WCNF
        if re.search('cnf(\.(gz|bz2|lzma|xz))?$', files[0]):
            if re.search('\.wcnf(\.(gz|bz2|lzma|xz))?$', files[0]):
                formula = WCNF(from_file=files[0])
            else:  # expecting '*.cnf'
                formula = CNF(from_file=files[0]).weighted()

            lsu = LSU(formula, solver=solver, pb_enc_type=pb_enc,
                    expect_interrupt=(timeout != None), verbose=verbose)

        # reading WCNF+
        elif re.search('\.wcnf[p,+](\.(gz|bz2|lzma|xz))?$', files[0]):
            formula = WCNFPlus(from_file=files[0])
            lsu = LSUPlus(formula, pb_enc_type=pb_enc,
                    expect_interrupt=(timeout != None), verbose=verbose)

        # setting a timer if necessary
        if timeout is not None:
            if verbose > 1:
                print('c timeout: {0}'.format(timeout))

            timer = Timer(timeout, lambda s: s.interrupt(), [lsu])
            timer.start()

        if lsu.solve():
            if print_model:
                print('v ' + ' '.join([str(l) for l in lsu.get_model()]), '0')

        if verbose > 1:
            print('c oracle time: {0:.4f}'.format(lsu.oracle_time()))

        if timeout is not None:
            timer.cancel()
    else:
        print_usage()
