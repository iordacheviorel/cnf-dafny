include "formula.dfy"
include "utils.dfy"

module CnfFormula
{
    import Utils
    import opened Formula

    predicate method validLiteral(lit : int)
    {
        lit <= -1 || lit >= 1
    }

    function method litToVar(l : int) : int
        requires validLiteral(l);
    {
        if (l <= -1) then
            (-l) - 1
        else
            l - 1
    }

    predicate validClause(clause : seq<int>)
    {
        forall lit :: lit in clause ==>
            validLiteral(lit)
    }

    lemma validClauseSmaller(clause : seq<int>)
        requires validClause(clause);
        requires |clause| > 0;
        ensures validClause(clause[1..]);
    {
        assert forall lit :: lit in clause ==> lit <= -1 || lit >= 1;
        assert forall lit :: lit in clause[1..] ==> lit in clause;
        assert forall lit :: lit in clause[1..] ==> lit <= -1 || lit >= 1;
    }

    predicate validCnfFormula(f : seq<seq<int>>)
    {
        forall clause : seq<int> :: clause in f ==>
            validClause(clause)
    }

    predicate variableInInterval(v : int, n : int, start : int, end : int)
        requires validVariable(v);
        requires 0 <= n <= start <= end;
    {
        0 <= v < n || start <= v < end
    }

    predicate variablesInIntervalLiteral(lit : int,
        n : int, start : int, end : int)
        requires validLiteral(lit);
        requires 0 <= n <= start <= end;
        ensures variablesInIntervalLiteral(lit, n, start, end) ==>
            variablesUpToLiteral(lit, end);
    {
        variableInInterval(litToVar(lit), n, start, end)
    }

    predicate variablesInIntervalClause(cl : seq<int>,
        n : int, start : int, end : int)
        requires validClause(cl);
        requires 0 <= n <= start <= end;
        ensures variablesInIntervalClause(cl, n, start, end) ==>
            variablesUpToClause(cl, end);
    {
        (forall lit : int :: lit in cl ==>
            variablesInIntervalLiteral(lit, n, start, end))
    }

    predicate variablesInInterval(f : seq<seq<int>>,
        n : int, start : int, end : int)
        // all variables in [0, n) or [start, end)
        requires validCnfFormula(f);
        requires 0 <= n <= start <= end;
        ensures variablesInInterval(f, n, start, end) ==>
            variablesUpToCnfFormula(f, end);
    {
        forall cl : seq<int> :: cl in f ==>
            variablesInIntervalClause(cl, n, start, end)
    }

    lemma varsUpToNM(f : FormulaT, n : int, nm : int)
        requires variablesUpTo(f, n);
        requires nm >= n;
        ensures variablesUpTo(f, nm);
    {
    }

    predicate validVariable(v : int)
    {
        v >= 0
    }

    function method posVarToLit(v : int) : int
        requires validVariable(v);
        ensures posVarToLit(v) >= 1;
        ensures validLiteral(posVarToLit(v));
    {
        v + 1
    }

    function method negVarToLit(v : int) : int
        requires validVariable(v);
        ensures negVarToLit(v) <= -1;
        ensures validLiteral(negVarToLit(v));
    {
        (-v) - 1
    }

    predicate variablesUpToLiteral(lit : int, n : int)
        requires n >= 0;
        requires validLiteral(lit);
    {
        0 <= litToVar(lit) < n
    }

    predicate variablesUpToClause(clause : seq<int>, n : int)
        requires n >= 0;
        requires validClause(clause);
    {
        forall lit :: lit in clause ==> variablesUpToLiteral(lit, n)
    }

    predicate variablesUpToCnfFormula(rf : seq<seq<int>>, n : int)
        requires n >= 0;
        requires validCnfFormula(rf);
    {
        forall clause :: clause in rf ==> variablesUpToClause(clause, n)
    }

    lemma variablesUpToCnfFormulaMonotone(rf : seq<seq<int>>, n : int, n' : int)
        requires validCnfFormula(rf);
        requires 0 <= n <= n';
        requires variablesUpToCnfFormula(rf, n);
        ensures variablesUpToCnfFormula(rf, n');
    {
    }
    
    function method maxVarLiteral(literal : int) : int
        requires validLiteral(literal);
        ensures maxVarLiteral(literal) >= 0;
        ensures litToVar(literal) < maxVarLiteral(literal);
        ensures variablesUpToLiteral(literal, maxVarLiteral(literal));
    {
        litToVar(literal) + 1
    }
    
    function method maxVarClause(clause : seq<int>) : int
        requires validClause(clause);
        ensures maxVarClause(clause) >= 0;
        ensures forall lit :: lit in clause ==> litToVar(lit) < maxVarClause(clause);
        ensures variablesUpToClause(clause, maxVarClause(clause));
    {
        if |clause| == 0 then
            0
        else
            var maxRecursive := maxVarClause(clause[1..]);
            var result := Utils.max(maxVarLiteral(clause[0]), maxRecursive);
            result
    }
    
    lemma variablesUpToMaxVarLiteral(lit : int, n : int)
        requires n >= 0;
        requires validLiteral(lit);
        requires variablesUpToLiteral(lit, n);
        ensures n >= maxVarLiteral(lit);
    {
    }

    lemma variablesUpToMaxVarClause(clause : seq<int>, n : int)
        requires n >= 0;
        requires validClause(clause);
        requires variablesUpToClause(clause, n);
        ensures n >= maxVarClause(clause);
    {
        if (|clause| == 0) {
        } else {
            variablesUpToMaxVarLiteral(clause[0], n);
            variablesUpToMaxVarClause(clause[1..], n);
        }
    }
    
    lemma variablesUpToMaxVarCnfFormula(rf : seq<seq<int>>, n : int)
        requires n >= 0;
        requires validCnfFormula(rf);
        requires variablesUpToCnfFormula(rf, n);
        ensures n >= maxVarCnfFormula(rf);
    {
        if (|rf| == 0) {
        } else {
            variablesUpToMaxVarClause(rf[0], n);
            variablesUpToMaxVarCnfFormula(rf[1..], n);
        }
    }

    function method maxVarCnfFormula(rf : seq<seq<int>>) : int
        requires validCnfFormula(rf);
        ensures maxVarCnfFormula(rf) >= 0;
        ensures forall clause | clause in rf ::
            variablesUpToClause(clause, maxVarCnfFormula(rf));
        ensures variablesUpToCnfFormula(rf, maxVarCnfFormula(rf));
    {
        if |rf| == 0 then
            assert variablesUpToCnfFormula(rf, 0);
            0
        else
            var result := Utils.max(maxVarClause(rf[0]), maxVarCnfFormula(rf[1..]));
            assert variablesUpToClause(rf[0], result);
            assert forall clause :: clause in rf[1..] ==> variablesUpToClause(clause, result);
            assert variablesUpToCnfFormula(rf, result);
            result
    }

    predicate truthValueCnfFormula(rf : seq<seq<int>>, tau : seq<bool>)
        requires validCnfFormula(rf);
        requires variablesUpToCnfFormula(rf, |tau|);
    {
        forall clause | clause in rf ::
            truthValueClause(clause, tau)
    }

    predicate truthValueLiteral(lit : int, tau : seq<bool>)
        requires validLiteral(lit);
        requires variablesUpToLiteral(lit, |tau|);
    {
        if lit < 0 then
            ! tau[litToVar(lit)]
        else
            tau[litToVar(lit)]
    }

    lemma negateLiteral(v : int, tau : seq<bool>)
        requires validVariable(v);
        requires |tau| > v;
        ensures truthValueLiteral(negVarToLit(v), tau) ==
            !truthValueLiteral(posVarToLit(v), tau);
    {
    }

    predicate truthValueClause(clause : seq<int>, tau : seq<bool>)
        requires validClause(clause);
        requires variablesUpToClause(clause, |tau|);
    {
        exists lit :: lit in clause &&
            truthValueLiteral(lit, tau)
    }

    predicate agree(tau1 : seq<bool>, tau2 : seq<bool>, start : int, end : int)
        requires 0 <= start <= end;
        requires |tau1| >= end;
        requires |tau2| >= end;
    {
        tau1[start..end] == tau2[start..end]
    }
    
    lemma assignmentRelevantCnfFormula(rf : seq<seq<int>>,
        tau : seq<bool>, tau' : seq<bool>, n : int)
        requires n >= 0;
        requires validCnfFormula(rf);
        requires variablesUpToCnfFormula(rf, n);
        requires |tau| >= n;
        requires |tau'| >= n;
        requires agree(tau, tau', 0, n);
        ensures truthValueCnfFormula(rf, tau) ==
            truthValueCnfFormula(rf, tau');
    {
    }
    
    lemma transferTruthValue(rf : seq<seq<int>>,
        tau : seq<bool>, tau' : seq<bool>,
        n : int, start : int, end : int)
        requires validCnfFormula(rf);
        requires 0 <= n <= start <= end;
        requires variablesInInterval(rf, n, start, end);
        requires |tau| >= end;
        requires |tau'| >= end;
        requires agree(tau, tau', 0, n);
        requires agree(tau, tau', start, end);
        ensures truthValueCnfFormula(rf, tau) == truthValueCnfFormula(rf, tau');
    {
        forall clause | clause in rf
            ensures truthValueClause(clause, tau) == truthValueClause(clause, tau')
        {
            transferTruthValueClause(clause, tau, tau', n, start, end);           }
    }

    lemma transferTruthValueLit(lit : int, tau : seq<bool>, tau' : seq<bool>, n : int, start : int, end : int)
        requires validLiteral(lit);
        requires 0 <= n <= start <= end;
        requires variablesInIntervalLiteral(lit, n, start, end);
        requires |tau| >= end;
        requires |tau'| >= end;
        requires agree(tau, tau', 0, n);
        requires agree(tau, tau', start, end);
        ensures truthValueLiteral(lit, tau) == truthValueLiteral(lit, tau');
    {
        assert 0 <= litToVar(lit) < n ||
            start <= litToVar(lit) < end;
        assert tau[litToVar(lit)] == tau'[litToVar(lit)];
    }

    lemma transferTruthValueClause(clause : seq<int>, tau : seq<bool>, tau' : seq<bool>, n : int, start : int, end : int)
        requires validClause(clause);
        requires 0 <= n <= start <= end;
        requires variablesInIntervalClause(clause, n, start, end);
        requires |tau| >= end;
        requires |tau'| >= end;
        requires agree(tau, tau', 0, n);
        requires agree(tau, tau', start, end);
        ensures truthValueClause(clause, tau) == truthValueClause(clause, tau');
    {
        assert forall lit :: lit in clause ==> 
            ((0 <= litToVar(lit) < n ||
             start <= litToVar(lit) < end) &&
             tau[litToVar(lit)] == tau'[litToVar(lit)]);
    }
}
    
