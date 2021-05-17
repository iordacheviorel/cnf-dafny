include "utils.dfy"
    
module Formula
{
    import Utils
        
    datatype FormulaT =
        | Var(val : int)
        | Not(f1 : FormulaT)
        | Or(f1 : FormulaT, f2: FormulaT)
        | And(f1 : FormulaT, f2 : FormulaT)
        | Implies(f1 : FormulaT, f2 : FormulaT)
        | DImplies(f1 :FormulaT, f2 : FormulaT)
        
    function method maxVar(f : FormulaT) : int
        requires validFormulaT(f);
        ensures variablesUpTo(f, maxVar(f));
        ensures maxVar(f) >= 0
    {
        match f
        {
            case And(f1,f2) => 
                var temp1 := maxVar(f1);
                var temp2 := maxVar(f2);
                var n' := Utils.max(temp1, temp2);
                variablesUpToMonotone(f1, temp1, n');
                variablesUpToMonotone(f2, temp2, n');
                n'
            case Var(val) =>
                val + 1
            case Or(f1,f2) =>
                var temp1 := maxVar(f1);
                var temp2 := maxVar(f2);
                var n' := Utils.max(temp1, temp2);
                variablesUpToMonotone(f1, temp1, n');
                variablesUpToMonotone(f2, temp2, n');
                n'
            case Not(f1) =>
                var temp1 := maxVar(f1);
                var n' := temp1;
                variablesUpToMonotone(f1, temp1, n');
                n'
            case Implies(f1,f2) =>
                var temp1 := maxVar(f1);
                var temp2 := maxVar(f2);
                var n' := Utils.max(temp1, temp2);
                variablesUpToMonotone(f1, temp1, n');
                variablesUpToMonotone(f2, temp2, n');
                n'
            case DImplies(f1,f2) =>
                var temp1 := maxVar(f1);
                var temp2 := maxVar(f2);
                var n' := Utils.max(temp1, temp2);
                variablesUpToMonotone(f1, temp1, n');
                variablesUpToMonotone(f2, temp2, n');
                n'
        }
    }

    predicate variablesUpTo(f : FormulaT, n : int)
        decreases f;
        ensures variablesUpTo(f, n) == true ==> validFormulaT(f);
    {
        match f
        {
            case And(f1,f2) =>
                variablesUpTo(f1, n) &&
                variablesUpTo(f2, n)
            case Var(val) =>
                0 <= val < n
            case Or(f1,f2) =>
                variablesUpTo(f1, n) && variablesUpTo(f2, n)
            case Not(f1) =>
                variablesUpTo(f1, n)
            case Implies(f1,f2) =>
                variablesUpTo(f1, n) && variablesUpTo(f2, n)
            case DImplies(f1,f2) =>
                variablesUpTo(f1, n) && variablesUpTo(f2, n)
        }
    }

    lemma variablesUpToMaxVar(f : FormulaT, n : int)
        requires variablesUpTo(f, n);
        ensures validFormulaT(f);
        ensures n >= maxVar(f);
    {
    }

    lemma variablesUpToMonotone(f : FormulaT, n : int, n' : int)
        requires variablesUpTo(f, n);
        requires n <= n';
        ensures variablesUpTo(f, n');
    {
    }

    lemma variablesUpToVar(v : int)
        requires v >= 0;
        ensures variablesUpTo(Var(v), v + 1);
    {
        assert v < v + 1;
    }

    predicate validFormulaT(f : FormulaT)
        decreases f;
    {
        match f
        {
            case And(f1,f2) =>
                validFormulaT(f1) && validFormulaT(f2)
            case Var(val) =>
                val >= 0
            case Or(f1,f2) =>
                validFormulaT(f1) && validFormulaT(f2)
            case Not(f1) =>
                validFormulaT(f1)
            case Implies(f1,f2) =>
                validFormulaT(f1) && validFormulaT(f2)
            case DImplies(f1,f2) =>
                validFormulaT(f1) && validFormulaT(f2)
        }
    }
    
    function method truthValue(f : FormulaT, assignment : seq<bool>) : bool
        decreases f;
        requires validFormulaT(f);
        requires variablesUpTo(f, |assignment|);
    {
        match f
        {
            case And(f1,f2) =>
                truthValue(f1, assignment) &&
                truthValue(f2, assignment)
            case Var(val) =>
                assignment[val]
            case Or(f1,f2) =>
                truthValue(f1, assignment) ||
                truthValue(f2, assignment)
            case Not(f1) =>
                !truthValue(f1, assignment)
            case Implies(f1,f2) =>
                !truthValue(f1, assignment) ||
                truthValue(f2, assignment)
            case DImplies(f1,f2) =>
                truthValue(f1, assignment) ==
                truthValue(f2, assignment)
            }
    }

    predicate equivalent(f1 : FormulaT, f2 : FormulaT)
        requires validFormulaT(f1);
        requires validFormulaT(f2);
    {
        forall tau : seq<bool> ::
            variablesUpTo(f1, |tau|) &&
            variablesUpTo(f2, |tau|) ==>
            truthValue(f1, tau) == truthValue(f2, tau)
    }

    lemma assignmentRelevant(f : FormulaT, n : int, tau1 : seq<bool>, tau2 : seq<bool>)
        requires validFormulaT(f);
        requires variablesUpTo(f, n);
        requires |tau1| >= n >= 0;
        requires |tau2| >= n;
        requires tau1[0..n] == tau2[0..n];
        ensures (
            variablesUpToMonotone(f, n, |tau1|);
            variablesUpToMonotone(f, n, |tau2|);
            truthValue(f, tau1) == truthValue(f, tau2)
                );
    {
        match f
        {
            case And(f1, f2) => {
                assignmentRelevant(f1, n, tau1, tau2);
                assignmentRelevant(f2, n, tau1, tau2);
                variablesUpToMonotone(f1, n, |tau1|);
                variablesUpToMonotone(f1, n, |tau2|);
                variablesUpToMonotone(f2, n, |tau1|);
                variablesUpToMonotone(f2, n, |tau2|);
                assert truthValue(f1, tau1) == truthValue(f1, tau2);
                assert truthValue(f2, tau1) == truthValue(f2, tau2);
            }
            case Var(val) => {
            }
            case Or(f1,f2) => {
                assignmentRelevant(f1, n, tau1, tau2);
                assignmentRelevant(f2, n, tau1, tau2);
                variablesUpToMonotone(f1, n, |tau1|);
                variablesUpToMonotone(f1, n, |tau2|);
                variablesUpToMonotone(f2, n, |tau1|);
                variablesUpToMonotone(f2, n, |tau2|);
                assert truthValue(f1, tau1) == truthValue(f1, tau2);
                assert truthValue(f2, tau1) == truthValue(f2, tau2);
            }
            case Not(f1) => {
                assignmentRelevant(f1, n, tau1, tau2);
                variablesUpToMonotone(f1, n, |tau1|);
                variablesUpToMonotone(f1, n, |tau2|);
                assert truthValue(f1, tau1) == truthValue(f1, tau2);
            }
            case Implies(f1,f2) => {
                assignmentRelevant(f1, n, tau1, tau2);
                assignmentRelevant(f2, n, tau1, tau2);
                variablesUpToMonotone(f1, n, |tau1|);
                variablesUpToMonotone(f1, n, |tau2|);
                variablesUpToMonotone(f2, n, |tau1|);
                variablesUpToMonotone(f2, n, |tau2|);
                assert truthValue(f1, tau1) == truthValue(f1, tau2);
                assert truthValue(f2, tau1) == truthValue(f2, tau2);
            }
            case DImplies(f1,f2) => {
                assignmentRelevant(f1, n, tau1, tau2);
                assignmentRelevant(f2, n, tau1, tau2);
                variablesUpToMonotone(f1, n, |tau1|);
                variablesUpToMonotone(f1, n, |tau2|);
                variablesUpToMonotone(f2, n, |tau1|);
                variablesUpToMonotone(f2, n, |tau2|);
                assert truthValue(f1, tau1) == truthValue(f1, tau2);
                assert truthValue(f2, tau1) == truthValue(f2, tau2);
            }
        }
    }

    function seqFalse(n : int) : seq<bool>
        requires n >= 0;
        ensures |seqFalse(n)| == n;
    {
        if n == 0 then
            []
        else
            seqFalse(n - 1) + [false]
    }

    lemma equivalentTrans(f1 : FormulaT, f2 : FormulaT, f3 : FormulaT)
        requires validFormulaT(f1);
        requires validFormulaT(f2);
        requires validFormulaT(f3);
        requires equivalent(f1, f2);
        requires equivalent(f2, f3);
        ensures equivalent(f1, f3);
    {
        forall tau | variablesUpTo(f1, |tau|) && variablesUpTo(f3, |tau|)
            ensures truthValue(f1, tau) == truthValue(f3, tau);
        {
            ghost var temp := seqFalse(maxVar(f2));
            variablesUpToMonotone(f2, |temp|, |tau + temp|);
            
            assignmentRelevant(f1, |tau|, tau, tau + temp);
            variablesUpToMonotone(f1, |tau|, |tau + temp|);
            
            assignmentRelevant(f3, |tau|, tau, tau + temp);
            variablesUpToMonotone(f3, |tau|, |tau + temp|);
            
            assert truthValue(f1, tau) == truthValue(f3, tau);
        }
    }

    method prettyPrint(f : FormulaT) returns (res : seq<char>)
        decreases f;
    {
        if(f.And?)
        {
            var f1 := prettyPrint(f.f1);
            var f2 := prettyPrint(f.f2);
            res := "(" + f1 + " and " + f2 + ")";
        }
        if(f.Or?)
        {
            var f1 := prettyPrint(f.f1);
            var f2 := prettyPrint(f.f2);
            res := "(" + f1 + " or " + f2 + ")";
        }
        if(f.Implies?)
        {
            var f1 := prettyPrint(f.f1);
            var f2 := prettyPrint(f.f2);
            res := "(" + f1 + " -> " + f2 + ")";
        }
        if(f.DImplies?)
        {
            var f1 := prettyPrint(f.f1);
            var f2 := prettyPrint(f.f2);
            res := "(" + f1 + " <-> " + f2 + ")";
        }
        if(f.Var?)
        {
            var val := Utils.integerToCharSequence(f.val);
            res := val;
        }
        if(f.Not?)
        {
            var f1 := prettyPrint(f.f1);
            res := "~(" + f1 + ")";
        }
    }
}

