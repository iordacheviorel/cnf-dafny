include "formula.dfy"
include "cnfformula.dfy"
include "utils.dfy"
include "tseitincore.dfy"
include "tseitinproofs.dfy"

module Tseitin
{
    import opened Formula
    import opened Utils
    import opened CnfFormula
    import opened TseitinCore
    import opened TseitinProofs

    predicate satisfiable(f : FormulaT)
        requires validFormulaT(f);
    {
        exists tau | |tau| == maxVar(f) :: truthValue(f, tau)
    }

    predicate satisfiableCnfFormula(rf : seq<seq<int>>)
        requires validCnfFormula(rf);
    {
        exists tau | |tau| == maxVarCnfFormula(rf) :: truthValueCnfFormula(rf, tau)
    }

    predicate equiSatisfiable(f : FormulaT, rf : seq<seq<int>>)
        requires validFormulaT(f);
        requires validCnfFormula(rf);
    {
        satisfiable(f) <==> satisfiableCnfFormula(rf)
    }

    lemma satisfiedFormula(f : FormulaT, tau : seq<bool>)
        requires validFormulaT(f);
        requires variablesUpTo(f, |tau|);
        requires truthValue(f, tau);
        ensures satisfiable(f);
    {
        ghost var n := maxVar(f);
        assert variablesUpTo(f, n);
        variablesUpToMaxVar(f, |tau|);
        assert |tau| >= n;
        ghost var tau' := tau[0..n];
        assignmentRelevant(f, n, tau, tau');
    }
    
    lemma satisfiedCnfFormula(rf : seq<seq<int>>, tau : seq<bool>)
        requires validCnfFormula(rf);
        requires variablesUpToCnfFormula(rf, |tau|);
        requires truthValueCnfFormula(rf, tau);
        ensures satisfiableCnfFormula(rf);
    {
        ghost var n := maxVarCnfFormula(rf);
        assert variablesUpToCnfFormula(rf, n);
        variablesUpToMaxVarCnfFormula(rf, |tau|);
        assert |tau| >= n;
        ghost var tau' := tau[0..n];
        assignmentRelevantCnfFormula(rf, tau, tau', n);
    }

    lemma tseitinFollows(f : FormulaT, rf : seq<seq<int>>, v : int,
        n : int, end : int)
        requires valid(f, rf, v, n, n, end);
        requires tseitinSameValue(f, rf, v, n, n, end);
        requires tseitinCanExtend(f, rf, v, n, n, end);
        ensures equiSatisfiable(f, rf + [[posVarToLit(v)]]);
    {
        if (satisfiable(f)) {
            ghost var tauShort :| |tauShort| == maxVar(f) &&
                truthValue(f, tauShort);
            variablesUpToMaxVar(f, n);
            assert maxVar(f) <= n;
            ghost var tau := tauShort + nFalses(n - maxVar(f));
            assignmentRelevant(f, maxVar(f), tauShort, tau);
            assert truthValue(f, tau);
            assert canExtend(tau, f, rf, v, n, n, end);
            ghost var tau' :| tau <= tau' && |tau'| == end &&
                truthValueCnfFormula(rf, tau') &&
                truthValue(f, tau) == truthValueLiteral(posVarToLit(v), tau');
            assert truthValueLiteral(posVarToLit(v), tau');
            assert truthValueCnfFormula(rf, tau');
            satisfiedCnfFormula(rf + [[posVarToLit(v)]], tau');
        }
        if (satisfiableCnfFormula(rf + [[posVarToLit(v)]])) {
            ghost var tauShort :|
                |tauShort| == maxVarCnfFormula(rf + [[posVarToLit(v)]]) &&
                truthValueCnfFormula(rf + [[posVarToLit(v)]], tauShort);

            variablesUpToMaxVarCnfFormula(rf + [[posVarToLit(v)]], end);
            assert end >= |tauShort|;

            ghost var tau := tauShort + nFalses(end - |tauShort|);
            assignmentRelevantCnfFormula(rf + [[posVarToLit(v)]],
                tauShort, tau, |tauShort|);
                
            assert truthValueCnfFormula(rf, tau);
            assert truthValueCnfFormula([[posVarToLit(v)]], tau);
            assert truthValueClause([posVarToLit(v)], tau);
            assert variablesUpToClause([posVarToLit(v)], |tau|);
            assert variablesUpToLiteral(posVarToLit(v), |tau|);
            assert truthValueLiteral(posVarToLit(v), tau);
            variablesUpToMonotone(f, n, end);
            variablesUpToMaxVar(f, end);
            assert truthValueLiteral(posVarToLit(v), tau) ==
                truthValue(f, tau);
            assert truthValue(f, tau);
            satisfiedFormula(f, tau);
        }
    }

    method tseitin(f : FormulaT) returns (result : seq<seq<int>>)
        requires validFormulaT(f);
        ensures validCnfFormula(result);
        ensures equiSatisfiable(f, result);
    {
        var n := maxVar(f);
        var v : int;
        var end : int;
        var rf : seq<seq<int>>;
        rf, v, end := tseitinCnf(f, n, n);
        result := rf + [[posVarToLit(v)]];
        tseitinFollows(f, rf, v, n, end);
    }

    method tseitinCnf(f : FormulaT, n : int, start : int)
        returns (rf : seq<seq<int>>, v : int, end : int)
        requires variablesUpTo(f, n);
        requires start >= n >= 0;
        ensures valid(f, rf, v, n, start, end);
        ensures tseitinSameValue(f, rf, v, n, start, end);
        ensures tseitinCanExtend(f, rf, v, n, start, end);
    {
        match f
        {
            case Or(f1, f2) => {
                var rf1 : seq<seq<int>>;
                var rf2 : seq<seq<int>>;
                var v1 : int;
                var v2 : int;
                var mid : int;
                rf1, v1, mid := tseitinCnf(f1, n, start);
                rf2, v2, v := tseitinCnf(f2, n, mid);
                end := v + 1;
                rf := rf1 + rf2 + orClauses(v1, v2, v);
                proveCanExtendOr(f1, rf1, v1, f2, rf2, v2, n, start, mid, v, end, rf);
                proveSameValueOr(f1, rf1, v1, f2, rf2, v2, n, start, mid, v, end, rf);
            }
            case And(f1, f2) => {
                var rf1 : seq<seq<int>>;
                var rf2 : seq<seq<int>>;
                var v1 : int;
                var v2 : int;
                var mid : int;
                rf1, v1, mid := tseitinCnf(f1, n, start);
                rf2, v2, v := tseitinCnf(f2, n, mid);
                end := v + 1;
                rf := rf1 + rf2 + andClauses(v1, v2, v);
                proveCanExtendAnd(f1, rf1, v1, f2, rf2, v2, n, start, mid, v, end, rf);
                proveSameValueAnd(f1, rf1, v1, f2, rf2, v2, n, start, mid, v, end, rf);
            }
            case Implies(f1, f2) => {
                var rf1 : seq<seq<int>>;
                var rf2 : seq<seq<int>>;
                var v1 : int;
                var v2 : int;
                var mid : int;
                rf1, v1, mid := tseitinCnf(f1, n, start);
                rf2, v2, v := tseitinCnf(f2, n, mid);
                end := v + 1;
                rf := rf1 + rf2 + impliesClauses(v1, v2, v);
                proveCanExtendImplies(f1, rf1, v1, f2, rf2, v2, n, start, mid, v, end, rf);
                proveSameValueImplies(f1, rf1, v1, f2, rf2, v2, n, start, mid, v, end, rf);
            }
            case DImplies(f1, f2) => {
                var rf1 : seq<seq<int>>;
                var rf2 : seq<seq<int>>;
                var v1 : int;
                var v2 : int;
                var mid : int;
                rf1, v1, mid := tseitinCnf(f1, n, start);
                rf2, v2, v := tseitinCnf(f2, n, mid);
                end := v + 1;
                rf := rf1 + rf2 + dimpliesClauses(v1, v2, v);
                proveCanExtendDimplies(f1, rf1, v1, f2, rf2, v2, n, start, mid, v, end, rf);
                proveSameValueDimplies(f1, rf1, v1, f2, rf2, v2, n, start, mid, v, end, rf);
            }
            case Not(f1) => {
                var rf1 : seq<seq<int>>;
                var v1 : int;
                rf1, v1, v := tseitinCnf(f1, n, start);
                end := v + 1;
                rf := rf1 + notClauses(v1, v);
                proveCanExtendNot(f1, rf1, v1, n, start, v, end, rf);
                proveSameValueNot(f1, rf1, v1, n, start, v, end, rf);
            }
            case Var(val) => {
                rf := [];
                v := val;
                end := start;
                forall tau : seq<bool> | |tau| == n
                    ensures canExtend(tau, f, rf, v, n, start, end)
                {
                    ghost var tau' := tau + nFalses(end - n);
                    assert |tau'| == end;
                    assert canExtend(tau, f, rf, v, n, start, end);
                }

                assert tseitinCanExtend(f, rf, v, n, start, end);
                assert tseitinSameValue(f, rf, v, n, start, end);
            }
        }
    }
}
