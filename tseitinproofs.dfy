include "formula.dfy"
include "cnfformula.dfy"
include "utils.dfy"
include "tseitincore.dfy"

module TseitinProofs
{
    import opened Formula
    import opened Utils
    import opened CnfFormula
    import opened TseitinCore

    lemma proveSameValueAnd(f1 : FormulaT, rf1 : seq<seq<int>>, v1 : int,
        f2 : FormulaT, rf2 : seq<seq<int>>, v2 : int,
        n : int, start : int, mid : int, v : int,
        end : int, rf : seq<seq<int>>)
        requires 0 <= n <= start <= mid <= v;
        requires valid(f1, rf1, v1, n, start, mid);
        requires tseitinSameValue(f1, rf1, v1, n, start, mid);
        requires valid(f2, rf2, v2, n, mid, v);
        requires tseitinSameValue(f2, rf2, v2, n, mid, v);
        requires rf == rf1 + rf2 + andClauses(v1, v2, v);
        requires end == v + 1;
        ensures valid(And(f1, f2), rf, v, n, start, end);
        ensures tseitinSameValue(And(f1, f2), rf, v, n, start, end);
    {
        assert valid(And(f1, f2), rf, v, n, start, end);
        forall tau : seq<bool> | |tau| >= end && truthValueCnfFormula(rf, tau)
            ensures truthValueLiteral(posVarToLit(v), tau) ==
               truthValue(And(f1, f2), tau)
        {
            variablesUpToMonotone(f1, n, |tau|);
            variablesUpToMonotone(f2, n, |tau|);
            assert truthValueLiteral(posVarToLit(v1), tau) ==
                truthValue(f1, tau);
            assert truthValueLiteral(posVarToLit(v2), tau) ==
                truthValue(f2, tau);
                lemmaAndClauses(v1, v2, v, tau);
                
            assert truthValueLiteral(posVarToLit(v), tau) ==
                truthValue(And(f1, f2), tau);
        }
    }

    lemma proveSameValueOr(f1 : FormulaT, rf1 : seq<seq<int>>, v1 : int,
        f2 : FormulaT, rf2 : seq<seq<int>>, v2 : int,
        n : int, start : int, mid : int, v : int,
        end : int, rf : seq<seq<int>>)
        requires 0 <= n <= start <= mid <= v;
        requires valid(f1, rf1, v1, n, start, mid);
        requires tseitinSameValue(f1, rf1, v1, n, start, mid);
        requires valid(f2, rf2, v2, n, mid, v);
        requires tseitinSameValue(f2, rf2, v2, n, mid, v);
        requires rf == rf1 + rf2 + orClauses(v1, v2, v);
        requires end == v + 1;
        ensures valid(Or(f1, f2), rf, v, n, start, end);
        ensures tseitinSameValue(Or(f1, f2), rf, v, n, start, end);
    {
        assert valid(Or(f1, f2), rf, v, n, start, end);
        forall tau : seq<bool> | |tau| >= end && truthValueCnfFormula(rf, tau)
            ensures truthValueLiteral(posVarToLit(v), tau) ==
               truthValue(Or(f1, f2), tau)
        {
            variablesUpToMonotone(f1, n, |tau|);
            variablesUpToMonotone(f2, n, |tau|);
            assert truthValueLiteral(posVarToLit(v1), tau) ==
                truthValue(f1, tau);
            assert truthValueLiteral(posVarToLit(v2), tau) ==
                truthValue(f2, tau);
            lemmaOrClauses(v1, v2, v, tau);
                
            assert truthValueLiteral(posVarToLit(v), tau) ==
                truthValue(Or(f1, f2), tau);
        }
    }

    lemma proveSameValueImplies(f1 : FormulaT, rf1 : seq<seq<int>>, v1 : int,
        f2 : FormulaT, rf2 : seq<seq<int>>, v2 : int,
        n : int, start : int, mid : int, v : int,
        end : int, rf : seq<seq<int>>)
        requires 0 <= n <= start <= mid <= v;
        requires valid(f1, rf1, v1, n, start, mid);
        requires tseitinSameValue(f1, rf1, v1, n, start, mid);
        requires valid(f2, rf2, v2, n, mid, v);
        requires tseitinSameValue(f2, rf2, v2, n, mid, v);
        requires rf == rf1 + rf2 + impliesClauses(v1, v2, v);
        requires end == v + 1;
        ensures valid(Implies(f1, f2), rf, v, n, start, end);
        ensures tseitinSameValue(Implies(f1, f2), rf, v, n, start, end);
    {
        assert valid(Implies(f1, f2), rf, v, n, start, end);
        forall tau : seq<bool> | |tau| >= end && truthValueCnfFormula(rf, tau)
            ensures truthValueLiteral(posVarToLit(v), tau) ==
               truthValue(Implies(f1, f2), tau)
        {
            variablesUpToMonotone(f1, n, |tau|);
            variablesUpToMonotone(f2, n, |tau|);
            assert truthValueLiteral(posVarToLit(v1), tau) ==
                truthValue(f1, tau);
            assert truthValueLiteral(posVarToLit(v2), tau) ==
                truthValue(f2, tau);
            lemmaImpliesClauses(v1, v2, v, tau);
                
            assert truthValueLiteral(posVarToLit(v), tau) ==
                truthValue(Implies(f1, f2), tau);
        }
    }

    lemma proveSameValueDimplies(f1 : FormulaT, rf1 : seq<seq<int>>, v1 : int,
        f2 : FormulaT, rf2 : seq<seq<int>>, v2 : int,
        n : int, start : int, mid : int, v : int,
        end : int, rf : seq<seq<int>>)
        requires 0 <= n <= start <= mid <= v;
        requires valid(f1, rf1, v1, n, start, mid);
        requires tseitinSameValue(f1, rf1, v1, n, start, mid);
        requires valid(f2, rf2, v2, n, mid, v);
        requires tseitinSameValue(f2, rf2, v2, n, mid, v);
        requires rf == rf1 + rf2 + dimpliesClauses(v1, v2, v);
        requires end == v + 1;
        ensures valid(DImplies(f1, f2), rf, v, n, start, end);
        ensures tseitinSameValue(DImplies(f1, f2), rf, v, n, start, end);
    {
        assert valid(DImplies(f1, f2), rf, v, n, start, end);
        forall tau : seq<bool> | |tau| >= end && truthValueCnfFormula(rf, tau)
            ensures truthValueLiteral(posVarToLit(v), tau) ==
               truthValue(DImplies(f1, f2), tau)
        {
            variablesUpToMonotone(f1, n, |tau|);
            variablesUpToMonotone(f2, n, |tau|);
            assert truthValueLiteral(posVarToLit(v1), tau) ==
                truthValue(f1, tau);
            assert truthValueLiteral(posVarToLit(v2), tau) ==
                truthValue(f2, tau);
            lemmaDimpliesClauses(v1, v2, v, tau);
                
            assert truthValueLiteral(posVarToLit(v), tau) ==
                truthValue(DImplies(f1, f2), tau);
        }
    }

    lemma proveSameValueNot(f1 : FormulaT, rf1 : seq<seq<int>>, v1 : int,
        n : int, start : int, v : int,
        end : int, rf : seq<seq<int>>)
        requires 0 <= n <= start <= v;
        requires valid(f1, rf1, v1, n, start, v);
        requires tseitinSameValue(f1, rf1, v1, n, start, v);
        requires rf == rf1 + notClauses(v1, v);
        requires end == v + 1;
        ensures valid(Not(f1), rf, v, n, start, end);
        ensures tseitinSameValue(Not(f1), rf, v, n, start, end);
    {
        assert valid(Not(f1), rf, v, n, start, end);
        forall tau : seq<bool> | |tau| >= end && truthValueCnfFormula(rf, tau)
            ensures truthValueLiteral(posVarToLit(v), tau) ==
               truthValue(Not(f1), tau)
        {
            variablesUpToMonotone(f1, n, |tau|);
            assert truthValueLiteral(posVarToLit(v1), tau) ==
                truthValue(f1, tau);
            lemmaNotClauses(v1, v, tau);
                
            assert truthValueLiteral(posVarToLit(v), tau) ==
                truthValue(Not(f1), tau);
        }
    }

    lemma proveCanExtendAnd(f1 : FormulaT, rf1 : seq<seq<int>>, v1 : int,
        f2 : FormulaT, rf2 : seq<seq<int>>, v2 : int,
        n : int, start : int, mid : int, v : int,
        end : int, rf : seq<seq<int>>)
        requires 0 <= n <= start <= mid <= v;
        requires valid(f1, rf1, v1, n, start, mid);
        requires tseitinCanExtend(f1, rf1, v1, n, start, mid);
        requires valid(f2, rf2, v2, n, mid, v);
        requires tseitinCanExtend(f2, rf2, v2, n, mid, v);
        requires rf == rf1 + rf2 + andClauses(v1, v2, v);
        requires end == v + 1;
        ensures valid(And(f1, f2), rf, v, n, start, end);
        ensures tseitinCanExtend(And(f1, f2), rf, v, n, start, end);
    {
        assert valid(And(f1, f2), rf, v, n, start, end);
        forall tau : seq<bool> | |tau| == n
            ensures canExtend(tau, And(f1, f2), rf, v, n, start, end);
        {
            ghost var tau1 :| tau <= tau1 && |tau1| == mid &&
                truthValueCnfFormula(rf1, tau1) &&
                truthValue(f1, tau) == truthValueLiteral(posVarToLit(v1), tau1);
            ghost var tau2 :| tau <= tau2 && |tau2| == v &&
                truthValueCnfFormula(rf2, tau2) &&
                truthValue(f2, tau) == truthValueLiteral(posVarToLit(v2), tau2);
            ghost var tau' := combine(tau, tau1, tau2, n, start, mid, v,
                truthValue(And(f1, f2), tau));
                
            assert agree(tau', tau, 0, n);
            assert agree(tau', tau1, start, mid);
            assert agree(tau', tau2, mid, v);
            assert tau'[v] == truthValue(And(f1, f2), tau);
            
            assert truthValueLiteral(posVarToLit(v), tau') ==
                truthValue(And(f1, f2), tau);
                
            assert truthValueLiteral(negVarToLit(v), tau') ==
                !truthValue(And(f1, f2), tau);
                    
            transferTruthValue(rf1, tau1, tau', n, start, mid);
            transferTruthValue(rf2, tau2, tau', n, mid, v);

            transferTruthValueLit(posVarToLit(v1), tau1, tau', n, start, mid);
            transferTruthValueLit(negVarToLit(v1), tau1, tau', n, start, mid);
            assert truthValueLiteral(posVarToLit(v1), tau') ==
                truthValue(f1, tau);
            assert truthValueLiteral(negVarToLit(v1), tau') ==
                !truthValue(f1, tau);
            
            transferTruthValueLit(posVarToLit(v2), tau2, tau', n, mid, v);
            transferTruthValueLit(negVarToLit(v2), tau2, tau', n, mid, v);
            assert truthValueLiteral(posVarToLit(v2), tau') ==
                truthValue(f2, tau);
            assert truthValueLiteral(negVarToLit(v2), tau') ==
                !truthValue(f2, tau);

            lemmaAndClauses(v1, v2, v, tau');
                
            //Increases verif time by 30 seconds
            //assert truthValueCnfFormula(andClauses(v1, v2, v), tau');

            assert canExtend(tau, And(f1, f2), rf, v, n, start, end);
        }
    }

    lemma proveCanExtendOr(f1 : FormulaT, rf1 : seq<seq<int>>, v1 : int,
        f2 : FormulaT, rf2 : seq<seq<int>>, v2 : int,
        n : int, start : int, mid : int, v : int,
        end : int, rf : seq<seq<int>>)
        requires 0 <= n <= start <= mid <= v;
        requires valid(f1, rf1, v1, n, start, mid);
        requires tseitinCanExtend(f1, rf1, v1, n, start, mid);
        requires valid(f2, rf2, v2, n, mid, v);
        requires tseitinCanExtend(f2, rf2, v2, n, mid, v);
        requires rf == rf1 + rf2 + orClauses(v1, v2, v);
        requires end == v + 1;
        ensures valid(Or(f1, f2), rf, v, n, start, end);
        ensures tseitinCanExtend(Or(f1, f2), rf, v, n, start, end);
    {
        assert valid(Or(f1, f2), rf, v, n, start, end);
        forall tau : seq<bool> | |tau| == n
            ensures canExtend(tau, Or(f1, f2), rf, v, n, start, end);
        {
            ghost var tau1 :| tau <= tau1 && |tau1| == mid &&
                truthValueCnfFormula(rf1, tau1) &&
                truthValue(f1, tau) == truthValueLiteral(posVarToLit(v1), tau1);
            ghost var tau2 :| tau <= tau2 && |tau2| == v &&
                truthValueCnfFormula(rf2, tau2) &&
                truthValue(f2, tau) == truthValueLiteral(posVarToLit(v2), tau2);
            ghost var tau' := combine(tau, tau1, tau2, n, start, mid, v,
                truthValue(Or(f1, f2), tau));
                
            assert agree(tau', tau, 0, n);
            assert agree(tau', tau1, start, mid);
            assert agree(tau', tau2, mid, v);
            assert tau'[v] == truthValue(Or(f1, f2), tau);
            
            assert truthValueLiteral(posVarToLit(v), tau') ==
                truthValue(Or(f1, f2), tau);
                
            assert truthValueLiteral(negVarToLit(v), tau') ==
                !truthValue(Or(f1, f2), tau);
                    
            transferTruthValue(rf1, tau1, tau', n, start, mid);
            transferTruthValue(rf2, tau2, tau', n, mid, v);

            transferTruthValueLit(posVarToLit(v1), tau1, tau', n, start, mid);
            transferTruthValueLit(negVarToLit(v1), tau1, tau', n, start, mid);
            assert truthValueLiteral(posVarToLit(v1), tau') ==
                truthValue(f1, tau);
            assert truthValueLiteral(negVarToLit(v1), tau') ==
                !truthValue(f1, tau);
            
            transferTruthValueLit(posVarToLit(v2), tau2, tau', n, mid, v);
            transferTruthValueLit(negVarToLit(v2), tau2, tau', n, mid, v);
            assert truthValueLiteral(posVarToLit(v2), tau') ==
                truthValue(f2, tau);
            assert truthValueLiteral(negVarToLit(v2), tau') ==
                !truthValue(f2, tau);

            assert truthValue(Or(f1, f2), tau) == truthValue(f1, tau) ||
                truthValue(f2, tau);

            lemmaOrClauses(v1, v2, v, tau');

            assert canExtend(tau, Or(f1, f2), rf, v, n, start, end);
        }
    }

    lemma proveCanExtendImplies(f1 : FormulaT, rf1 : seq<seq<int>>, v1 : int,
        f2 : FormulaT, rf2 : seq<seq<int>>, v2 : int,
        n : int, start : int, mid : int, v : int,
        end : int, rf : seq<seq<int>>)
        requires 0 <= n <= start <= mid <= v;
        requires valid(f1, rf1, v1, n, start, mid);
        requires tseitinCanExtend(f1, rf1, v1, n, start, mid);
        requires valid(f2, rf2, v2, n, mid, v);
        requires tseitinCanExtend(f2, rf2, v2, n, mid, v);
        requires rf == rf1 + rf2 + impliesClauses(v1, v2, v);
        requires end == v + 1;
        ensures valid(Implies(f1, f2), rf, v, n, start, end);
        ensures tseitinCanExtend(Implies(f1, f2), rf, v, n, start, end);
    {
        assert valid(Implies(f1, f2), rf, v, n, start, end);
        forall tau : seq<bool> | |tau| == n
            ensures canExtend(tau, Implies(f1, f2), rf, v, n, start, end);
        {
            ghost var tau1 :| tau <= tau1 && |tau1| == mid &&
                truthValueCnfFormula(rf1, tau1) &&
                truthValue(f1, tau) == truthValueLiteral(posVarToLit(v1), tau1);
            ghost var tau2 :| tau <= tau2 && |tau2| == v &&
                truthValueCnfFormula(rf2, tau2) &&
                truthValue(f2, tau) == truthValueLiteral(posVarToLit(v2), tau2);
            ghost var tau' := combine(tau, tau1, tau2, n, start, mid, v,
                truthValue(Implies(f1, f2), tau));
                
            assert agree(tau', tau, 0, n);
            assert agree(tau', tau1, start, mid);
            assert agree(tau', tau2, mid, v);
            assert tau'[v] == truthValue(Implies(f1, f2), tau);
            
            assert truthValueLiteral(posVarToLit(v), tau') ==
                truthValue(Implies(f1, f2), tau);
                
            assert truthValueLiteral(negVarToLit(v), tau') ==
                !truthValue(Implies(f1, f2), tau);
                    
            transferTruthValue(rf1, tau1, tau', n, start, mid);
            transferTruthValue(rf2, tau2, tau', n, mid, v);

            transferTruthValueLit(posVarToLit(v1), tau1, tau', n, start, mid);
            transferTruthValueLit(negVarToLit(v1), tau1, tau', n, start, mid);
            assert truthValueLiteral(posVarToLit(v1), tau') ==
                truthValue(f1, tau);
            assert truthValueLiteral(negVarToLit(v1), tau') ==
                !truthValue(f1, tau);
            
            transferTruthValueLit(posVarToLit(v2), tau2, tau', n, mid, v);
            transferTruthValueLit(negVarToLit(v2), tau2, tau', n, mid, v);
            assert truthValueLiteral(posVarToLit(v2), tau') ==
                truthValue(f2, tau);
            assert truthValueLiteral(negVarToLit(v2), tau') ==
                !truthValue(f2, tau);

            assert truthValue(Implies(f1, f2), tau) == (truthValue(f1, tau)
                    ==>
                truthValue(f2, tau));

            lemmaImpliesClauses(v1, v2, v, tau');
            
            assert canExtend(tau, Implies(f1, f2), rf, v, n, start, end);
        }
    }

    lemma proveCanExtendDimplies(f1 : FormulaT, rf1 : seq<seq<int>>, v1 : int,
        f2 : FormulaT, rf2 : seq<seq<int>>, v2 : int,
        n : int, start : int, mid : int, v : int,
        end : int, rf : seq<seq<int>>)
        requires 0 <= n <= start <= mid <= v;
        requires valid(f1, rf1, v1, n, start, mid);
        requires tseitinCanExtend(f1, rf1, v1, n, start, mid);
        requires valid(f2, rf2, v2, n, mid, v);
        requires tseitinCanExtend(f2, rf2, v2, n, mid, v);
        requires rf == rf1 + rf2 + dimpliesClauses(v1, v2, v);
        requires end == v + 1;
        ensures valid(DImplies(f1, f2), rf, v, n, start, end);
        ensures tseitinCanExtend(DImplies(f1, f2), rf, v, n, start, end);
    {
        assert valid(DImplies(f1, f2), rf, v, n, start, end);
        forall tau : seq<bool> | |tau| == n
            ensures canExtend(tau, DImplies(f1, f2), rf, v, n, start, end);
        {
            ghost var tau1 :| tau <= tau1 && |tau1| == mid &&
                truthValueCnfFormula(rf1, tau1) &&
                truthValue(f1, tau) == truthValueLiteral(posVarToLit(v1), tau1);
            ghost var tau2 :| tau <= tau2 && |tau2| == v &&
                truthValueCnfFormula(rf2, tau2) &&
                truthValue(f2, tau) == truthValueLiteral(posVarToLit(v2), tau2);
            ghost var tau' := combine(tau, tau1, tau2, n, start, mid, v,
                truthValue(DImplies(f1, f2), tau));
                
            assert agree(tau', tau, 0, n);
            assert agree(tau', tau1, start, mid);
            assert agree(tau', tau2, mid, v);
            assert tau'[v] == truthValue(DImplies(f1, f2), tau);
            
            assert truthValueLiteral(posVarToLit(v), tau') ==
                truthValue(DImplies(f1, f2), tau);
                
            assert truthValueLiteral(negVarToLit(v), tau') ==
                !truthValue(DImplies(f1, f2), tau);
                    
            transferTruthValue(rf1, tau1, tau', n, start, mid);
            transferTruthValue(rf2, tau2, tau', n, mid, v);

            transferTruthValueLit(posVarToLit(v1), tau1, tau', n, start, mid);
            transferTruthValueLit(negVarToLit(v1), tau1, tau', n, start, mid);
            assert truthValueLiteral(posVarToLit(v1), tau') ==
                truthValue(f1, tau);
            assert truthValueLiteral(negVarToLit(v1), tau') ==
                !truthValue(f1, tau);
            
            transferTruthValueLit(posVarToLit(v2), tau2, tau', n, mid, v);
            transferTruthValueLit(negVarToLit(v2), tau2, tau', n, mid, v);
            assert truthValueLiteral(posVarToLit(v2), tau') ==
                truthValue(f2, tau);
            assert truthValueLiteral(negVarToLit(v2), tau') ==
                !truthValue(f2, tau);

            assert truthValue(DImplies(f1, f2), tau) == (truthValue(f1, tau)
                <==>
                truthValue(f2, tau));

            lemmaDimpliesClauses(v1, v2, v, tau');
           
            assert canExtend(tau, DImplies(f1, f2), rf, v, n, start, end);
        }
    }

    lemma proveCanExtendNot(f1 : FormulaT, rf1 : seq<seq<int>>, v1 : int,
        n : int, start : int, v : int,
        end : int, rf : seq<seq<int>>)
        requires 0 <= n <= start <= v < end;
        requires valid(f1, rf1, v1, n, start, v);
        requires tseitinCanExtend(f1, rf1, v1, n, start, v);
        requires rf == rf1 + notClauses(v1, v);
        requires end == v + 1;
        ensures valid(Not(f1), rf, v, n, start, end);
        ensures tseitinCanExtend(Not(f1), rf, v, n, start, end);
    {
        assert 0 <= n <= v;
        assert valid(Not(f1), rf, v, n, start, end);
        forall tau : seq<bool> | |tau| == n
            ensures canExtend(tau, Not(f1), rf, v, n, start, end);
        {
            assert canExtend(tau, f1, rf1, v1, n, start, v);
            assert validLiteral(posVarToLit(v1));

            ghost var tau1 :|
                tau <= tau1 &&
                |tau1| == v &&
                truthValueCnfFormula(rf1, tau1) &&
                truthValue(f1, tau) ==
                truthValueLiteral(posVarToLit(v1), tau1);

            negateLiteral(v1, tau1);

            ghost var tau' := combine1(tau, tau1, n, start, v,
                truthValue(Not(f1), tau));

            assert tau <= tau';
            assert |tau'| == end;
            transferTruthValue(rf1, tau1, tau', n, start, v);

            transferTruthValueLit(posVarToLit(v1), tau1, tau', n, start, v);
            assert truthValueLiteral(posVarToLit(v1), tau') ==
                truthValue(f1, tau);
            transferTruthValueLit(negVarToLit(v1), tau1, tau', n, start, v);
            assert truthValueLiteral(negVarToLit(v1), tau1) ==
                !truthValueLiteral(posVarToLit(v1), tau1);

            lemmaNotClauses(v1, v, tau');

            assert truthValueCnfFormula(rf, tau');
        }
    }
}
