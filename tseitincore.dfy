include "formula.dfy"
include "cnfformula.dfy"
include "utils.dfy"

module TseitinCore
{
    import opened Formula
    import opened Utils
    import opened CnfFormula

    function extend(tau : seq<bool>, tau' : seq<bool>,
        n : int, start : int, end : int) : seq<bool>
        requires end >= start >= n >= 0;
        requires |tau| == n;
        requires |tau'| == end - start;
        ensures |extend(tau, tau', n, start, end)| == end;
        ensures agree(extend(tau, tau', n, start, end), tau, 0, n);
        ensures extend(tau, tau', n, start, end)[start..end] == tau';
    {
        var upToStart := tau + nFalses(start - n);
        var result := upToStart + tau';
        result
    }

    predicate valid(f : FormulaT, rf : seq<seq<int>>, v : int,
        n : int, start : int, end : int)
    {
        0 <= n <= start <= end &&
        variablesUpTo(f, n) &&
        validCnfFormula(rf) &&
        validVariable(v) && 
        variableInInterval(v, n, start, end) &&
        variablesInInterval(rf, n, start, end)
    }
    
    predicate canExtend(tau : seq<bool>, f : FormulaT, rf : seq<seq<int>>,
        v : int, n : int, start : int, end : int)
        requires |tau| == n;
        requires valid(f, rf, v, n, start, end);
    {
        exists tau' : seq<bool> | tau <= tau' && |tau'| == end ::
            truthValueCnfFormula(rf, tau') &&
            truthValue(f, tau) == truthValueLiteral(posVarToLit(v), tau')
    }

    predicate tseitinCanExtend(f : FormulaT, rf : seq<seq<int>>, v : int,
        n : int, start : int, end : int)
        requires valid(f, rf, v, n, start, end);
    {
        forall tau : seq<bool> | |tau| == n ::
            canExtend(tau, f, rf, v, n, start, end)
    }

    function method andClauses(v1 : int, v2 : int, v : int) : seq<seq<int>>
        requires validVariable(v1);
        requires validVariable(v2);
        requires validVariable(v);
    {
        [[negVarToLit(v), posVarToLit(v1)],
            [negVarToLit(v), posVarToLit(v2)],
            [negVarToLit(v1), negVarToLit(v2), posVarToLit(v)]]
    }

    function method orClauses(v1 : int, v2 : int, v : int) : seq<seq<int>>
        requires validVariable(v1);
        requires validVariable(v2);
        requires validVariable(v);
    {
        [[negVarToLit(v), posVarToLit(v1), posVarToLit(v2)],
            [negVarToLit(v1), posVarToLit(v)],
            [negVarToLit(v2), posVarToLit(v)]]
    }

    function method impliesClauses(v1 : int, v2 : int, v : int) : seq<seq<int>>
        requires validVariable(v1);
        requires validVariable(v2);
        requires validVariable(v);
    {
        [[negVarToLit(v), negVarToLit(v1), posVarToLit(v2)],
            [posVarToLit(v1), posVarToLit(v)],
            [negVarToLit(v2), posVarToLit(v)]]
    }

    function method dimpliesClauses(v1 : int, v2 : int, v : int) : seq<seq<int>>
        requires validVariable(v1);
        requires validVariable(v2);
        requires validVariable(v);
    {
        [
            [negVarToLit(v), negVarToLit(v1), posVarToLit(v2)],
            [negVarToLit(v1), negVarToLit(v2), posVarToLit(v)],
            [posVarToLit(v1), posVarToLit(v2), posVarToLit(v)],
            [negVarToLit(v), negVarToLit(v2), posVarToLit(v1)]
            ]
    }

    function method notClauses(v1 : int, v : int) : seq<seq<int>>
        requires validVariable(v1);
        requires validVariable(v);
    {
        [[negVarToLit(v), negVarToLit(v1)],
            [posVarToLit(v1), posVarToLit(v)]]
    }
    
    function combine(tau : seq<bool>, tau1 : seq<bool>, tau2 : seq<bool>, n : int,
        start : int, mid : int, end : int, last : bool) : seq<bool>
        requires 0 <= n <= start <= mid <= end;
        requires |tau| == n;
        requires |tau1| == mid;
        requires |tau2| == end;
        ensures (
            ghost var result := combine(tau, tau1, tau2, n, start, mid, end, last);
            |result| == end + 1 &&
                agree(result, tau, 0, n) &&
                agree(result, tau1, start, mid) &&
                agree(result, tau2, mid, end) &&
                result[|result|-1] == last
                );
    {
        tau + nFalses(start - n) + tau1[start..mid] + tau2[mid..end] +
            [last]
    }

    function combine1(tau : seq<bool>, tau1 : seq<bool>, n : int,
        start : int, v : int, last : bool) : seq<bool>
        requires 0 <= n <= start <= v;
        requires |tau| == n;
        requires |tau1| == v;
        ensures |combine1(tau, tau1, n, start, v, last)| == v + 1;
        ensures agree(combine1(tau, tau1, n, start, v, last),
            tau, 0, n);
        ensures agree(combine1(tau, tau1, n, start, v, last),
            tau1, start, v);
        ensures combine1(tau, tau1, n, start, v, last)[v] == last;
    {
        tau + nFalses(start - n) + tau1[start..v] + [last]
    }

    predicate tseitinSameValue(f : FormulaT, rf : seq<seq<int>>, v : int,
        n : int, start : int, end : int)
        requires valid(f, rf, v, n, start, end);
    {
        forall tau : seq<bool> | |tau| >= end && truthValueCnfFormula(rf, tau) ::
            (
            variablesUpToMonotone(f, n, |tau|);
            truthValueLiteral(posVarToLit(v), tau) == truthValue(f, tau)
            )
    }

    lemma lemmaAndClauses(v1 : int, v2 : int, v : int, tau : seq<bool>)
        requires validVariable(v1);
        requires validVariable(v2);
        requires validVariable(v);
        requires |tau| > v;
        requires |tau| > v1;
        requires |tau| > v2;
        ensures truthValueCnfFormula(andClauses(v1, v2, v), tau) <==>
            ((truthValueLiteral(posVarToLit(v1), tau) &&
            truthValueLiteral(posVarToLit(v2), tau)) <==>
            truthValueLiteral(posVarToLit(v), tau));
    {
        ghost var rf := andClauses(v1, v2, v);
        assert truthValueCnfFormula(rf, tau) <==>
            truthValueClause(rf[0], tau) &&
            truthValueClause(rf[1], tau) &&
            truthValueClause(rf[2], tau);
        assert truthValueClause(rf[0], tau) <==>
            truthValueLiteral(rf[0][0], tau) ||
            truthValueLiteral(rf[0][1], tau);
        assert truthValueClause(rf[1], tau) <==>
            truthValueLiteral(rf[1][0], tau) ||
            truthValueLiteral(rf[1][1], tau);
        assert truthValueClause(rf[2], tau) <==>
            truthValueLiteral(rf[2][0], tau) ||
            truthValueLiteral(rf[2][1], tau) ||
            truthValueLiteral(rf[2][2], tau);
    }

    lemma lemmaOrClauses(v1 : int, v2 : int, v : int, tau : seq<bool>)
        requires validVariable(v1);
        requires validVariable(v2);
        requires validVariable(v);
        requires |tau| > v;
        requires |tau| > v1;
        requires |tau| > v2;
        ensures truthValueCnfFormula(orClauses(v1, v2, v), tau) <==>
            ((truthValueLiteral(posVarToLit(v1), tau) ||
            truthValueLiteral(posVarToLit(v2), tau)) <==>
            truthValueLiteral(posVarToLit(v), tau));
    {
        ghost var rf := orClauses(v1, v2, v);
        assert truthValueCnfFormula(rf, tau) <==>
            truthValueClause(rf[0], tau) &&
            truthValueClause(rf[1], tau) &&
            truthValueClause(rf[2], tau);
        assert truthValueClause(rf[0], tau) <==>
            truthValueLiteral(rf[0][0], tau) ||
            truthValueLiteral(rf[0][1], tau) ||
            truthValueLiteral(rf[0][2], tau);
        assert truthValueClause(rf[1], tau) <==>
            truthValueLiteral(rf[1][0], tau) ||
            truthValueLiteral(rf[1][1], tau);
        assert truthValueClause(rf[2], tau) <==>
            truthValueLiteral(rf[2][0], tau) ||
            truthValueLiteral(rf[2][1], tau);
    }

    lemma lemmaImpliesClauses(v1 : int, v2 : int, v : int, tau : seq<bool>)
        requires validVariable(v1);
        requires validVariable(v2);
        requires validVariable(v);
        requires |tau| > v;
        requires |tau| > v1;
        requires |tau| > v2;
        ensures truthValueCnfFormula(impliesClauses(v1, v2, v), tau) <==>
            ((truthValueLiteral(posVarToLit(v1), tau) ==>
            truthValueLiteral(posVarToLit(v2), tau)) <==>
            truthValueLiteral(posVarToLit(v), tau));
    {
        ghost var rf := impliesClauses(v1, v2, v);
        assert truthValueCnfFormula(rf, tau) <==>
            truthValueClause(rf[0], tau) &&
            truthValueClause(rf[1], tau) &&
            truthValueClause(rf[2], tau);
        assert truthValueClause(rf[0], tau) <==>
            truthValueLiteral(rf[0][0], tau) ||
            truthValueLiteral(rf[0][1], tau) ||
            truthValueLiteral(rf[0][2], tau);
        assert truthValueClause(rf[1], tau) <==>
            truthValueLiteral(rf[1][0], tau) ||
            truthValueLiteral(rf[1][1], tau);
        assert truthValueClause(rf[2], tau) <==>
            truthValueLiteral(rf[2][0], tau) ||
            truthValueLiteral(rf[2][1], tau);
    }

    lemma lemmaDimpliesClauses(v1 : int, v2 : int, v : int, tau : seq<bool>)
        requires validVariable(v1);
        requires validVariable(v2);
        requires validVariable(v);
        requires |tau| > v;
        requires |tau| > v1;
        requires |tau| > v2;
        ensures truthValueCnfFormula(dimpliesClauses(v1, v2, v), tau) <==>
            ((truthValueLiteral(posVarToLit(v1), tau) <==>
            truthValueLiteral(posVarToLit(v2), tau)) <==>
            truthValueLiteral(posVarToLit(v), tau));
    {
        ghost var rf := dimpliesClauses(v1, v2, v);
        assert truthValueCnfFormula(rf, tau) <==>
            truthValueClause(rf[0], tau) &&
            truthValueClause(rf[1], tau) &&
            truthValueClause(rf[2], tau) &&
            truthValueClause(rf[3], tau);
        assert truthValueClause(rf[0], tau) <==>
            truthValueLiteral(rf[0][0], tau) ||
            truthValueLiteral(rf[0][1], tau) ||
            truthValueLiteral(rf[0][2], tau);
        assert truthValueClause(rf[1], tau) <==>
            truthValueLiteral(rf[1][0], tau) ||
            truthValueLiteral(rf[1][1], tau) ||
            truthValueLiteral(rf[1][2], tau);
        assert truthValueClause(rf[2], tau) <==>
            truthValueLiteral(rf[2][0], tau) ||
            truthValueLiteral(rf[2][1], tau) ||
            truthValueLiteral(rf[2][2], tau);
        assert truthValueClause(rf[3], tau) <==>
            truthValueLiteral(rf[3][0], tau) ||
            truthValueLiteral(rf[3][1], tau) ||
            truthValueLiteral(rf[3][2], tau);
    }

    lemma lemmaNotClauses(v1 : int, v : int, tau : seq<bool>)
        requires validVariable(v1);
        requires validVariable(v);
        requires |tau| > v;
        requires |tau| > v1;
        ensures truthValueCnfFormula(notClauses(v1, v), tau) <==>
            ((!truthValueLiteral(posVarToLit(v1), tau)) <==>
            truthValueLiteral(posVarToLit(v), tau));
    {
        ghost var rf := notClauses(v1, v);
        assert truthValueCnfFormula(rf, tau) <==>
            truthValueClause(rf[0], tau) &&
            truthValueClause(rf[1], tau);
        assert truthValueClause(rf[0], tau) <==>
            truthValueLiteral(rf[0][0], tau) ||
            truthValueLiteral(rf[0][1], tau);
        assert truthValueClause(rf[1], tau) <==>
            truthValueLiteral(rf[1][0], tau) ||
            truthValueLiteral(rf[1][1], tau);
    }
}
    
