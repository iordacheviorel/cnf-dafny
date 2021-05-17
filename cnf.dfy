include "formula.dfy"
include "utils.dfy"

module Cnf {

    import opened Formula
    import opened Utils

    method applyRule1(f : FormulaT,
        ghost orsAboveLeft : int, ghost andsAboveLeft : int) returns (r : FormulaT)
        requires validFormulaT(f);
        requires f.DImplies?;
        requires orsAboveLeft >= 0;
        requires andsAboveLeft >= 0;
        ensures validFormulaT(r);
        ensures equivalent(f, r);

        ensures weightOfAnds(r) <= weightOfAnds(f);
        ensures countDImplies(r) < countDImplies(f);
        ensures
            smaller(measure(r, orsAboveLeft, andsAboveLeft),
            measure(f, orsAboveLeft, andsAboveLeft));
    {
        var DImplies(f1, f2) := f;
        r := And(Implies(f1, f2), Implies(f2, f1));

        assert countDImplies(And(Implies(f1, f2), Implies(f2, f1))) ==
            countDImplies(Implies(f1, f2)) + countDImplies(Implies(f2, f1));

        assert countDImplies(And(Implies(f1, f2), Implies(f2, f1))) ==
            2 * (countDImplies(f1) + countDImplies(f2));

        assert countDImplies(DImplies(f1, f2)) ==
            1 + pow(2, countDImplies(f1) + countDImplies(f2));

        mult2_upper(countDImplies(f1) + countDImplies(f2));
    }

    method applyRule2(f : FormulaT,
        ghost orsAboveLeft : int, ghost andsAboveLeft : int) returns (r : FormulaT)
        requires validFormulaT(f);
        requires f.Implies?;
        requires orsAboveLeft >= 0;
        requires andsAboveLeft >= 0;
        ensures validFormulaT(r);
        ensures equivalent(f, r);

        ensures weightOfAnds(r) <= weightOfAnds(f);
        ensures countDImplies(r) <= countDImplies(f); 
        ensures countImplies(r) < countImplies(f); 
        ensures
            smaller(measure(r, orsAboveLeft, andsAboveLeft),
            measure(f, orsAboveLeft, andsAboveLeft));
    {
        var Implies(f1, f2) := f;
        r := Or(Not(f1), f2);
        assert weightOfAnds(r) <= weightOfAnds(f);
    }

    method applyRule3(f : FormulaT,
        ghost orsAboveLeft : int, ghost andsAboveLeft : int) returns (r : FormulaT)
        requires validFormulaT(f);
        requires f.Or?;
        requires f.f2.And?;
        requires orsAboveLeft >= 0;
        requires andsAboveLeft >= 0;
        ensures validFormulaT(r);
        ensures equivalent(f, r);

        ensures weightOfAnds(r) < weightOfAnds(f);
        ensures
            smaller(measure(r, orsAboveLeft, andsAboveLeft),
            measure(f, orsAboveLeft, andsAboveLeft));
    {
        var Or(f1, f2) := f;
        var And(f21, f22) := f2;
        r := And(Or(f1, f21), Or(f1, f22));
    }

    method applyRule4(f : FormulaT,
        ghost orsAboveLeft : int, ghost andsAboveLeft : int) returns (r : FormulaT)
        requires validFormulaT(f);
        requires f.Or?;
        requires f.f1.And?;
        requires orsAboveLeft >= 0;
        requires andsAboveLeft >= 0;
        ensures validFormulaT(r);
        ensures equivalent(f, r);

        ensures weightOfAnds(r) < weightOfAnds(f);
        ensures
            smaller(measure(r, orsAboveLeft, andsAboveLeft),
            measure(f, orsAboveLeft, andsAboveLeft));
    {
        var Or(f1, f2) := f;
        var And(f11, f12) := f1;
        r := And(Or(f11, f2), Or(f12, f2));
    }
   
    lemma Rule5Prop(f1 : FormulaT, f2 : FormulaT, f3 : FormulaT,
        orsAboveLeft : int)
        requires orsAboveLeft >= 0;
        ensures countOrPairs(Or(Or(f1, f2), f3), orsAboveLeft) <
            countOrPairs(Or(f1, Or(f2, f3)), orsAboveLeft);
    {
        assert countOrPairs(Or(f1, Or(f2, f3)), orsAboveLeft) ==
            countOrPairs(f1, orsAboveLeft) + countOrPairs(f2, orsAboveLeft + 1) +
            countOrPairs(f3, orsAboveLeft + 2) + orsAboveLeft + orsAboveLeft + 1;
        assert countOrPairs(Or(Or(f1, f2), f3), orsAboveLeft) ==
            countOrPairs(f1, orsAboveLeft) +
            countOrPairs(f2, orsAboveLeft + 1) +
            countOrPairs(f3, orsAboveLeft + 1) + orsAboveLeft + orsAboveLeft;
        Rule5PropAux(f3, orsAboveLeft + 1);
        assert countOrPairs(f3, orsAboveLeft + 1) <= countOrPairs(f3, orsAboveLeft + 2); 
        assert countOrPairs(Or(Or(f1, f2), f3), orsAboveLeft) <
            countOrPairs(Or(f1, Or(f2, f3)), orsAboveLeft);
    }

    lemma Rule5PropAux(f: FormulaT, orsAboveLeft : int)
        requires orsAboveLeft >= 0;
        ensures countOrPairs(f, orsAboveLeft) <= countOrPairs(f, orsAboveLeft + 1);
    {
    } 

    method applyRule5(f : FormulaT,
        ghost orsAboveLeft : int, ghost andsAboveLeft : int) returns (r : FormulaT)
        requires validFormulaT(f);
        requires f.Or?;
        requires f.f2.Or?;
        requires orsAboveLeft >= 0;
        requires andsAboveLeft >= 0;
        ensures validFormulaT(r);
        ensures equivalent(f, r);

        ensures weightOfAnds(r) <= weightOfAnds(f);
        ensures countDImplies(r) <= countDImplies(f);
        ensures countImplies(r) <= countImplies(f);
        ensures countOrPairs(r, orsAboveLeft) < countOrPairs(f, orsAboveLeft);
        ensures 
            smaller(measure(r, orsAboveLeft, andsAboveLeft),
            measure(f, orsAboveLeft, andsAboveLeft));
    {
        var Or(f1, f2) := f;
        var Or(f21, f22) := f2;
        r := Or(Or(f1, f21), f22);
        Rule5Prop(f1, f21, f22, orsAboveLeft);
        assert countOrPairs(r, orsAboveLeft) < countOrPairs(f, orsAboveLeft);
   }

   lemma Rule6Prop(f1 : FormulaT, f2 : FormulaT, f3 : FormulaT,
       andsAboveLeft : int)
       requires andsAboveLeft >= 0;
       ensures countAndPairs(And(And(f1, f2), f3), andsAboveLeft) <
        countAndPairs(And(f1, And(f2, f3)), andsAboveLeft);
    {
        assert countAndPairs(And(f1, And(f2, f3)), andsAboveLeft) ==
            countAndPairs(f1, andsAboveLeft) +
            countAndPairs(f2, andsAboveLeft + 1) +
            countAndPairs(f3, andsAboveLeft + 2) + andsAboveLeft + andsAboveLeft + 1;
        assert countAndPairs(And(And(f1, f2), f3), andsAboveLeft) ==
            countAndPairs(f1, andsAboveLeft) +
            countAndPairs(f2, andsAboveLeft + 1) +
            countAndPairs(f3, andsAboveLeft + 1) + andsAboveLeft + andsAboveLeft;
        Rule6PropAux(f3, andsAboveLeft + 1);
        assert countAndPairs(f3, andsAboveLeft + 1) <=
            countAndPairs(f3, andsAboveLeft + 2); 
        assert countAndPairs(And(And(f1, f2), f3), andsAboveLeft) <
            countAndPairs(And(f1, And(f2, f3)), andsAboveLeft);
    }
    
    lemma Rule6PropAux(f: FormulaT, andsAboveLeft : int)
        requires andsAboveLeft >= 0;
        ensures countAndPairs(f, andsAboveLeft) <= countAndPairs(f, andsAboveLeft + 1);
    {
    } 
    
    method applyRule6(f : FormulaT,
        ghost orsAboveLeft : int, ghost andsAboveLeft : int) returns (r : FormulaT)
        requires validFormulaT(f);
        requires f.And?;
        requires f.f2.And?;
        requires orsAboveLeft >= 0;
        requires andsAboveLeft >= 0;
        ensures validFormulaT(r);
        ensures equivalent(f, r);

        ensures weightOfAnds(r) <= weightOfAnds(f);
        ensures countDImplies(r) <= countDImplies(f);
        ensures countImplies(r) <= countImplies(f);
        ensures countOrPairs(r, orsAboveLeft) <= countOrPairs(f, orsAboveLeft);
        ensures countAndPairs(r, andsAboveLeft) < countAndPairs(f, andsAboveLeft);
        ensures 
            smaller(measure(r, orsAboveLeft, andsAboveLeft),
            measure(f, orsAboveLeft, andsAboveLeft));
    {
        var And(f1, f2) := f;
        var And(f21, f22) := f2;
        r := And(And(f1, f21), f22);
        Rule6Prop(f1, f21, f22, andsAboveLeft);
        assert countAndPairs(r, andsAboveLeft) < countAndPairs(f, andsAboveLeft);
    }

    lemma Rule7Prop(f1 : FormulaT, f2 : FormulaT)
        requires weightOfAnds(f1) >= 2;
        requires weightOfAnds(f2) >= 2;
        ensures weightOfAnds(And(Not(f1), Not(f2))) < weightOfAnds(Not(Or(f1, f2)));
    {
        assert weightOfAnds(And(Not(f1), Not(f2))) ==
            pow(2, weightOfAnds(f1)) + pow(2, weightOfAnds(f2)) + 1;
        assert weightOfAnds(Not(Or(f1, f2))) ==
            pow(2, weightOfAnds(f1) * weightOfAnds(f2));
        if (weightOfAnds(f1) >= weightOfAnds(f2)) {
            sumpow_upper(weightOfAnds(f1), weightOfAnds(f2));
            assert pow(2, weightOfAnds(f1)) + pow(2, weightOfAnds(f2)) + 1 <
                pow(2, weightOfAnds(f1) * weightOfAnds(f2));
            assert weightOfAnds(And(Not(f1), Not(f2))) <
                weightOfAnds(Not(Or(f1, f2)));
        } else {
            sumpow_upper(weightOfAnds(f2), weightOfAnds(f1));
        }
    }
    
    method applyRule7(f : FormulaT,
        ghost orsAboveLeft : int, ghost andsAboveLeft : int) returns (r : FormulaT)
        requires validFormulaT(f);
        requires f.Not?;
        requires f.f1.Or?;
        requires orsAboveLeft >= 0;
        requires andsAboveLeft >= 0;
        ensures validFormulaT(r);
        ensures equivalent(f, r);

        ensures weightOfAnds(r) < weightOfAnds(f);
        ensures
            smaller(measure(r, orsAboveLeft, andsAboveLeft),
            measure(f, orsAboveLeft, andsAboveLeft));
    {
        var Not(f1) := f;
        var Or(f11, f12) := f1;
        r := And(Not(f11), Not(f12));
        Rule7Prop(f11, f12);
        assert weightOfAnds(r) < weightOfAnds(f);
    }

    lemma Rule8Prop(f1 : FormulaT, f2 : FormulaT)
        requires weightOfAnds(f1) >= 2;
        requires weightOfAnds(f2) >= 2;
        ensures weightOfAnds(Or(Not(f1), Not(f2))) < weightOfAnds(Not(And(f1, f2)));
    {
        assert weightOfAnds(Or(Not(f1), Not(f2))) ==
            pow(2, weightOfAnds(f1)) * pow(2, weightOfAnds(f2));
        assert weightOfAnds(Not(And(f1, f2))) ==
            pow(2, weightOfAnds(f1) + weightOfAnds(f2) + 1);
        assert pow(2, weightOfAnds(f1) + weightOfAnds(f2)) * 2 ==
            pow(2, weightOfAnds(f1) + weightOfAnds(f2) + 1);
        multpow_powsum(weightOfAnds(f1), weightOfAnds(f2));
        assert pow(2, weightOfAnds(f1)) * pow(2, weightOfAnds(f2)) ==
            pow(2, weightOfAnds(f1) + weightOfAnds(f2));
    }

    method applyRule8(f : FormulaT,
        ghost orsAboveLeft : int, ghost andsAboveLeft : int) returns (r : FormulaT)
        requires validFormulaT(f);
        requires f.Not?;
        requires f.f1.And?;
        requires orsAboveLeft >= 0;
        requires andsAboveLeft >= 0;
        ensures validFormulaT(r);
        ensures equivalent(f, r);

        ensures weightOfAnds(r) < weightOfAnds(f);
        ensures
            smaller(measure(r, orsAboveLeft, andsAboveLeft),
            measure(f, orsAboveLeft, andsAboveLeft));
    {
        var Not(f1) := f;
        var And(f11, f12) := f1;
        r := Or(Not(f11), Not(f12));
        Rule8Prop(f11, f12);
        assert weightOfAnds(r) < weightOfAnds(f);
    }

    lemma Rule9Prop(f1 : FormulaT)
        requires weightOfAnds(f1) >= 2;
        ensures weightOfAnds(f1) < weightOfAnds(Not(Not(f1)));
    {
        pow_increases(weightOfAnds(f1));
        pow_increases(pow(2, weightOfAnds(f1)));
        assert weightOfAnds(Not(Not(f1))) == pow(2, pow(2, weightOfAnds(f1)));
    }

    method applyRule9(f : FormulaT,
        ghost orsAboveLeft : int, ghost andsAboveLeft : int) returns (r : FormulaT)
        requires validFormulaT(f);
        requires f.Not?;
        requires f.f1.Not?;
        requires orsAboveLeft >= 0;
        requires andsAboveLeft >= 0;
        ensures validFormulaT(r);
        ensures equivalent(f, r);

        ensures weightOfAnds(r) < weightOfAnds(f);
        ensures
            smaller(measure(r, orsAboveLeft, andsAboveLeft),
            measure(f, orsAboveLeft, andsAboveLeft));
    {
        var Not(f1) := f;
        var Not(f11) := f1;
        r := f11;
        Rule9Prop(f11);
        assert weightOfAnds(r) < weightOfAnds(f);
    }
    
    method applyAtTop(f : FormulaT,
        ghost orsAboveLeft : int, ghost andsAboveLeft : int)
        returns (r : FormulaT)
        decreases f;
        requires orsAboveLeft >= 0;
        requires andsAboveLeft >= 0;
        requires validFormulaT(f);
        ensures validFormulaT(r);
        ensures equivalent(f, r);
        ensures f == r ==> !f.Implies?;
        ensures f == r ==> !f.DImplies?;
        ensures r == f || Utils.smaller(measure(r, orsAboveLeft, andsAboveLeft),
                measure(f, orsAboveLeft, andsAboveLeft));
    {
        match f
        {
            case DImplies(f1, f2) => { 
                r := applyRule1(f, orsAboveLeft, andsAboveLeft);
            }
            case Implies(f1, f2) => {
                r := applyRule2(f, orsAboveLeft, andsAboveLeft);
            }
            case Or(f1, f2) => {
                if (f2.And?) {
                    r := applyRule3(f, orsAboveLeft, andsAboveLeft);
                } else if (f2.Or?) {
                    r := applyRule5(f, orsAboveLeft, andsAboveLeft);
                } else if (f1.And?) {
                    r := applyRule4(f, orsAboveLeft, andsAboveLeft);
                } else {
                    r := f;
                }
            }
            case And(f1, f2) => {
                if (f2.And?) {
                    r := applyRule6(f, orsAboveLeft, andsAboveLeft);
                } else {
                    r := f;
                }
            }
            case Var(val) => {
                r := f;
            }
            case Not(f1) => {
                if (f1.Or?) {
                    r := applyRule7(f, orsAboveLeft, andsAboveLeft);
                } else if (f1.And?) {
                    r := applyRule8(f, orsAboveLeft, andsAboveLeft);
                } else if (f1.Not?) {
                    r := applyRule9(f, orsAboveLeft, andsAboveLeft);
                } else {
                    r := f;
                }
            }
        }
    }

    lemma Rule3Or(f1 : FormulaT, f2 : FormulaT, f3 : FormulaT)
        requires weightOfAnds(f3) < weightOfAnds(f2);
        requires weightOfAnds(f1) >= 2;
        requires weightOfAnds(f2) >= 2;
        requires weightOfAnds(f3) >= 2;
        ensures weightOfAnds(Or(f1, f3)) < weightOfAnds(Or(f1, f2));
    {
        assert weightOfAnds(Or(f1, f3)) == weightOfAnds(f1) * weightOfAnds(f3);
        assert weightOfAnds(Or(f1, f2)) == weightOfAnds(f1) * weightOfAnds(f2);
        lessthan_mult_right(weightOfAnds(f1), weightOfAnds(f2), weightOfAnds(f3));
        assert weightOfAnds(f1) * weightOfAnds(f3) < weightOfAnds(f1) * weightOfAnds(f2);
    }

    function weightOfAnds(f : FormulaT) : (res : int)
        decreases f;
        ensures res >= 2;
    {
        match f
        {
            case Var(val) =>
                2
            case Not(f1) =>
                pow(2, weightOfAnds(f1))
            case And(f1, f2) =>
                weightOfAnds(f1) + weightOfAnds(f2) + 1
            case Or(f1, f2) =>
                weightOfAnds(f1) * weightOfAnds(f2)
            case Implies(f1, f2) =>
                pow(2, weightOfAnds(f1)) * weightOfAnds(f2)
            case DImplies(f1, f2) =>
                pow(2, weightOfAnds(f1)) * weightOfAnds(f2) +
                pow(2, weightOfAnds(f2)) * weightOfAnds(f1) + 1
        }
    }

    function countDImplies(f : FormulaT) : (res : int)
        decreases f;
        ensures res >= 0;
    {
        match f
        {
            case Or(f11,f12) =>
                countDImplies(f11) + countDImplies(f12)
            case And(f11,f12) =>
                countDImplies(f11) + countDImplies(f12)
            case Not(f11) =>
                countDImplies(f11)
            case Var(val) =>
                0
            case Implies(f11,f12) =>
                countDImplies(f11) + countDImplies(f12)
            case DImplies(f11,f12) => 
                1 + pow(2, countDImplies(f11) + countDImplies(f12))
        }
    }

    function countImplies(f : FormulaT) : (res : int)
        decreases f;
        ensures res >= 0;
    {
        match f
        {
            case Or(f11,f12) =>
                countImplies(f11) + countImplies(f12)
            case And(f11,f12) =>
                countImplies(f11) + countImplies(f12)
            case Not(f11) =>
                countImplies(f11)
            case Var(val) =>
                0
            case Implies(f11,f12) =>
                countImplies(f11) + countImplies(f12)  + 1
            case DImplies(f11,f12) =>
                countImplies(f11) + countImplies(f12)
        }
    }

    function countAndPairs(f : FormulaT, andsAboveLeft : int) : (res : int)
        decreases f;
        requires andsAboveLeft >= 0;
        ensures res >= 0;
    {
        match f
        {
            case And(f11,f12) =>
                countAndPairs(f11, andsAboveLeft) + countAndPairs(f12, andsAboveLeft + 1) + andsAboveLeft
            case Or(f11,f12) =>
                countAndPairs(f11, andsAboveLeft) + countAndPairs(f12, andsAboveLeft)
            case Var(val) =>
                0
            case Implies(f11,f12) =>
                countAndPairs(f11, andsAboveLeft) + countAndPairs(f12, andsAboveLeft)
            case DImplies(f11,f12) =>
                countAndPairs(f11, andsAboveLeft) + countAndPairs(f12, andsAboveLeft)
            case Not(f1) =>
                countAndPairs(f1, andsAboveLeft)
        }
    }

    function countOrPairs(f : FormulaT, orsAboveLeft : int) : (res : int)
        decreases f;
        requires orsAboveLeft >= 0;
        ensures res >= 0;
    {
        match f
        {
            case Or(f11,f12) =>
                countOrPairs(f11, orsAboveLeft) + countOrPairs(f12, orsAboveLeft + 1) + orsAboveLeft
            case And(f11,f12) =>
                countOrPairs(f11, orsAboveLeft) + countOrPairs(f12, orsAboveLeft)
            case Var(val) => 0
            case Implies(f11,f12) =>
                countOrPairs(f11, orsAboveLeft) + countOrPairs(f12, orsAboveLeft)
            case DImplies(f11,f12) =>
                countOrPairs(f11, orsAboveLeft) + countOrPairs(f12, orsAboveLeft)
            case Not(f1) =>
                countOrPairs(f1, orsAboveLeft)
        }
    }

    lemma Rule3UnderNot(f1 : FormulaT, f2 : FormulaT)
        requires weightOfAnds(f1) <=  weightOfAnds(f2);
        ensures weightOfAnds(Not(f1)) <= weightOfAnds(Not(f2));
    {
        assert weightOfAnds(Not(f1)) ==  pow(2, weightOfAnds(f1));
        assert weightOfAnds(Not(f2)) ==  pow(2, weightOfAnds(f2));
        pow_monotone(weightOfAnds(f1), weightOfAnds(f2));
    }

    lemma Rule3UnderNot2(f1 : FormulaT, f2 : FormulaT)
        requires weightOfAnds(f1) <  weightOfAnds(f2);
        ensures weightOfAnds(Not(f1)) < weightOfAnds(Not(f2));
    {
        assert weightOfAnds(Not(f1)) ==  pow(2, weightOfAnds(f1));
        assert weightOfAnds(Not(f2)) ==  pow(2, weightOfAnds(f2));
        pow_monotone_strict(weightOfAnds(f1), weightOfAnds(f2));
    }

    method applyRule(f : FormulaT,
        ghost orsAboveLeft : int, ghost andsAboveLeft : int) returns (r : FormulaT)
        requires validFormulaT(f);
        ensures validFormulaT(r);
        ensures equivalent(f, r);
        decreases f;
        requires orsAboveLeft >= 0;
        requires andsAboveLeft >= 0;
        requires orsAboveLeft >= 0;
        ensures r == f ||
            Utils.smaller(measure(r, orsAboveLeft, andsAboveLeft),
            measure(f, orsAboveLeft, andsAboveLeft));
    {
        var res : FormulaT := applyAtTop(f, orsAboveLeft, andsAboveLeft);

        if (res != f) {
            return res;
        } else if (f.Or?) {
            var f1_step := applyRule(f.f1, orsAboveLeft, andsAboveLeft);
            if (f.f1 == f1_step) {
                var f2_step := applyRule(f.f2, orsAboveLeft + 1, andsAboveLeft);
                assert equivalent(f.f2, f2_step);
                assert equivalent(Or(f.f1, f.f2), Or(f.f1, f2_step));
                res := Or(f.f1, f2_step);
                if (weightOfAnds(f2_step) < weightOfAnds(f.f2)) {
                    Rule3Or(f.f1, f.f2, f2_step);
                }
                return res;
            } else {
                assert equivalent(f.f1, f1_step);
                assert equivalent(Or(f.f1, f.f2), Or(f1_step, f.f2));
                res := Or(f1_step, f.f2);
                if (weightOfAnds(f1_step) < weightOfAnds(f.f1)) {
                    Rule3Or(f.f2, f.f1, f1_step);
                }
                return res;
            }
        } else if(f.And?) {
            var f1_step := applyRule(f.f1, orsAboveLeft, andsAboveLeft);
            if (f.f1 == f1_step) {
                var f2_step := applyRule(f.f2, orsAboveLeft, andsAboveLeft + 1);
                res := And(f.f1, f2_step);
                return res;
            } else {
                res := And(f1_step, f.f2);
                return res;
            }
        } else if (f.Not?) {
            assert f ==  Not(f.f1);
            var f1_step := applyRule(f.f1, orsAboveLeft, andsAboveLeft);
            res := Not(f1_step);
            Rule3UnderNot(f1_step, f.f1);
            if (weightOfAnds(f1_step) < weightOfAnds(f.f1)) {
                Rule3UnderNot2(f1_step, f.f1);
            }
            return res;
        } else if (f.Var?) {
            return f;
        } else {
            assert false;
        }
    }

    function measure(f : FormulaT, h1 : int, h2 : int) :
        (int, int, int, int, int)
        requires h1 >= 0;
        requires h2 >= 0;
    {
        (weightOfAnds(f),
            countDImplies(f),
            countImplies(f),
            countOrPairs(f, h1),
            countAndPairs(f, h2))
    }

    method convertToCNF(f : FormulaT) returns (r : FormulaT)
        decreases weightOfAnds(f);               // 3 + 4 + 7 + 8 + 9
        decreases countDImplies(f);         // 1
        decreases countImplies(f);          // 2
        decreases countOrPairs(f, 0);            // 5
        decreases countAndPairs(f, 0);              // 6
        requires validFormulaT(f);
        ensures validFormulaT(r);
        ensures equivalent(f, r);
    {
        var res := applyRule(f, 0, 0);
        assert equivalent(f, res);

        if(res != f) {
            r := convertToCNF(res);
            assert equivalent(res, r);
            equivalentTrans(f, res, r);
        } else {
            r := res;
        }
    }
}
