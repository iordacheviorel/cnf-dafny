include "cnf.dfy"

module Main
{

    import opened Formula
    import opened Cnf
    
    method Main()
    {
        var F0 := Var(0);
        var F1 := Var(1);
        var F2 := Var(2);
        var F3 := Var(3);
        
        var varForRule0 := DImplies(F0, F1);
        var varForRule1 := Implies(F0, F1);
        var varForRule2 := Or(F0, And(F1, F2));
        var varForRule3 := Or(And(F1, F2), DImplies(F0, F1));
        var varForRule5 := Or(F0, Or(F1, F2));
        var varForRule6 := And(F0, And(F1, F2));
        var varForRule7 := Not(And(F0, F1));
        var varForRule8 := Not(Or(F0, F1));
        var varForRule9 := Not(Not(F0));
        
        var testFormula := DImplies(Or(F1, F2), F0);
        
        var out1 := prettyPrint(testFormula);
        print out1, "\n";
        
        var cnf := convertToCNF(testFormula);
        
        var out2 := prettyPrint(testFormula);
        print out2, "\n";
    }
}
