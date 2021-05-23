# CNF-DAFNY

A verified implementation in Dafny of two algorithms for finding the
CNF of a propositional formula:

## The textbook Algorithm

The textbook algorithm applies the following rewrite rules
left-to-write for as long as possible:

1. φ₁ ⇔ φ₂ ≡ (φ₁ ⇒ φ₂) ∧ (φ₂ ⇒ φ₁);

2. φ₂ ⇒ φ₁ ≡ ¬ φ₁ ∨ φ₂

3. φ₁ ∨ (φ₂ ∧ φ_3) ≡ (φ₁ ∨ φ₂) ∧ (φ₁ ∨ φ_3);

4. (φ₂ ∧ φ_3) ∨ φ₁ ≡ (φ₂ ∨ φ₁) ∧ (φ_3 ∨ φ₁);

5. φ₁ ∨ (φ₂ ∨ φ_3) ≡ (φ₁ ∨ φ₂) ∨ φ_3;

6. φ₁ ∧ (φ₂ ∧ φ_3) ≡ (φ₁ ∧ φ₂) ∧ φ_3;

7. ¬ (φ₁ ∨ φ₂) ≡ ¬ φ₁ ∧ ¬ φ₂;

8. ¬ (φ₁ ∧ φ₂) ≡ ¬ φ₁ ∨ ¬ φ₂;

9. ¬ ¬ φ ≡ φ.

We prove in Dafny that and algorithm applying the rewrite rules
terminates and that it produces an equivalent formula.

## Tseitin's Transformation

Unfortunately, the rewrite rules above can produce a formula
exponentially larger than the input formula. A better way to obtain a
CNF is to use Tseitin's algorithm, which produces a formula that has
size linear in the size of the initial formula. The resulting formula
is only equisatisfiable (not equivalent in general) to the initial
formula.

Here is how Tseitin's algorithm works on an example. Consider the
formula φ = ¬ x₁ ∨ x₂ . Choose fresh variables y₁, y₂ for the two
subformulae ¬ x₁ and ¬ x₁ ∨ x₂ , respectively. Add to the resulting
CNF clauses that encode that each of the two variables is equivalent
to the corresponding subformula:

1. for y₁ ≡ ¬ x₁, add the clauses y₁ ∨ x₁, ¬ y₁ ∨ ¬ x₁;

2. for y₂ ≡ y₁ ∨ x₂, add the clauses: ¬ y₁ ∨ y₂, ¬ x₂ ∨ y₂, ¬ y₂
   ∨ y₁ ∨ x₂.

Finally, add a clause consisting of a single literal: the variable
corresponding to the initial formula proposes to add the negation of
this literal, the initial formula being valid iff the resulting
formula is unsatisfiable; modern treatments
diverge~\cite{harrison}.}. The final result is:

    (y₁ ∨ x₁) ∧ (¬ y₁ ∨ ¬ x₁) ∧ (¬ y₁ ∨ y₂) ∧ (¬ x₂ ∨ y₂) ∧ (¬ y₂ ∨ y₁ ∨ x₂) ∧ y₂.

## Contents of the Repository

The Dafny development consists of 8 source files:

1. *utils.dfy* contains generally useful definitions and
   lemmas, such as the definition of exponentiation (*pow*);

2. *formula.dfy* contains the definition of the
   *FormulaT* data type and related functions and lemmas such as
   *validFormulaT*, *truthValue*, *maxVar*;

3. *cnf.dfy* contains the verified implementation of the
   textbook algorithm for finding the CNF (with functions/methods such
   as *convertToCNF* or *applyRule*);
  
4. *cnfformula.dfy* contains various items concerning the
   representation of CNF formulae as elements of type
   *seq<seq<int> >*, such as the predicates
   *validLiteral*, *validCnfFormula*,
   *truthValueCnfFormula*;

5. *tseitin.dfy* contains the entry point (*tseitin*)
   to Tseitin's transformation, together with the main implementatino
   *tseitinCnf*;

6. it relies on *tseitinproofs.dfy*, which contains lemmas
   that prove the invariant of *tseitinCnf* for all cases;

7. both of the modules above rely on *tseitincore.dfy*,
   which contains definitions useful in both the algorithm and its
   proof, such as the set of clauses *orClauses* to be added for
   disjunctions;

8. *main.dfy* exercises the CNF transformation in a
   *Main* method and can be used to obtain an executable;

9. *Makefile* to be used in the usual Unix-like manner.

## Compilation

To compile (and verify) the development, it is sufficient to run:

    dafny /verifySeparately *.dfy

We have verified the source code with Dafny version 3.0.0.20820, but
some earlier versions should work as well.
