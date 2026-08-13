/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFTransitionExprSoundness

/-!
# Atom bounds for compiled transition expressions

The constructive completeness proof assigns the generated Tseitin atoms after
preserving all source atoms.  This file proves the required noninterference
invariant: if every source atom is below `fresh`, every atom mentioned by the
compiled clauses is below the returned `nextFresh`.
-/

namespace LeanTrominoes

namespace PeriodicCNF

/-- Every atom mentioned by a clause list lies below `bound`. -/
def ClausesAtomsBelow (clauses : List (PeriodicClause Nat))
    (bound : Nat) : Prop :=
  ∀ clause ∈ clauses, ∀ literal ∈ clause, literal.atom < bound

theorem clausesAtomsBelow_mono {clauses : List (PeriodicClause Nat)}
    {firstBound secondBound : Nat}
    (bounded : ClausesAtomsBelow clauses firstBound)
    (le : firstBound ≤ secondBound) :
    ClausesAtomsBelow clauses secondBound := by
  intro clause clauseMem literal literalMem
  exact lt_of_lt_of_le (bounded clause clauseMem literal literalMem) le

theorem clausesAtomsBelow_append {first second : List (PeriodicClause Nat)}
    {bound : Nat}
    (firstBound : ClausesAtomsBelow first bound)
    (secondBound : ClausesAtomsBelow second bound) :
    ClausesAtomsBelow (first ++ second) bound := by
  intro clause clauseMem literal literalMem
  rcases List.mem_append.mp clauseMem with inFirst | inSecond
  · exact firstBound clause inFirst literal literalMem
  · exact secondBound clause inSecond literal literalMem

theorem constantClauses_atomsBelow {output bound : Nat} (lt : output < bound)
    (value : Bool) :
    ClausesAtomsBelow (constantClauses output value) bound := by
  simp [ClausesAtomsBelow, constantClauses, TransitionWire.literal,
    gateOutput, lt]

theorem equalityClauses_atomsBelow {output bound : Nat}
    (input : TransitionWire) (outputLt : output < bound)
    (inputLt : input.atom < bound) :
    ClausesAtomsBelow (equalityClauses output input) bound := by
  simp [ClausesAtomsBelow, equalityClauses, TransitionWire.literal,
    gateOutput, outputLt, inputLt]

theorem notClauses_atomsBelow {output bound : Nat}
    (input : TransitionWire) (outputLt : output < bound)
    (inputLt : input.atom < bound) :
    ClausesAtomsBelow (notClauses output input) bound := by
  simp [ClausesAtomsBelow, notClauses, TransitionWire.literal,
    gateOutput, outputLt, inputLt]

theorem andClauses_atomsBelow {output bound : Nat}
    (first second : TransitionWire) (outputLt : output < bound)
    (firstLt : first.atom < bound) (secondLt : second.atom < bound) :
    ClausesAtomsBelow (andClauses output first second) bound := by
  simp [ClausesAtomsBelow, andClauses, TransitionWire.literal,
    gateOutput, outputLt, firstLt, secondLt]

theorem orClauses_atomsBelow {output bound : Nat}
    (first second : TransitionWire) (outputLt : output < bound)
    (firstLt : first.atom < bound) (secondLt : second.atom < bound) :
    ClausesAtomsBelow (orClauses output first second) bound := by
  simp [ClausesAtomsBelow, orClauses, TransitionWire.literal,
    gateOutput, outputLt, firstLt, secondLt]

theorem TransitionExpr.AtomsBelow.mono {expression : TransitionExpr}
    {firstBound secondBound : Nat}
    (bounded : expression.AtomsBelow firstBound)
    (le : firstBound ≤ secondBound) :
    expression.AtomsBelow secondBound := by
  induction expression with
  | constant value => trivial
  | wire input =>
      exact lt_of_lt_of_le bounded le
  | not input ih =>
      exact ih bounded
  | and first second firstIH secondIH =>
      exact ⟨firstIH bounded.1, secondIH bounded.2⟩
  | or first second firstIH secondIH =>
      exact ⟨firstIH bounded.1, secondIH bounded.2⟩

/-- Complete atom-range invariant for structural Tseitin compilation. -/
theorem compileTransitionExpr_atomsBelow (expression : TransitionExpr)
    (fresh : Nat) (sourceBound : expression.AtomsBelow fresh) :
    ClausesAtomsBelow (compileTransitionExpr expression fresh).clauses
      (compileTransitionExpr expression fresh).nextFresh := by
  induction expression generalizing fresh with
  | constant value =>
      apply constantClauses_atomsBelow
      simp [compileTransitionExpr]
  | wire input =>
      apply equalityClauses_atomsBelow
      · simp [compileTransitionExpr]
      · have inputLt : input.atom < fresh := sourceBound
        simp [compileTransitionExpr]
        omega
  | not input ih =>
      let compiled := compileTransitionExpr input fresh
      have inputBound := ih fresh sourceBound
      change ClausesAtomsBelow
        (compiled.clauses ++
          notClauses compiled.nextFresh (gateOutput compiled.root))
        (compiled.nextFresh + 1)
      apply clausesAtomsBelow_append
      · exact clausesAtomsBelow_mono inputBound (Nat.le_succ _)
      · apply notClauses_atomsBelow
        · exact Nat.lt_succ_self _
        · have rootLt := compileTransitionExpr_root_lt_nextFresh input fresh
          change compiled.root < compiled.nextFresh + 1
          dsimp [compiled] at rootLt ⊢
          omega
  | and first second firstIH secondIH =>
      let firstCompiled := compileTransitionExpr first fresh
      let secondCompiled :=
        compileTransitionExpr second firstCompiled.nextFresh
      have freshLeFirst : fresh ≤ firstCompiled.nextFresh := by
        dsimp [firstCompiled]
        rw [compileTransitionExpr_nextFresh]
        omega
      have firstBound := firstIH fresh sourceBound.1
      have secondSource := sourceBound.2.mono freshLeFirst
      have secondBound := secondIH firstCompiled.nextFresh secondSource
      have firstToSecond : firstCompiled.nextFresh ≤
          secondCompiled.nextFresh := by
        have secondNext : secondCompiled.nextFresh =
            firstCompiled.nextFresh + second.gateCount := by
          exact compileTransitionExpr_nextFresh second firstCompiled.nextFresh
        rw [secondNext]
        omega
      change ClausesAtomsBelow
        (firstCompiled.clauses ++ secondCompiled.clauses ++
          andClauses secondCompiled.nextFresh
            (gateOutput firstCompiled.root)
            (gateOutput secondCompiled.root))
        (secondCompiled.nextFresh + 1)
      apply clausesAtomsBelow_append
      · apply clausesAtomsBelow_append
        · exact clausesAtomsBelow_mono firstBound
            (le_trans firstToSecond (Nat.le_succ _))
        · exact clausesAtomsBelow_mono secondBound (Nat.le_succ _)
      · apply andClauses_atomsBelow
        · exact Nat.lt_succ_self _
        · have firstRootLt :=
            compileTransitionExpr_root_lt_nextFresh first fresh
          have firstRootLt' : firstCompiled.root <
              firstCompiled.nextFresh := firstRootLt
          change firstCompiled.root < secondCompiled.nextFresh + 1
          omega
        · have secondRootLt :=
            compileTransitionExpr_root_lt_nextFresh second
              firstCompiled.nextFresh
          have secondRootLt' : secondCompiled.root <
              secondCompiled.nextFresh := secondRootLt
          change secondCompiled.root < secondCompiled.nextFresh + 1
          omega
  | or first second firstIH secondIH =>
      let firstCompiled := compileTransitionExpr first fresh
      let secondCompiled :=
        compileTransitionExpr second firstCompiled.nextFresh
      have freshLeFirst : fresh ≤ firstCompiled.nextFresh := by
        dsimp [firstCompiled]
        rw [compileTransitionExpr_nextFresh]
        omega
      have firstBound := firstIH fresh sourceBound.1
      have secondSource := sourceBound.2.mono freshLeFirst
      have secondBound := secondIH firstCompiled.nextFresh secondSource
      have firstToSecond : firstCompiled.nextFresh ≤
          secondCompiled.nextFresh := by
        have secondNext : secondCompiled.nextFresh =
            firstCompiled.nextFresh + second.gateCount := by
          exact compileTransitionExpr_nextFresh second firstCompiled.nextFresh
        rw [secondNext]
        omega
      change ClausesAtomsBelow
        (firstCompiled.clauses ++ secondCompiled.clauses ++
          orClauses secondCompiled.nextFresh
            (gateOutput firstCompiled.root)
            (gateOutput secondCompiled.root))
        (secondCompiled.nextFresh + 1)
      apply clausesAtomsBelow_append
      · apply clausesAtomsBelow_append
        · exact clausesAtomsBelow_mono firstBound
            (le_trans firstToSecond (Nat.le_succ _))
        · exact clausesAtomsBelow_mono secondBound (Nat.le_succ _)
      · apply orClauses_atomsBelow
        · exact Nat.lt_succ_self _
        · have firstRootLt :=
            compileTransitionExpr_root_lt_nextFresh first fresh
          have firstRootLt' : firstCompiled.root <
              firstCompiled.nextFresh := firstRootLt
          change firstCompiled.root < secondCompiled.nextFresh + 1
          omega
        · have secondRootLt :=
            compileTransitionExpr_root_lt_nextFresh second
              firstCompiled.nextFresh
          have secondRootLt' : secondCompiled.root <
              secondCompiled.nextFresh := secondRootLt
          change secondCompiled.root < secondCompiled.nextFresh + 1
          omega

end PeriodicCNF

end LeanTrominoes
