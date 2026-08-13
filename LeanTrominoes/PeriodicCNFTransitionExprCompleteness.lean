/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFTransitionExprBounds

/-!
# Constructive completeness of transition-expression compilation

Given values for the source current and next slices, this file constructs the
canonical values of every generated Tseitin atom.  The construction preserves
all source atoms and satisfies every compiled clause, completing the semantic
correctness proof for transition expressions.
-/

namespace LeanTrominoes

namespace PeriodicCNF

/-- Canonically assign every generated Tseitin atom.  Recursive subexpressions
are realized first; the enclosing gate output is then written at its fresh
root. -/
def realizeTransitionExpr : TransitionExpr → Nat →
    (Nat → Bool) → (Nat → Bool) → Nat → Bool
  | .constant value, fresh, current, _ =>
      Function.update current fresh value
  | .wire input, fresh, current, next =>
      Function.update current fresh (input.value current next)
  | .not input, fresh, current, next =>
      let compiled := compileTransitionExpr input fresh
      let realized := realizeTransitionExpr input fresh current next
      Function.update realized compiled.nextFresh (!(input.eval current next))
  | .and first second, fresh, current, next =>
      let firstCompiled := compileTransitionExpr first fresh
      let firstRealized := realizeTransitionExpr first fresh current next
      let secondCompiled :=
        compileTransitionExpr second firstCompiled.nextFresh
      let secondRealized := realizeTransitionExpr second
        firstCompiled.nextFresh firstRealized next
      Function.update secondRealized secondCompiled.nextFresh
        (first.eval current next && second.eval current next)
  | .or first second, fresh, current, next =>
      let firstCompiled := compileTransitionExpr first fresh
      let firstRealized := realizeTransitionExpr first fresh current next
      let secondCompiled :=
        compileTransitionExpr second firstCompiled.nextFresh
      let secondRealized := realizeTransitionExpr second
        firstCompiled.nextFresh firstRealized next
      Function.update secondRealized secondCompiled.nextFresh
        (first.eval current next || second.eval current next)

/-- Canonical realization never changes an atom below its initial fresh
boundary. -/
theorem realizeTransitionExpr_preserves (expression : TransitionExpr)
    (fresh : Nat) (current next : Nat → Bool) {atom : Nat}
    (atomLt : atom < fresh) :
    realizeTransitionExpr expression fresh current next atom = current atom := by
  induction expression generalizing fresh current with
  | constant value =>
      simp [realizeTransitionExpr, Function.update, Nat.ne_of_lt atomLt]
  | wire input =>
      simp [realizeTransitionExpr, Function.update, Nat.ne_of_lt atomLt]
  | not input ih =>
      let compiled := compileTransitionExpr input fresh
      have freshLe : fresh ≤ compiled.nextFresh := by
        dsimp [compiled]
        rw [compileTransitionExpr_nextFresh]
        omega
      simp only [realizeTransitionExpr]
      rw [Function.update_of_ne (by omega : atom ≠ compiled.nextFresh)]
      exact ih fresh current atomLt
  | and first second firstIH secondIH =>
      let firstCompiled := compileTransitionExpr first fresh
      let firstRealized := realizeTransitionExpr first fresh current next
      let secondCompiled :=
        compileTransitionExpr second firstCompiled.nextFresh
      have freshLeFirst : fresh ≤ firstCompiled.nextFresh := by
        dsimp [firstCompiled]
        rw [compileTransitionExpr_nextFresh]
        omega
      have firstLeSecond : firstCompiled.nextFresh ≤
          secondCompiled.nextFresh := by
        have secondNext : secondCompiled.nextFresh =
            firstCompiled.nextFresh + second.gateCount :=
          compileTransitionExpr_nextFresh second firstCompiled.nextFresh
        omega
      simp only [realizeTransitionExpr]
      rw [Function.update_of_ne (by omega : atom ≠ secondCompiled.nextFresh)]
      calc
        realizeTransitionExpr second firstCompiled.nextFresh
            firstRealized next atom = firstRealized atom :=
          secondIH firstCompiled.nextFresh firstRealized (by omega)
        _ = current atom := firstIH fresh current atomLt
  | or first second firstIH secondIH =>
      let firstCompiled := compileTransitionExpr first fresh
      let firstRealized := realizeTransitionExpr first fresh current next
      let secondCompiled :=
        compileTransitionExpr second firstCompiled.nextFresh
      have freshLeFirst : fresh ≤ firstCompiled.nextFresh := by
        dsimp [firstCompiled]
        rw [compileTransitionExpr_nextFresh]
        omega
      have firstLeSecond : firstCompiled.nextFresh ≤
          secondCompiled.nextFresh := by
        have secondNext : secondCompiled.nextFresh =
            firstCompiled.nextFresh + second.gateCount :=
          compileTransitionExpr_nextFresh second firstCompiled.nextFresh
        omega
      simp only [realizeTransitionExpr]
      rw [Function.update_of_ne (by omega : atom ≠ secondCompiled.nextFresh)]
      calc
        realizeTransitionExpr second firstCompiled.nextFresh
            firstRealized next atom = firstRealized atom :=
          secondIH firstCompiled.nextFresh firstRealized (by omega)
        _ = current atom := firstIH fresh current atomLt

/-- The enclosing root receives the direct expression value. -/
@[simp]
theorem realizeTransitionExpr_root (expression : TransitionExpr)
    (fresh : Nat) (current next : Nat → Bool) :
    realizeTransitionExpr expression fresh current next
        (compileTransitionExpr expression fresh).root =
      expression.eval current next := by
  cases expression <;>
    simp [realizeTransitionExpr, compileTransitionExpr,
      TransitionExpr.eval, Function.update]

/-- Expression evaluation is unchanged when current-slice source atoms agree
below their declared bound. -/
theorem TransitionExpr.eval_congr_current {expression : TransitionExpr}
    {bound : Nat} (atoms : expression.AtomsBelow bound)
    {first second next : Nat → Bool}
    (agree : ∀ atom < bound, first atom = second atom) :
    expression.eval first next = expression.eval second next := by
  induction expression with
  | constant value => rfl
  | wire input =>
      cases input with
      | mk slice atom =>
          cases slice with
          | current =>
              exact agree atom atoms
          | next => rfl
  | not input ih =>
      simp only [TransitionExpr.eval]
      rw [ih atoms]
  | and firstExpr secondExpr firstIH secondIH =>
      simp only [TransitionExpr.eval]
      rw [firstIH atoms.1, secondIH atoms.2]
  | or firstExpr secondExpr firstIH secondIH =>
      simp only [TransitionExpr.eval]
      rw [firstIH atoms.1, secondIH atoms.2]

private theorem literal_holdsBetween_congr_current
    {bound : Nat} {first second next : Nat → Bool}
    {literal : PeriodicLiteral Nat}
    (atomBound : literal.atom < bound)
    (agree : ∀ atom < bound, first atom = second atom) :
    literal.HoldsBetween first next ↔ literal.HoldsBetween second next := by
  constructor
  · rintro (⟨offset, value⟩ | ⟨offset, value⟩)
    · exact Or.inl ⟨offset, by simpa [agree literal.atom atomBound] using value⟩
    · exact Or.inr ⟨offset, value⟩
  · rintro (⟨offset, value⟩ | ⟨offset, value⟩)
    · exact Or.inl ⟨offset, by simpa [agree literal.atom atomBound] using value⟩
    · exact Or.inr ⟨offset, value⟩

/-- Clause satisfaction is stable under changes above the proved atom bound. -/
theorem clausesHoldBetween_congr_current
    {clauses : List (PeriodicClause Nat)} {bound : Nat}
    (atoms : ClausesAtomsBelow clauses bound)
    {first second next : Nat → Bool}
    (agree : ∀ atom < bound, first atom = second atom) :
    ClausesHoldBetween first next clauses ↔
      ClausesHoldBetween second next clauses := by
  constructor
  · intro holds clause clauseMem
    obtain ⟨literal, literalMem, literalHolds⟩ := holds clause clauseMem
    exact ⟨literal, literalMem,
      (literal_holdsBetween_congr_current
        (atoms clause clauseMem literal literalMem) agree).mp literalHolds⟩
  · intro holds clause clauseMem
    obtain ⟨literal, literalMem, literalHolds⟩ := holds clause clauseMem
    exact ⟨literal, literalMem,
      (literal_holdsBetween_congr_current
        (atoms clause clauseMem literal literalMem) agree).mpr literalHolds⟩

private theorem update_agrees_below (values : Nat → Bool)
    (position : Nat) (value : Bool) :
    ∀ atom < position,
      Function.update values position value atom = values atom := by
  intro atom atomLt
  simp [Function.update, Nat.ne_of_lt atomLt]

/-- The canonical auxiliary valuation satisfies the complete structural
Tseitin compilation. -/
theorem realizeTransitionExpr_holds (expression : TransitionExpr)
    (fresh : Nat) (current next : Nat → Bool)
    (sourceBound : expression.AtomsBelow fresh) :
    ClausesHoldBetween
      (realizeTransitionExpr expression fresh current next) next
      (compileTransitionExpr expression fresh).clauses := by
  induction expression generalizing fresh current with
  | constant value =>
      apply (constantClauses_hold_iff fresh value _ next).mpr
      simp [realizeTransitionExpr]
  | wire input =>
      apply (equalityClauses_hold_iff fresh input _ next).mpr
      have preserved : input.value
          (realizeTransitionExpr (.wire input) fresh current next) next =
          input.value current next := by
        apply TransitionExpr.eval_congr_current
          (expression := .wire input) sourceBound
        intro atom atomLt
        exact realizeTransitionExpr_preserves (.wire input)
          fresh current next atomLt
      simpa [realizeTransitionExpr] using preserved.symm
  | not input ih =>
      let compiled := compileTransitionExpr input fresh
      let inputRealized := realizeTransitionExpr input fresh current next
      let realized := Function.update inputRealized compiled.nextFresh
        (!(input.eval current next))
      have inputHolds := ih fresh current sourceBound
      have inputAtoms := compileTransitionExpr_atomsBelow input fresh sourceBound
      have inputStable : ClausesHoldBetween realized next compiled.clauses := by
        apply (clausesHoldBetween_congr_current inputAtoms
          (first := inputRealized) (second := realized) ?_).mp
        · simpa [inputRealized, compiled, realized] using inputHolds
        · intro atom atomLt
          exact (update_agrees_below inputRealized compiled.nextFresh
            (!(input.eval current next)) atom atomLt).symm
      have gateHolds : ClausesHoldBetween realized next
          (notClauses compiled.nextFresh (gateOutput compiled.root)) := by
        apply (notClauses_hold_iff compiled.nextFresh
          (gateOutput compiled.root) realized next).mpr
        have rootLt := compileTransitionExpr_root_lt_nextFresh input fresh
        have rootPreserved : realized compiled.root = inputRealized compiled.root := by
          simpa [realized] using
            update_agrees_below inputRealized compiled.nextFresh
              (!(input.eval current next)) compiled.root
              (by simpa [compiled] using rootLt)
        simp only [gateOutput_value]
        rw [rootPreserved]
        simp [realized, inputRealized, compiled, Function.update]
      apply (clausesHoldBetween_append_iff realized next
        compiled.clauses
        (notClauses compiled.nextFresh (gateOutput compiled.root))).mpr
      exact ⟨inputStable, gateHolds⟩
  | and first second firstIH secondIH =>
      let firstCompiled := compileTransitionExpr first fresh
      let firstRealized := realizeTransitionExpr first fresh current next
      let secondCompiled :=
        compileTransitionExpr second firstCompiled.nextFresh
      let secondRealized := realizeTransitionExpr second
        firstCompiled.nextFresh firstRealized next
      let realized := Function.update secondRealized secondCompiled.nextFresh
        (first.eval current next && second.eval current next)
      have freshLeFirst : fresh ≤ firstCompiled.nextFresh := by
        have firstNext := compileTransitionExpr_nextFresh first fresh
        simpa [firstCompiled] using Nat.le.intro firstNext.symm
      have secondSource := sourceBound.2.mono freshLeFirst
      have firstHolds := firstIH fresh current sourceBound.1
      have secondHolds := secondIH firstCompiled.nextFresh
        firstRealized secondSource
      have firstAtoms := compileTransitionExpr_atomsBelow first fresh sourceBound.1
      have secondAtoms := compileTransitionExpr_atomsBelow second
        firstCompiled.nextFresh secondSource
      have firstAtoms' : ClausesAtomsBelow firstCompiled.clauses
          firstCompiled.nextFresh := by
        simpa [firstCompiled] using firstAtoms
      have secondAtoms' : ClausesAtomsBelow secondCompiled.clauses
          secondCompiled.nextFresh := by
        simpa [secondCompiled] using secondAtoms
      have firstToSecond : firstCompiled.nextFresh ≤ secondCompiled.nextFresh := by
        have secondNext := compileTransitionExpr_nextFresh second
          firstCompiled.nextFresh
        simpa [secondCompiled] using Nat.le.intro secondNext.symm
      have firstStableSecond : ClausesHoldBetween secondRealized next
          firstCompiled.clauses := by
        apply (clausesHoldBetween_congr_current firstAtoms'
          (first := firstRealized) (second := secondRealized) ?_).mp
        · simpa [firstRealized, firstCompiled] using firstHolds
        · intro atom atomLt
          exact (realizeTransitionExpr_preserves second
            firstCompiled.nextFresh firstRealized next atomLt).symm
      have firstStable : ClausesHoldBetween realized next
          firstCompiled.clauses := by
        apply (clausesHoldBetween_congr_current firstAtoms'
          (first := secondRealized) (second := realized) ?_).mp
        · exact firstStableSecond
        · intro atom atomLt
          exact (update_agrees_below secondRealized secondCompiled.nextFresh
            (first.eval current next && second.eval current next) atom
            (lt_of_lt_of_le atomLt firstToSecond)).symm
      have secondStable : ClausesHoldBetween realized next
          secondCompiled.clauses := by
        apply (clausesHoldBetween_congr_current secondAtoms'
          (first := secondRealized) (second := realized) ?_).mp
        · simpa [secondRealized, secondCompiled] using secondHolds
        · intro atom atomLt
          exact (update_agrees_below secondRealized secondCompiled.nextFresh
            (first.eval current next && second.eval current next)
            atom atomLt).symm
      have gateHolds : ClausesHoldBetween realized next
          (andClauses secondCompiled.nextFresh
            (gateOutput firstCompiled.root)
            (gateOutput secondCompiled.root)) := by
        apply (andClauses_hold_iff secondCompiled.nextFresh
          (gateOutput firstCompiled.root) (gateOutput secondCompiled.root)
          realized next).mpr
        have firstRootLt := compileTransitionExpr_root_lt_nextFresh first fresh
        have secondRootLt := compileTransitionExpr_root_lt_nextFresh second
          firstCompiled.nextFresh
        have firstRootLt' : firstCompiled.root <
            firstCompiled.nextFresh := firstRootLt
        have secondRootLt' : secondCompiled.root <
            secondCompiled.nextFresh := secondRootLt
        have finalPreserves : ∀ atom < secondCompiled.nextFresh,
            realized atom = secondRealized atom := by
          intro atom atomLt
          simpa [realized] using
            update_agrees_below secondRealized secondCompiled.nextFresh
              (first.eval current next && second.eval current next)
              atom atomLt
        have firstRootValue : realized firstCompiled.root =
            first.eval current next := by
          rw [finalPreserves firstCompiled.root (by omega)]
          have secondPreservesFirstRoot :
              secondRealized firstCompiled.root =
                firstRealized firstCompiled.root := by
            dsimp [secondRealized]
            exact realizeTransitionExpr_preserves second
              firstCompiled.nextFresh firstRealized next firstRootLt'
          rw [secondPreservesFirstRoot]
          simpa [firstRealized, firstCompiled] using
            realizeTransitionExpr_root first fresh current next
        have secondEval : second.eval firstRealized next =
            second.eval current next := by
          apply TransitionExpr.eval_congr_current sourceBound.2
          intro atom atomLt
          exact realizeTransitionExpr_preserves first fresh current next atomLt
        have secondRootValue : realized secondCompiled.root =
            second.eval current next := by
          rw [finalPreserves secondCompiled.root secondRootLt']
          have secondRootCanonical :
              secondRealized secondCompiled.root =
                second.eval firstRealized next := by
            simpa [secondRealized, secondCompiled] using
              realizeTransitionExpr_root second firstCompiled.nextFresh
                firstRealized next
          rw [secondRootCanonical, secondEval]
        simp only [gateOutput_value, firstRootValue, secondRootValue]
        simp [realized, Function.update]
      apply (clausesHoldBetween_append_iff realized next
        (firstCompiled.clauses ++ secondCompiled.clauses)
        (andClauses secondCompiled.nextFresh
          (gateOutput firstCompiled.root)
          (gateOutput secondCompiled.root))).mpr
      exact ⟨(clausesHoldBetween_append_iff realized next
        firstCompiled.clauses secondCompiled.clauses).mpr
          ⟨firstStable, secondStable⟩, gateHolds⟩
  | or first second firstIH secondIH =>
      let firstCompiled := compileTransitionExpr first fresh
      let firstRealized := realizeTransitionExpr first fresh current next
      let secondCompiled :=
        compileTransitionExpr second firstCompiled.nextFresh
      let secondRealized := realizeTransitionExpr second
        firstCompiled.nextFresh firstRealized next
      let realized := Function.update secondRealized secondCompiled.nextFresh
        (first.eval current next || second.eval current next)
      have freshLeFirst : fresh ≤ firstCompiled.nextFresh := by
        have firstNext := compileTransitionExpr_nextFresh first fresh
        simpa [firstCompiled] using Nat.le.intro firstNext.symm
      have secondSource := sourceBound.2.mono freshLeFirst
      have firstHolds := firstIH fresh current sourceBound.1
      have secondHolds := secondIH firstCompiled.nextFresh
        firstRealized secondSource
      have firstAtoms := compileTransitionExpr_atomsBelow first fresh sourceBound.1
      have secondAtoms := compileTransitionExpr_atomsBelow second
        firstCompiled.nextFresh secondSource
      have firstAtoms' : ClausesAtomsBelow firstCompiled.clauses
          firstCompiled.nextFresh := by
        simpa [firstCompiled] using firstAtoms
      have secondAtoms' : ClausesAtomsBelow secondCompiled.clauses
          secondCompiled.nextFresh := by
        simpa [secondCompiled] using secondAtoms
      have firstToSecond : firstCompiled.nextFresh ≤ secondCompiled.nextFresh := by
        have secondNext := compileTransitionExpr_nextFresh second
          firstCompiled.nextFresh
        simpa [secondCompiled] using Nat.le.intro secondNext.symm
      have firstStableSecond : ClausesHoldBetween secondRealized next
          firstCompiled.clauses := by
        apply (clausesHoldBetween_congr_current firstAtoms'
          (first := firstRealized) (second := secondRealized) ?_).mp
        · simpa [firstRealized, firstCompiled] using firstHolds
        · intro atom atomLt
          exact (realizeTransitionExpr_preserves second
            firstCompiled.nextFresh firstRealized next atomLt).symm
      have firstStable : ClausesHoldBetween realized next
          firstCompiled.clauses := by
        apply (clausesHoldBetween_congr_current firstAtoms'
          (first := secondRealized) (second := realized) ?_).mp
        · exact firstStableSecond
        · intro atom atomLt
          exact (update_agrees_below secondRealized secondCompiled.nextFresh
            (first.eval current next || second.eval current next) atom
            (lt_of_lt_of_le atomLt firstToSecond)).symm
      have secondStable : ClausesHoldBetween realized next
          secondCompiled.clauses := by
        apply (clausesHoldBetween_congr_current secondAtoms'
          (first := secondRealized) (second := realized) ?_).mp
        · simpa [secondRealized, secondCompiled] using secondHolds
        · intro atom atomLt
          exact (update_agrees_below secondRealized secondCompiled.nextFresh
            (first.eval current next || second.eval current next)
            atom atomLt).symm
      have gateHolds : ClausesHoldBetween realized next
          (orClauses secondCompiled.nextFresh
            (gateOutput firstCompiled.root)
            (gateOutput secondCompiled.root)) := by
        apply (orClauses_hold_iff secondCompiled.nextFresh
          (gateOutput firstCompiled.root) (gateOutput secondCompiled.root)
          realized next).mpr
        have firstRootLt := compileTransitionExpr_root_lt_nextFresh first fresh
        have secondRootLt := compileTransitionExpr_root_lt_nextFresh second
          firstCompiled.nextFresh
        have firstRootLt' : firstCompiled.root <
            firstCompiled.nextFresh := firstRootLt
        have secondRootLt' : secondCompiled.root <
            secondCompiled.nextFresh := secondRootLt
        have finalPreserves : ∀ atom < secondCompiled.nextFresh,
            realized atom = secondRealized atom := by
          intro atom atomLt
          simpa [realized] using
            update_agrees_below secondRealized secondCompiled.nextFresh
              (first.eval current next || second.eval current next)
              atom atomLt
        have firstRootValue : realized firstCompiled.root =
            first.eval current next := by
          rw [finalPreserves firstCompiled.root (by omega)]
          have secondPreservesFirstRoot :
              secondRealized firstCompiled.root =
                firstRealized firstCompiled.root := by
            dsimp [secondRealized]
            exact realizeTransitionExpr_preserves second
              firstCompiled.nextFresh firstRealized next firstRootLt'
          rw [secondPreservesFirstRoot]
          simpa [firstRealized, firstCompiled] using
            realizeTransitionExpr_root first fresh current next
        have secondEval : second.eval firstRealized next =
            second.eval current next := by
          apply TransitionExpr.eval_congr_current sourceBound.2
          intro atom atomLt
          exact realizeTransitionExpr_preserves first fresh current next atomLt
        have secondRootValue : realized secondCompiled.root =
            second.eval current next := by
          rw [finalPreserves secondCompiled.root secondRootLt']
          have secondRootCanonical :
              secondRealized secondCompiled.root =
                second.eval firstRealized next := by
            simpa [secondRealized, secondCompiled] using
              realizeTransitionExpr_root second firstCompiled.nextFresh
                firstRealized next
          rw [secondRootCanonical, secondEval]
        simp only [gateOutput_value, firstRootValue, secondRootValue]
        simp [realized, Function.update]
      apply (clausesHoldBetween_append_iff realized next
        (firstCompiled.clauses ++ secondCompiled.clauses)
        (orClauses secondCompiled.nextFresh
          (gateOutput firstCompiled.root)
          (gateOutput secondCompiled.root))).mpr
      exact ⟨(clausesHoldBetween_append_iff realized next
        firstCompiled.clauses secondCompiled.clauses).mpr
          ⟨firstStable, secondStable⟩, gateHolds⟩

/-- Constructive semantic completeness of transition-expression compilation. -/
theorem compileTransitionExpr_complete (expression : TransitionExpr)
    (fresh : Nat) (current next : Nat → Bool)
    (sourceBound : expression.AtomsBelow fresh) :
    ∃ realized : Nat → Bool,
      (∀ atom < fresh, realized atom = current atom) ∧
      ClausesHoldBetween realized next
        (compileTransitionExpr expression fresh).clauses ∧
      realized (compileTransitionExpr expression fresh).root =
        expression.eval current next := by
  exact ⟨realizeTransitionExpr expression fresh current next,
    fun _ atomLt => realizeTransitionExpr_preserves
      expression fresh current next atomLt,
    realizeTransitionExpr_holds expression fresh current next sourceBound,
    realizeTransitionExpr_root expression fresh current next⟩

end PeriodicCNF

end LeanTrominoes
