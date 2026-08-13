/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFOneDimensional
import LeanTrominoes.FiniteState

/-!
# Periodic CNF as a transition system

A forward-local periodic formula reads each Boolean atom either at the current
integer position or at the next one.  Such a formula is precisely a finite CNF
presentation of a time-homogeneous transition relation on Boolean states.
This file proves that satisfying line assignments are exactly bi-infinite
paths through that relation.
-/

namespace LeanTrominoes

namespace PeriodicLiteral

/-- A literal is forward-local when it reads the current or next horizontal
slice and has no vertical displacement. -/
def IsForwardLocal {Variable : Type*}
    (literal : PeriodicLiteral Variable) : Prop :=
  literal.offset = (0, 0) ∨ literal.offset = (1, 0)

/-- Whether a literal holds between two consecutive Boolean states. -/
def HoldsBetween {Variable : Type*}
    (current next : Variable → Bool)
    (literal : PeriodicLiteral Variable) : Prop :=
  (literal.offset = (0, 0) ∧
      current literal.atom = literal.value) ∨
    (literal.offset = (1, 0) ∧
      next literal.atom = literal.value)

/-- For a forward-local literal, line evaluation at `translate` is evaluation
between the states at `translate` and `translate + 1`. -/
theorem holdsOnLine_iff_holdsBetween {Variable : Type*}
    (assignment : Variable → Int → Bool) (translate : Int)
    (literal : PeriodicLiteral Variable)
    (forward : literal.IsForwardLocal) :
    literal.HoldsOnLine assignment translate ↔
      literal.HoldsBetween
        (fun atom => assignment atom translate)
        (fun atom => assignment atom (translate + 1)) := by
  rcases forward with current | next
  · simp [HoldsOnLine, HoldsBetween, current]
  · simp [HoldsOnLine, HoldsBetween, next]

end PeriodicLiteral

namespace PeriodicClause

/-- Whether one clause is satisfied between two consecutive Boolean states. -/
def HoldsBetween {Variable : Type*}
    (current next : Variable → Bool)
    (clause : PeriodicClause Variable) : Prop :=
  ∃ literal ∈ clause, literal.HoldsBetween current next

/-- Clause-level correspondence between line and transition semantics. -/
theorem holdsOnLine_iff_holdsBetween {Variable : Type*}
    (assignment : Variable → Int → Bool) (translate : Int)
    (clause : PeriodicClause Variable)
    (forward : ∀ literal ∈ clause, literal.IsForwardLocal) :
    clause.HoldsOnLine assignment translate ↔
      clause.HoldsBetween
        (fun atom => assignment atom translate)
        (fun atom => assignment atom (translate + 1)) := by
  constructor
  · rintro ⟨literal, literalMem, holds⟩
    exact ⟨literal, literalMem,
      (PeriodicLiteral.holdsOnLine_iff_holdsBetween
        assignment translate literal (forward literal literalMem)).mp holds⟩
  · rintro ⟨literal, literalMem, holds⟩
    exact ⟨literal, literalMem,
      (PeriodicLiteral.holdsOnLine_iff_holdsBetween
        assignment translate literal (forward literal literalMem)).mpr holds⟩

end PeriodicClause

namespace PeriodicCNF

/-- Every literal in a forward-local formula reads the current or next
horizontal slice. -/
def IsForwardLocal {Variable : Type*}
    (formula : PeriodicCNF Variable) : Prop :=
  ∀ clause ∈ formula.clauses, ∀ literal ∈ clause,
    literal.IsForwardLocal

/-- A forward-local formula is one-dimensional. -/
theorem isOneDimensional_of_isForwardLocal {Variable : Type*}
    {formula : PeriodicCNF Variable}
    (forward : formula.IsForwardLocal) :
    formula.IsOneDimensional := by
  intro clause clauseMem literal literalMem
  rcases forward clause clauseMem literal literalMem with current | next
  · simp [current]
  · simp [next]

/-- A forward-local formula is local on the line. -/
theorem isLocalOnLine_of_isForwardLocal {Variable : Type*}
    {formula : PeriodicCNF Variable}
    (forward : formula.IsForwardLocal) :
    formula.IsLocalOnLine := by
  intro clause clauseMem first firstMem second secondMem
  rcases forward clause clauseMem first firstMem with firstOffset | firstOffset <;>
    rcases forward clause clauseMem second secondMem with
      secondOffset | secondOffset <;>
    simp [PeriodicClause.offsetDistanceOnLine,
      firstOffset, secondOffset]

/-- The Boolean-state transition relation presented by a forward-local CNF
formula. -/
def Transition {Variable : Type*}
    (formula : PeriodicCNF Variable)
    (current next : Variable → Bool) : Prop :=
  ∀ clause ∈ formula.clauses, clause.HoldsBetween current next

/-- A satisfying line assignment produces a bi-infinite path through the
presented transition relation. -/
theorem hasBiInfinitePath_of_satisfiableOnLine {Variable : Type*}
    {formula : PeriodicCNF Variable}
    (forward : formula.IsForwardLocal)
    (satisfiable : formula.SatisfiableOnLine) :
    FiniteState.HasBiInfinitePath formula.Transition := by
  obtain ⟨assignment, satisfies⟩ := satisfiable
  refine ⟨fun translate atom => assignment atom translate, ?_⟩
  intro translate clause clauseMem
  apply (PeriodicClause.holdsOnLine_iff_holdsBetween
    assignment translate clause (forward clause clauseMem)).mp
  exact satisfies translate clause clauseMem

/-- A bi-infinite path through the presented transition relation produces a
satisfying line assignment. -/
theorem satisfiableOnLine_of_hasBiInfinitePath {Variable : Type*}
    {formula : PeriodicCNF Variable}
    (forward : formula.IsForwardLocal)
    (path : FiniteState.HasBiInfinitePath formula.Transition) :
    formula.SatisfiableOnLine := by
  obtain ⟨states, follows⟩ := path
  refine ⟨fun atom translate => states translate atom, ?_⟩
  intro translate clause clauseMem
  apply (PeriodicClause.holdsOnLine_iff_holdsBetween
    (fun atom translate => states translate atom)
    translate clause (forward clause clauseMem)).mpr
  exact follows translate clause clauseMem

/-- Forward-local periodic CNF models are exactly bi-infinite paths through
the induced Boolean transition relation. -/
theorem satisfiableOnLine_iff_hasBiInfinitePath {Variable : Type*}
    {formula : PeriodicCNF Variable}
    (forward : formula.IsForwardLocal) :
    formula.SatisfiableOnLine ↔
      FiniteState.HasBiInfinitePath formula.Transition :=
  ⟨hasBiInfinitePath_of_satisfiableOnLine forward,
    satisfiableOnLine_of_hasBiInfinitePath forward⟩

end PeriodicCNF

end LeanTrominoes
