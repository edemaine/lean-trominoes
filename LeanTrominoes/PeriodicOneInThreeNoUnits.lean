/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOneInThreeCorrectness

/-!
# Eliminating unit clauses from periodic exact-one SAT

The paired-port 3DM clause gadget naturally handles clauses of arity two or
three, because its shared colored elements must have degree two or three.
Figure 9 also emits unit clauses to force padding variables false.  This file
removes that last mismatch.

A unit exact-one clause `[ℓ]` is replaced by

* `[¬ℓ, a, b]`, and
* `[a, b]`.

The second clause says exactly one of `a,b` is true, so the first holds exactly
when `¬ℓ` is false, equivalently when the original unit literal is true.  An
empty source clause is replaced by the unsatisfiable triangle
`[a,b], [b,c], [a,c]`.  All other clauses are merely embedded.
-/

namespace LeanTrominoes

/-- Clause-local variables introduced while removing exact-one unit clauses. -/
inductive OneInThreeNoUnitAux
  | first
  | second
  | third
  deriving DecidableEq, Repr, Fintype

/-- Original exact-one variables or auxiliaries scoped to one protoclauses. -/
abbrev OneInThreeNoUnitVariable (Variable : Type*) :=
  Sum Variable
    ((Nat × PeriodicClause Variable) × OneInThreeNoUnitAux)

namespace PeriodicOneInThreeNoUnits

/-- Embed an original literal into the unit-free variable type. -/
def liftLiteral {Variable : Type*}
    (literal : PeriodicLiteral Variable) :
    PeriodicLiteral (OneInThreeNoUnitVariable Variable) :=
  ⟨Sum.inl literal.atom, literal.offset, literal.value⟩

/-- A positive auxiliary literal at the source clause's anchor. -/
def auxiliary {Variable : Type*} (clauseIndex : Nat)
    (source : PeriodicClause Variable) (kind : OneInThreeNoUnitAux) :
    PeriodicLiteral (OneInThreeNoUnitVariable Variable) :=
  ⟨Sum.inr ((clauseIndex, source), kind),
    PeriodicOneInThree.anchor source, true⟩

/-- Replace one exact-one clause by clauses of arity two or three. -/
def clauseClauses {Variable : Type*} (clauseIndex : Nat)
    (source : PeriodicClause Variable) :
    List (PeriodicClause (OneInThreeNoUnitVariable Variable)) :=
  match source with
  | [] =>
      [[auxiliary clauseIndex source .first,
          auxiliary clauseIndex source .second],
        [auxiliary clauseIndex source .second,
          auxiliary clauseIndex source .third],
        [auxiliary clauseIndex source .first,
          auxiliary clauseIndex source .third]]
  | [literal] =>
      [[PeriodicOneInThree.negate (liftLiteral literal),
          auxiliary clauseIndex source .first,
          auxiliary clauseIndex source .second],
        [auxiliary clauseIndex source .first,
          auxiliary clauseIndex source .second]]
  | first :: second :: rest =>
      [(first :: second :: rest).map liftLiteral]

/-- Every clause in one unit-elimination block retains the source clause's
periodic anchor. -/
theorem clauseAnchor_eq_of_mem_clauseClauses
    {Variable : Type*} (clauseIndex : Nat)
    (source : PeriodicClause Variable)
    (generated :
      PeriodicClause (OneInThreeNoUnitVariable Variable))
    (generatedMember :
      generated ∈ clauseClauses clauseIndex source) :
    PeriodicOneInThree.anchor generated =
      PeriodicOneInThree.anchor source := by
  cases source with
  | nil =>
      simp [clauseClauses,
        auxiliary, PeriodicOneInThree.anchor] at generatedMember ⊢
      rcases generatedMember with rfl | rfl | rfl <;> rfl
  | cons first rest =>
      cases rest with
      | nil =>
          simp [clauseClauses,
            auxiliary, PeriodicOneInThree.anchor,
            liftLiteral] at generatedMember ⊢
          rcases generatedMember with rfl | rfl <;> rfl
      | cons second tail =>
          simp [clauseClauses, PeriodicOneInThree.anchor,
            liftLiteral] at generatedMember ⊢
          subst generated
          rfl

/-- Eliminate every unit clause in a finite periodic presentation. -/
def formula {Variable : Type*} (source : PeriodicCNF Variable) :
    PeriodicCNF (OneInThreeNoUnitVariable Variable) where
  clauses := source.clauses.zipIdx.flatMap fun tagged =>
    clauseClauses tagged.2 tagged.1

/-- The two-clause Boolean kernel used for a source unit literal. -/
def UnitGadgetHolds (literal first second : Bool) : Prop :=
  PeriodicOneInThree.ExactlyOne [!literal, first, second] ∧
    PeriodicOneInThree.ExactlyOne [first, second]

instance (literal first second : Bool) :
    Decidable (UnitGadgetHolds literal first second) := by
  unfold UnitGadgetHolds
  infer_instance

/-- The replacement for a unit clause has an extension exactly when that
literal is true. -/
theorem exists_unitGadgetHolds_iff (literal : Bool) :
    (∃ first second, UnitGadgetHolds literal first second) ↔
      literal = true := by
  cases literal <;> native_decide

/-- Any completion of the unit gadget recovers the source literal. -/
theorem unitGadgetHolds_literal_true
    {literal first second : Bool}
    (holds : UnitGadgetHolds literal first second) :
    literal = true := by
  exact (exists_unitGadgetHolds_iff literal).mp
    ⟨first, second, holds⟩

/-- The three binary clauses replacing an empty exact-one clause are
inconsistent. -/
theorem emptyTriangle_impossible (first second third : Bool) :
    ¬(PeriodicOneInThree.ExactlyOne [first, second] ∧
      PeriodicOneInThree.ExactlyOne [second, third] ∧
      PeriodicOneInThree.ExactlyOne [first, third]) := by
  cases first <;> cases second <;> cases third <;> native_decide

/-- A fixed completion used for every satisfiable unit gadget. -/
def extendAssignment {Variable : Type*}
    (assignment : Variable → Cell → Bool) :
    OneInThreeNoUnitVariable Variable → Cell → Bool
  | Sum.inl atom, cell => assignment atom cell
  | Sum.inr (_, .first), _cell => true
  | Sum.inr (_, .second), _cell => false
  | Sum.inr (_, .third), _cell => false

/-- Forget all clause-local auxiliaries. -/
def restrictAssignment {Variable : Type*}
    (assignment :
      OneInThreeNoUnitVariable Variable → Cell → Bool) :
    Variable → Cell → Bool :=
  fun atom cell => assignment (Sum.inl atom) cell

@[simp]
theorem restrict_extendAssignment {Variable : Type*}
    (assignment : Variable → Cell → Bool) :
    restrictAssignment (extendAssignment assignment) = assignment := by
  rfl

@[simp]
theorem literalTruth_lift_extend {Variable : Type*}
    (assignment : Variable → Cell → Bool) (translate : Cell)
    (literal : PeriodicLiteral Variable) :
    PeriodicOneInThree.literalTruth
        (extendAssignment assignment) translate
        (liftLiteral literal) =
      PeriodicOneInThree.literalTruth assignment translate literal := by
  rfl

@[simp]
theorem literalTruth_lift_restrict {Variable : Type*}
    (assignment :
      OneInThreeNoUnitVariable Variable → Cell → Bool)
    (translate : Cell) (literal : PeriodicLiteral Variable) :
    PeriodicOneInThree.literalTruth assignment translate
        (liftLiteral literal) =
      PeriodicOneInThree.literalTruth
        (restrictAssignment assignment) translate literal := by
  rfl

@[simp]
theorem literalTruth_auxiliary_extend {Variable : Type*}
    (assignment : Variable → Cell → Bool) (translate : Cell)
    (clauseIndex : Nat) (source : PeriodicClause Variable)
    (kind : OneInThreeNoUnitAux) :
    PeriodicOneInThree.literalTruth
        (extendAssignment assignment) translate
        (auxiliary clauseIndex source kind) =
      match kind with
      | .first => true
      | .second => false
      | .third => false := by
  cases kind <;> simp [PeriodicOneInThree.literalTruth,
    auxiliary, extendAssignment]

/-- Clause values are the mapped literal-truth values. -/
theorem clauseValues_eq_map_literalTruth {Variable : Type*}
    (assignment : Variable → Cell → Bool) (translate : Cell)
    (clause : PeriodicClause Variable) :
    PeriodicOneInThree.clauseValues assignment translate clause =
      clause.map
        (PeriodicOneInThree.literalTruth assignment translate) := by
  rfl

/-- Embedded clauses retain their complete exact-one truth-value list. -/
@[simp]
theorem clauseValues_map_lift_extend {Variable : Type*}
    (assignment : Variable → Cell → Bool) (translate : Cell)
    (clause : PeriodicClause Variable) :
    PeriodicOneInThree.clauseValues
        (extendAssignment assignment) translate
        (clause.map liftLiteral) =
      PeriodicOneInThree.clauseValues assignment translate clause := by
  simp [clauseValues_eq_map_literalTruth]

/-- Restriction likewise preserves every embedded clause value. -/
@[simp]
theorem clauseValues_map_lift_restrict {Variable : Type*}
    (assignment :
      OneInThreeNoUnitVariable Variable → Cell → Bool)
    (translate : Cell) (clause : PeriodicClause Variable) :
    PeriodicOneInThree.clauseValues assignment translate
        (clause.map liftLiteral) =
      PeriodicOneInThree.clauseValues
        (restrictAssignment assignment) translate clause := by
  simp [clauseValues_eq_map_literalTruth]

/-- A satisfying source clause satisfies every one of its generated
unit-free clauses under the canonical extension. -/
theorem clauseClauses_complete {Variable : Type*}
    (assignment : Variable → Cell → Bool) (translate : Cell)
    (clauseIndex : Nat) (source : PeriodicClause Variable)
    (sourceHolds :
      PeriodicOneInThree.ClauseHolds assignment translate source) :
    ∀ generated ∈ clauseClauses clauseIndex source,
      PeriodicOneInThree.ClauseHolds
        (extendAssignment assignment) translate generated := by
  intro generated generatedMem
  rcases source with _ | ⟨literal, rest⟩
  · simp [PeriodicOneInThree.ClauseHolds,
      PeriodicOneInThree.clauseValues,
      PeriodicOneInThree.ExactlyOne] at sourceHolds
  · cases rest with
    | nil =>
        simp only [clauseClauses, List.mem_cons,
          List.not_mem_nil, or_false] at generatedMem
        rcases generatedMem with rfl | rfl
        · have literalTrue :
              PeriodicOneInThree.literalTruth
                  assignment translate literal = true := by
            unfold PeriodicOneInThree.ClauseHolds at sourceHolds
            rw [clauseValues_eq_map_literalTruth] at sourceHolds
            change PeriodicOneInThree.ExactlyOne
              [PeriodicOneInThree.literalTruth
                assignment translate literal] at sourceHolds
            cases truthEq :
                PeriodicOneInThree.literalTruth
                  assignment translate literal with
            | false =>
                have falseH :
                    PeriodicOneInThree.ExactlyOne [false] := by
                  simpa only [truthEq] using sourceHolds
                exact ((by native_decide :
                  ¬PeriodicOneInThree.ExactlyOne [false])
                    falseH).elim
            | true => rfl
          simp [PeriodicOneInThree.ClauseHolds,
            clauseValues_eq_map_literalTruth, literalTrue,
            PeriodicOneInThree.literalTruth_negate] ;
            native_decide
        · simp [PeriodicOneInThree.ClauseHolds,
            clauseValues_eq_map_literalTruth] ;
            native_decide
    | cons second rest =>
        simp only [clauseClauses, List.mem_singleton] at generatedMem
        subst generated
        unfold PeriodicOneInThree.ClauseHolds at sourceHolds ⊢
        rw [clauseValues_map_lift_extend]
        exact sourceHolds

/-- Satisfying all generated clauses recovers the source exact-one clause. -/
theorem clauseClauses_sound {Variable : Type*}
    (assignment :
      OneInThreeNoUnitVariable Variable → Cell → Bool)
    (translate : Cell) (clauseIndex : Nat)
    (source : PeriodicClause Variable)
    (generatedHolds :
      ∀ generated ∈ clauseClauses clauseIndex source,
        PeriodicOneInThree.ClauseHolds assignment translate generated) :
    PeriodicOneInThree.ClauseHolds
      (restrictAssignment assignment) translate source := by
  rcases source with _ | ⟨literal, rest⟩
  · have first :=
      generatedHolds
        [auxiliary clauseIndex [] .first,
          auxiliary clauseIndex [] .second] (by simp [clauseClauses])
    have second :=
      generatedHolds
        [auxiliary clauseIndex [] .second,
          auxiliary clauseIndex [] .third] (by simp [clauseClauses])
    have third :=
      generatedHolds
        [auxiliary clauseIndex [] .first,
          auxiliary clauseIndex [] .third] (by simp [clauseClauses])
    have impossible := emptyTriangle_impossible
      (PeriodicOneInThree.literalTruth assignment translate
        (auxiliary clauseIndex [] .first))
      (PeriodicOneInThree.literalTruth assignment translate
        (auxiliary clauseIndex [] .second))
      (PeriodicOneInThree.literalTruth assignment translate
        (auxiliary clauseIndex [] .third))
    exfalso
    apply impossible
    simpa [PeriodicOneInThree.ClauseHolds,
      clauseValues_eq_map_literalTruth] using And.intro first
        (And.intro second third)
  · cases rest with
    | nil =>
        have firstClause :=
          generatedHolds
            [PeriodicOneInThree.negate (liftLiteral literal),
              auxiliary clauseIndex [literal] .first,
              auxiliary clauseIndex [literal] .second]
            (by simp [clauseClauses])
        have secondClause :=
          generatedHolds
            [auxiliary clauseIndex [literal] .first,
              auxiliary clauseIndex [literal] .second]
            (by simp [clauseClauses])
        let literalValue :=
          PeriodicOneInThree.literalTruth
            (restrictAssignment assignment) translate literal
        let firstValue :=
          PeriodicOneInThree.literalTruth assignment translate
            (auxiliary clauseIndex [literal] .first)
        let secondValue :=
          PeriodicOneInThree.literalTruth assignment translate
            (auxiliary clauseIndex [literal] .second)
        have gadget :
            UnitGadgetHolds literalValue firstValue secondValue := by
          constructor
          · simpa [PeriodicOneInThree.ClauseHolds,
              clauseValues_eq_map_literalTruth, literalValue,
              firstValue, secondValue,
              PeriodicOneInThree.literalTruth_negate] using firstClause
          · simpa [PeriodicOneInThree.ClauseHolds,
              clauseValues_eq_map_literalTruth, firstValue,
              secondValue] using secondClause
        have literalTrue :=
          unitGadgetHolds_literal_true gadget
        unfold PeriodicOneInThree.ClauseHolds
        rw [clauseValues_eq_map_literalTruth]
        change PeriodicOneInThree.ExactlyOne [literalValue]
        rw [literalTrue]
        native_decide
    | cons second rest =>
        have embedded :=
          generatedHolds
            ((literal :: second :: rest).map liftLiteral)
            (by simp [clauseClauses])
        unfold PeriodicOneInThree.ClauseHolds at embedded ⊢
        rw [clauseValues_map_lift_restrict] at embedded
        exact embedded

/-- Canonical extension satisfies the complete unit-free formula. -/
theorem formula_satisfies_of_satisfies {Variable : Type*}
    (source : PeriodicCNF Variable)
    (assignment : Variable → Cell → Bool)
    (satisfies : PeriodicOneInThree.Satisfies source assignment) :
    PeriodicOneInThree.Satisfies
      (formula source) (extendAssignment assignment) := by
  intro translate generated generatedMem
  simp only [formula, List.mem_flatMap] at generatedMem
  rcases generatedMem with ⟨tagged, taggedMem, generatedMem⟩
  exact clauseClauses_complete assignment translate tagged.2 tagged.1
    (satisfies translate tagged.1
      (List.fst_mem_of_mem_zipIdx taggedMem))
    generated generatedMem

/-- Restricting any unit-free solution satisfies the source formula. -/
theorem satisfies_of_formula_satisfies {Variable : Type*}
    (source : PeriodicCNF Variable)
    (assignment :
      OneInThreeNoUnitVariable Variable → Cell → Bool)
    (satisfies :
      PeriodicOneInThree.Satisfies (formula source) assignment) :
    PeriodicOneInThree.Satisfies source
      (restrictAssignment assignment) := by
  intro translate clause clauseMem
  have mappedMem :
      clause ∈ source.clauses.zipIdx.map Prod.fst := by
    simpa only [List.zipIdx_map_fst] using clauseMem
  rcases List.mem_map.mp mappedMem with
    ⟨⟨taggedClause, clauseIndex⟩, taggedMem, taggedEq⟩
  simp only at taggedEq
  subst taggedClause
  apply clauseClauses_sound assignment translate clauseIndex clause
  intro generated generatedMem
  apply satisfies translate generated
  simp only [formula, List.mem_flatMap]
  exact ⟨(clause, clauseIndex), taggedMem, generatedMem⟩

/-- Unit elimination preserves periodic exact-one satisfiability exactly. -/
theorem satisfiable_iff {Variable : Type*}
    (source : PeriodicCNF Variable) :
    PeriodicOneInThree.Satisfiable (formula source) ↔
      PeriodicOneInThree.Satisfiable source := by
  constructor
  · rintro ⟨assignment, satisfies⟩
    exact ⟨restrictAssignment assignment,
      satisfies_of_formula_satisfies source assignment satisfies⟩
  · rintro ⟨assignment, satisfies⟩
    exact ⟨extendAssignment assignment,
      formula_satisfies_of_satisfies source assignment satisfies⟩

/-- Embedding literals does not change their offset distance. -/
theorem liftLiteral_offsetDistance {Variable : Type*}
    (first second : PeriodicLiteral Variable) :
    PeriodicClause.offsetDistance
        (liftLiteral first) (liftLiteral second) =
      PeriodicClause.offsetDistance first second := by
  rfl

/-- Mapping the embedding over a local clause preserves locality. -/
theorem map_liftLiteral_isLocal {Variable : Type*}
    {source : PeriodicClause Variable} (sourceLocal : source.IsLocal) :
    PeriodicClause.IsLocal (source.map liftLiteral) := by
  intro first firstMem second secondMem
  simp only [List.mem_map] at firstMem secondMem
  rcases firstMem with ⟨sourceFirst, sourceFirstMem, rfl⟩
  rcases secondMem with ⟨sourceSecond, sourceSecondMem, rfl⟩
  rw [liftLiteral_offsetDistance]
  exact sourceLocal sourceFirst sourceFirstMem sourceSecond sourceSecondMem

/-- Every clause in one unit-elimination gadget remains local. -/
theorem clauseClauses_areLocal {Variable : Type*}
    (clauseIndex : Nat) {source : PeriodicClause Variable}
    (sourceLocal : source.IsLocal) :
    ∀ generated ∈ clauseClauses clauseIndex source,
      generated.IsLocal := by
  intro generated generatedMem
  rcases source with _ | ⟨first, rest⟩
  · simp [clauseClauses] at generatedMem
    rcases generatedMem with rfl | rfl | rfl <;>
      simp [PeriodicClause.IsLocal,
        PeriodicClause.offsetDistance, auxiliary,
        PeriodicOneInThree.anchor]
  · cases rest with
    | nil =>
        simp [clauseClauses] at generatedMem
        rcases generatedMem with rfl | rfl <;>
          simp [PeriodicClause.IsLocal,
            PeriodicClause.offsetDistance, auxiliary,
            liftLiteral, PeriodicOneInThree.negate,
            PeriodicOneInThree.anchor]
    | cons second rest =>
        simp only [clauseClauses, List.mem_singleton] at generatedMem
        subst generated
        exact map_liftLiteral_isLocal sourceLocal

/-- Unit elimination preserves the paper's locality condition. -/
theorem formula_isLocal {Variable : Type*}
    {source : PeriodicCNF Variable} (sourceLocal : source.IsLocal) :
    (formula source).IsLocal := by
  intro generated generatedMem
  simp only [formula, List.mem_flatMap] at generatedMem
  rcases generatedMem with ⟨tagged, taggedMem, generatedMem⟩
  exact clauseClauses_areLocal tagged.2
    (sourceLocal tagged.1 (List.fst_mem_of_mem_zipIdx taggedMem))
    generated generatedMem

/-- Every clause has one of the two arities accepted by the 3DM gadget. -/
def ArityTwoOrThree {Variable : Type*}
    (source : PeriodicCNF Variable) : Prop :=
  ∀ clause ∈ source.clauses,
    clause.length = 2 ∨ clause.length = 3

/-- One source clause of width at most three produces only clauses of arity
two or three. -/
theorem clauseClauses_arityTwoOrThree {Variable : Type*}
    (clauseIndex : Nat) (source : PeriodicClause Variable)
    (width : source.WidthAtMost 3) :
    ∀ generated ∈ clauseClauses clauseIndex source,
      generated.length = 2 ∨ generated.length = 3 := by
  intro generated generatedMem
  rcases source with _ | ⟨first, rest⟩
  · simp [clauseClauses] at generatedMem
    rcases generatedMem with rfl | rfl | rfl <;> simp
  · cases rest with
    | nil =>
        simp [clauseClauses] at generatedMem
        rcases generatedMem with rfl | rfl <;> simp
    | cons second rest =>
        simp only [clauseClauses, List.mem_singleton] at generatedMem
        subst generated
        simp only [List.length_map, List.length_cons]
        simp [PeriodicClause.WidthAtMost] at width
        omega

/-- Width-three input becomes an exact-one formula with no empty or unit
clauses. -/
theorem formula_arityTwoOrThree {Variable : Type*}
    (source : PeriodicCNF Variable) (width : source.WidthAtMost 3) :
    ArityTwoOrThree (formula source) := by
  intro generated generatedMem
  simp only [formula, List.mem_flatMap] at generatedMem
  rcases generatedMem with ⟨tagged, taggedMem, generatedMem⟩
  exact clauseClauses_arityTwoOrThree tagged.2 tagged.1
    (width tagged.1 (List.fst_mem_of_mem_zipIdx taggedMem))
    generated generatedMem

end PeriodicOneInThreeNoUnits
end LeanTrominoes
