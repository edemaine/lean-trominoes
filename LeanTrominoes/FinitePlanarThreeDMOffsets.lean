/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.FinitePolarityNormalizationOffsets
import LeanTrominoes.PeriodicPlanarOneInThreeToThreeDMOneDimensional
import LeanTrominoes.PeriodicPlanarOneInThreeToThreeDMNormalized

/-! # Finite offsets survive planar exact-one-to-3DM assembly -/
namespace LeanTrominoes.PeriodicThreeDM
/-- Every colored reference stays in its prototype triple's lattice cell. -/
def ZeroOffsets (problem : PeriodicThreeDM) : Prop :=
  ∀ triple∈problem.triples,∀ color,(triple.reference color).offset=(0,0)
end LeanTrominoes.PeriodicThreeDM
namespace LeanTrominoes.PeriodicOneInThreeToThreeDM

theorem taggedLiterals_offset_eq_zero {V : Type*} {source : PeriodicCNF V}
    (zero : FiniteCNF.ZeroOffsets source) {tagged : TaggedOccurrence V}
    (member : tagged∈PeriodicThreeSATThree.taggedLiterals source) : tagged.1.offset=(0,0) := by
  simp only [PeriodicThreeSATThree.taggedLiterals,List.mem_flatMap] at member
  obtain ⟨clause,clauseMember,member⟩ := member
  obtain ⟨literal,literalMember,rfl⟩ := List.mem_map.mp member
  exact zero clause.1 (List.fst_mem_of_mem_zipIdx clauseMember) literal.1 (List.fst_mem_of_mem_zipIdx literalMember)
end LeanTrominoes.PeriodicOneInThreeToThreeDM
namespace LeanTrominoes
namespace PeriodicPlanarOneInThreeToThreeDM

/-- Typed planar-3DM zero offsets before color elements are encoded by
natural numbers. -/
def TypedProblem.ZeroOffsets
    {Variable : Type*} (typed : TypedProblem Variable) : Prop :=
  ∀ triple ∈ typed.triples,
    let references := typed.references triple
    references.red.offset = (0,0) ∧
      references.green.offset = (0,0) ∧
      references.blue.offset = (0,0)

/-- Every occurrence connector offset is zero for a finite
source exact-one formula. -/
theorem occurrenceReverseOffset_offset_eq_zero
    {Variable : Type*} [DecidableEq Variable]
    {source : PeriodicCNF Variable}
    (zero : FiniteCNF.ZeroOffsets source)
    (atom : Variable) (slot : OccurrenceSlot) :
    occurrenceReverseOffset source atom slot = (0,0) := by
  cases lookup : occurrenceAt source atom slot with
  | none => simp [occurrenceReverseOffset, lookup]
  | some tagged =>
      have coreLookup :
          PeriodicOneInThreeToThreeDM.occurrenceAt source atom slot =
            some tagged := by
        simpa [occurrenceAt] using lookup
      have taggedMember :=
        (PeriodicOneInThreeToThreeDM.occurrenceAt_mem_and_atom
          source atom slot tagged coreLookup).1
      have taggedHorizontal :=
        PeriodicOneInThreeToThreeDM.taggedLiterals_offset_eq_zero
          zero taggedMember
      simp [occurrenceReverseOffset,lookup,
        PeriodicOneInThreeToThreeDM.reverseOffset,taggedHorizontal]

/-- Every typed triple in the planar Figure 10 assembly has zero
colored references. -/
theorem tripleReferences_zeroOffsets
    {Variable : Type*} [DecidableEq Variable]
    {source : PeriodicCNF Variable}
    (zero : FiniteCNF.ZeroOffsets source)
    (triple : Triple Variable) :
    let references := tripleReferences source triple
    references.red.offset = (0,0) ∧
      references.green.offset = (0,0) ∧
      references.blue.offset = (0,0) := by
  cases triple with
  | ordinary atom slot variant triple =>
      have terminalHorizontal :=
        occurrenceReverseOffset_offset_eq_zero zero atom slot
      have iteHorizontal (condition : Prop) [Decidable condition] :
          (if condition then occurrenceReverseOffset source atom slot
            else (0, 0)) = (0,0) := by
        by_cases holds : condition <;> simp [holds, terminalHorizontal]
      simp only [tripleReferences, ordinaryTripleReferences]
      exact ⟨iteHorizontal _, iteHorizontal _, iteHorizontal _⟩
  | fixedRed atom slot triple =>
      have terminalHorizontal :=
        occurrenceReverseOffset_offset_eq_zero zero atom slot
      have iteHorizontal (condition : Prop) [Decidable condition] :
          (if condition then occurrenceReverseOffset source atom slot
            else (0, 0)) = (0,0) := by
        by_cases holds : condition <;> simp [holds, terminalHorizontal]
      simp only [tripleReferences, fixedRedTripleReferences]
      exact ⟨iteHorizontal _, iteHorizontal _, iteHorizontal _⟩
  | clause clauseIndex set =>
      exact ⟨rfl, rfl, rfl⟩

/-- The complete typed planar Figure 10 problem is finite. -/
theorem problem_zeroOffsets
    {Variable : Type*} [DecidableEq Variable]
    {source : PeriodicCNF Variable}
    (zero : FiniteCNF.ZeroOffsets source) :
    (problem source).ZeroOffsets := by
  intro triple _tripleMember
  exact tripleReferences_zeroOffsets zero triple

/-- Finite-index encoding of the planar typed problem preserves its reference
offsets. -/
theorem TypedProblem.encode_zeroOffsets
    {Variable : Type*} [DecidableEq Variable]
    (typed : TypedProblem Variable)
    (zero : typed.ZeroOffsets) :
    typed.encode.ZeroOffsets := by
  intro encodedTriple encodedTripleMember color
  simp only [TypedProblem.encode, List.mem_map] at encodedTripleMember
  obtain ⟨triple, tripleMember, rfl⟩ := encodedTripleMember
  have referencesHorizontal := zero triple tripleMember
  cases color with
  | red =>
      simpa [TypedProblem.encodeTriple, encodeReference,
        PeriodicThreeDMTriple.reference] using referencesHorizontal.1
  | green =>
      simpa [TypedProblem.encodeTriple, encodeReference,
        PeriodicThreeDMTriple.reference] using referencesHorizontal.2.1
  | blue =>
      simpa [TypedProblem.encodeTriple, encodeReference,
        PeriodicThreeDMTriple.reference] using referencesHorizontal.2.2

/-- The natural-number planar 3DM problem is finite whenever its
exact-one source is. -/
theorem encodedProblem_zeroOffsets
    {Variable : Type*} [DecidableEq Variable]
    {source : PeriodicCNF Variable}
    (zero : FiniteCNF.ZeroOffsets source) :
    (encodedProblem source).ZeroOffsets :=
  TypedProblem.encode_zeroOffsets
    (problem source) (problem_zeroOffsets zero)

end PeriodicPlanarOneInThreeToThreeDM
end LeanTrominoes

namespace LeanTrominoes.PeriodicPlanarOneInThreeToThreeDM

theorem normalizedProblem_zeroOffsets {V : Type*} [DecidableEq V]
    {source : PositionedPeriodicCNF V} (placement : PeriodicVariablePlacement V)
    (zero : FiniteCNF.ZeroOffsets source.erase) :
    (normalizedProblem source placement).ZeroOffsets := by
  unfold normalizedProblem
  apply encodedProblem_zeroOffsets
  rw [normalizedSource_eq]
  apply FiniteCNF.uniformOffsets_anchorNormalize
  intro clause member
  exact ⟨(0,0),zero clause member⟩
end LeanTrominoes.PeriodicPlanarOneInThreeToThreeDM
