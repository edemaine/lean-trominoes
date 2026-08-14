/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicPlanarOneInThreeToThreeDMEncode
import LeanTrominoes.PeriodicThreeDMOneDimensional

/-!
# One-dimensional planar exact-one-to-3DM assembly

The planar Figure 10 assembly uses zero offsets internally.  Its only
translated references are connector terminals, whose offset negates the
corresponding genuine source occurrence.  Encoding typed elements by finite
list indices leaves these offsets unchanged.
-/

namespace LeanTrominoes
namespace PeriodicPlanarOneInThreeToThreeDM

/-- Typed planar-3DM one-dimensionality before color elements are encoded by
natural numbers. -/
def TypedProblem.IsOneDimensional
    {Variable : Type*} (typed : TypedProblem Variable) : Prop :=
  ∀ triple ∈ typed.triples,
    let references := typed.references triple
    references.red.offset.2 = 0 ∧
      references.green.offset.2 = 0 ∧
      references.blue.offset.2 = 0

/-- Every occurrence connector offset is horizontal for a one-dimensional
source exact-one formula. -/
theorem occurrenceReverseOffset_vertical_eq_zero
    {Variable : Type*} [DecidableEq Variable]
    {source : PeriodicCNF Variable}
    (horizontal : source.IsOneDimensional)
    (atom : Variable) (slot : OccurrenceSlot) :
    (occurrenceReverseOffset source atom slot).2 = 0 := by
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
        PeriodicOneInThreeToThreeDM.taggedLiterals_vertical_eq_zero
          horizontal taggedMember
      simpa [occurrenceReverseOffset, lookup,
        PeriodicOneInThreeToThreeDM.reverseOffset] using taggedHorizontal

/-- Every typed triple in the planar Figure 10 assembly has horizontal
colored references. -/
theorem tripleReferences_isOneDimensional
    {Variable : Type*} [DecidableEq Variable]
    {source : PeriodicCNF Variable}
    (horizontal : source.IsOneDimensional)
    (triple : Triple Variable) :
    let references := tripleReferences source triple
    references.red.offset.2 = 0 ∧
      references.green.offset.2 = 0 ∧
      references.blue.offset.2 = 0 := by
  cases triple with
  | ordinary atom slot variant triple =>
      have terminalHorizontal :=
        occurrenceReverseOffset_vertical_eq_zero horizontal atom slot
      have iteHorizontal (condition : Prop) [Decidable condition] :
          (if condition then occurrenceReverseOffset source atom slot
            else (0, 0)).2 = 0 := by
        by_cases holds : condition <;> simp [holds, terminalHorizontal]
      simp only [tripleReferences, ordinaryTripleReferences]
      exact ⟨iteHorizontal _, iteHorizontal _, iteHorizontal _⟩
  | fixedRed atom slot triple =>
      have terminalHorizontal :=
        occurrenceReverseOffset_vertical_eq_zero horizontal atom slot
      have iteHorizontal (condition : Prop) [Decidable condition] :
          (if condition then occurrenceReverseOffset source atom slot
            else (0, 0)).2 = 0 := by
        by_cases holds : condition <;> simp [holds, terminalHorizontal]
      simp only [tripleReferences, fixedRedTripleReferences]
      exact ⟨iteHorizontal _, iteHorizontal _, iteHorizontal _⟩
  | clause clauseIndex set =>
      exact ⟨rfl, rfl, rfl⟩

/-- The complete typed planar Figure 10 problem is one dimensional. -/
theorem problem_isOneDimensional
    {Variable : Type*} [DecidableEq Variable]
    {source : PeriodicCNF Variable}
    (horizontal : source.IsOneDimensional) :
    (problem source).IsOneDimensional := by
  intro triple _tripleMember
  exact tripleReferences_isOneDimensional horizontal triple

/-- Finite-index encoding of the planar typed problem preserves its reference
offsets. -/
theorem TypedProblem.encode_isOneDimensional
    {Variable : Type*} [DecidableEq Variable]
    (typed : TypedProblem Variable)
    (horizontal : typed.IsOneDimensional) :
    typed.encode.IsOneDimensional := by
  intro encodedTriple encodedTripleMember color
  simp only [TypedProblem.encode, List.mem_map] at encodedTripleMember
  obtain ⟨triple, tripleMember, rfl⟩ := encodedTripleMember
  have referencesHorizontal := horizontal triple tripleMember
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

/-- The natural-number planar 3DM problem is one dimensional whenever its
exact-one source is. -/
theorem encodedProblem_isOneDimensional
    {Variable : Type*} [DecidableEq Variable]
    {source : PeriodicCNF Variable}
    (horizontal : source.IsOneDimensional) :
    (encodedProblem source).IsOneDimensional :=
  TypedProblem.encode_isOneDimensional
    (problem source) (problem_isOneDimensional horizontal)

end PeriodicPlanarOneInThreeToThreeDM
end LeanTrominoes
