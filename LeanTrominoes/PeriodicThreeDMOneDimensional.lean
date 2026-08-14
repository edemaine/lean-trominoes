/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFOneDimensional
import LeanTrominoes.PeriodicOneInThreeToThreeDMEncode
import LeanTrominoes.PeriodicOneInThreeToThreeDMOccurrences

/-!
# One-dimensional periodic 3DM

A periodic 3DM presentation is one dimensional when every colored reference
of every prototype triple stays in the same vertical lattice translate.  The
exact-one-to-3DM construction preserves this invariant: only used variable
blue ports have nonzero offsets, and those offsets negate genuine source
literal offsets.
-/

namespace LeanTrominoes

namespace PeriodicThreeDM

/-- Every colored reference stays in the same vertical lattice translate as
its prototype triple. -/
def IsOneDimensional (problem : PeriodicThreeDM) : Prop :=
  ∀ triple ∈ problem.triples, ∀ color,
    (triple.reference color).offset.2 = 0

end PeriodicThreeDM

namespace PeriodicOneInThreeToThreeDM

/-- Typed analogue of one-dimensionality before finite element names are
encoded by natural numbers. -/
def TypedPeriodicThreeDM.IsOneDimensional
    {Variable : Type*} (problem : TypedPeriodicThreeDM Variable) : Prop :=
  ∀ triple ∈ problem.triples,
    let references := problem.references triple
    references.red.offset.2 = 0 ∧
      references.green.offset.2 = 0 ∧
      references.blue.offset.2 = 0

/-- A tagged source occurrence in a one-dimensional formula has zero
vertical offset. -/
theorem taggedLiterals_vertical_eq_zero
    {Variable : Type*}
    {source : PeriodicCNF Variable}
    (horizontal : source.IsOneDimensional)
    {tagged : TaggedOccurrence Variable}
    (taggedMember :
      tagged ∈ PeriodicThreeSATThree.taggedLiterals source) :
    tagged.1.offset.2 = 0 := by
  simp only [PeriodicThreeSATThree.taggedLiterals, List.mem_flatMap]
    at taggedMember
  obtain ⟨taggedClause, taggedClauseMember, taggedMember⟩ := taggedMember
  simp only [List.mem_map] at taggedMember
  obtain ⟨taggedLiteral, taggedLiteralMember, rfl⟩ := taggedMember
  exact horizontal taggedClause.1
    (List.fst_mem_of_mem_zipIdx taggedClauseMember)
    taggedLiteral.1
    (List.fst_mem_of_mem_zipIdx taggedLiteralMember)

/-- Every variable blue-port offset is horizontal for a one-dimensional
source formula. -/
theorem variableBlueOffset_vertical_eq_zero
    {Variable : Type*} [DecidableEq Variable]
    {source : PeriodicCNF Variable}
    (horizontal : source.IsOneDimensional)
    (atom : Variable)
    (triple : PlanarThreeDM.VariableTriple) :
    (variableBlueOffset source atom triple).2 = 0 := by
  cases lookup :
      occurrenceAt source atom (variableTripleSlot triple) with
  | none => simp [variableBlueOffset, lookup]
  | some tagged =>
      have taggedMember :=
        (occurrenceAt_mem_and_atom source atom
          (variableTripleSlot triple) tagged lookup).1
      have taggedHorizontal :=
        taggedLiterals_vertical_eq_zero horizontal taggedMember
      simpa [variableBlueOffset, lookup, reverseOffset] using taggedHorizontal

/-- Every typed triple emitted from a one-dimensional exact-one formula has
horizontal references. -/
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
  | «variable» atom triple =>
      exact ⟨rfl, rfl, variableBlueOffset_vertical_eq_zero
        horizontal atom triple⟩
  | clauseAuxiliary clauseIndex literalIndex =>
      exact ⟨rfl, rfl, rfl⟩

/-- The complete typed exact-one-to-3DM problem is one dimensional. -/
theorem problem_isOneDimensional
    {Variable : Type*} [DecidableEq Variable]
    {source : PeriodicCNF Variable}
    (horizontal : source.IsOneDimensional) :
    (problem source).IsOneDimensional := by
  intro triple _tripleMember
  exact tripleReferences_isOneDimensional horizontal triple

/-- Encoding typed color elements by finite indices preserves reference
offsets and hence one-dimensionality. -/
theorem TypedPeriodicThreeDM.encode_isOneDimensional
    {Variable : Type*} [DecidableEq Variable]
    (typed : TypedPeriodicThreeDM Variable)
    (horizontal : typed.IsOneDimensional) :
    typed.encode.IsOneDimensional := by
  intro encodedTriple encodedTripleMember color
  simp only [TypedPeriodicThreeDM.encode, List.mem_map]
    at encodedTripleMember
  obtain ⟨triple, tripleMember, rfl⟩ := encodedTripleMember
  have referencesHorizontal := horizontal triple tripleMember
  cases color with
  | red =>
      simpa [TypedPeriodicThreeDM.encodeTriple, encodeReference,
        PeriodicThreeDMTriple.reference] using
        referencesHorizontal.1
  | green =>
      simpa [TypedPeriodicThreeDM.encodeTriple, encodeReference,
        PeriodicThreeDMTriple.reference] using
        referencesHorizontal.2.1
  | blue =>
      simpa [TypedPeriodicThreeDM.encodeTriple, encodeReference,
        PeriodicThreeDMTriple.reference] using
        referencesHorizontal.2.2

/-- The natural-number periodic 3DM problem produced by the exact-one
reduction is one dimensional whenever its source formula is. -/
theorem encodedProblem_isOneDimensional
    {Variable : Type*} [DecidableEq Variable]
    {source : PeriodicCNF Variable}
    (horizontal : source.IsOneDimensional) :
    (encodedProblem source).IsOneDimensional :=
  TypedPeriodicThreeDM.encode_isOneDimensional
    (problem source) (problem_isOneDimensional horizontal)

end PeriodicOneInThreeToThreeDM
end LeanTrominoes
