/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOneInThreeToThreeDMEncode

/-!
# Canonical periodic 3DM matching values

Given an exact-one assignment, variable-cycle triples use the corresponding
alternating phase and every clause-auxiliary triple repeats its source
literal's truth value.  This file verifies those local values, including the
translated-cell calculation along a literal-offset incidence.
-/

namespace LeanTrominoes
namespace PeriodicOneInThreeToThreeDM

namespace OccurrenceSlot

/-- The port whose phase agrees with a literal sign. -/
def literalTriple (slot : OccurrenceSlot) (value : Bool) :
    PlanarThreeDM.VariableTriple :=
  if value then slot.trueTriple else slot.falseTriple

/-- The other port in the occurrence pair. -/
def complementTriple (slot : OccurrenceSlot) (value : Bool) :
    PlanarThreeDM.VariableTriple :=
  if value then slot.falseTriple else slot.trueTriple

@[simp]
theorem variableTripleSlot_literalTriple
    (slot : OccurrenceSlot) (value : Bool) :
    variableTripleSlot (slot.literalTriple value) = slot := by
  cases slot <;> cases value <;> rfl

@[simp]
theorem variableTripleSlot_complementTriple
    (slot : OccurrenceSlot) (value : Bool) :
    variableTripleSlot (slot.complementTriple value) = slot := by
  cases slot <;> cases value <;> rfl

@[simp]
theorem variableTripleValue_literalTriple
    (slot : OccurrenceSlot) (value : Bool) :
    variableTripleValue (slot.literalTriple value) = value := by
  cases slot <;> cases value <;> rfl

@[simp]
theorem variableTripleValue_complementTriple
    (slot : OccurrenceSlot) (value : Bool) :
    variableTripleValue (slot.complementTriple value) = !value := by
  cases slot <;> cases value <;> rfl

end OccurrenceSlot

/-- Look up the source literal at one tagged clause/literal position. -/
def literalAt {Variable : Type*} (source : PeriodicCNF Variable)
    (clauseIndex literalIndex : Nat) : Option (PeriodicLiteral Variable) :=
  source.clauses[clauseIndex]?.bind fun clause =>
    clause[literalIndex]?

/-- Tagged-list membership recovers both nested source-list lookups. -/
theorem literalAt_eq_some_of_tagged_mem {Variable : Type*}
    (source : PeriodicCNF Variable)
    (tagged : TaggedOccurrence Variable)
    (member :
      tagged ∈ PeriodicThreeSATThree.taggedLiterals source) :
    literalAt source tagged.2.1 tagged.2.2 = some tagged.1 := by
  simp only [PeriodicThreeSATThree.taggedLiterals,
    List.mem_flatMap, List.mem_map] at member
  rcases member with
    ⟨taggedClause, clauseMember, taggedLiteral, literalMember, taggedEq⟩
  subst tagged
  have clauseLookup :=
    (List.mem_zipIdx_iff_getElem?).mp clauseMember
  have literalLookup :=
    (List.mem_zipIdx_iff_getElem?).mp literalMember
  simp [literalAt, clauseLookup, literalLookup]

/-- Canonical triple selections induced by a plane-wide variable assignment. -/
def matchingOfAssignment {Variable : Type*}
    (source : PeriodicCNF Variable)
    (assignment : Variable → Cell → Bool) :
    Triple Variable → Cell → Bool
  | Triple.variable atom triple, cell =>
      PlanarThreeDM.variableSelection (assignment atom cell) triple
  | Triple.clauseAuxiliary clauseIndex literalIndex, cell =>
      match literalAt source clauseIndex literalIndex with
      | none => false
      | some literal =>
          PeriodicOneInThree.literalTruth assignment cell literal

@[simp]
theorem matchingOfAssignment_variable {Variable : Type*}
    (source : PeriodicCNF Variable)
    (assignment : Variable → Cell → Bool)
    (atom : Variable) (triple : PlanarThreeDM.VariableTriple)
    (cell : Cell) :
    matchingOfAssignment source assignment (.variable atom triple) cell =
      PlanarThreeDM.variableSelection (assignment atom cell) triple := by
  rfl

/-- The auxiliary triple at a genuine tagged occurrence repeats that
literal's truth value. -/
theorem matchingOfAssignment_clauseAuxiliary {Variable : Type*}
    (source : PeriodicCNF Variable)
    (assignment : Variable → Cell → Bool)
    (translate : Cell) (tagged : TaggedOccurrence Variable)
    (member :
      tagged ∈ PeriodicThreeSATThree.taggedLiterals source) :
    matchingOfAssignment source assignment
        (.clauseAuxiliary tagged.2.1 tagged.2.2) translate =
      PeriodicOneInThree.literalTruth
        assignment translate tagged.1 := by
  simp [matchingOfAssignment,
    literalAt_eq_some_of_tagged_mem source tagged member]

/-- Every variable cycle in the canonical matching satisfies all of its
internal red and green exact-cover constraints. -/
theorem matchingOfAssignment_variableGadgetHolds {Variable : Type*}
    (source : PeriodicCNF Variable)
    (assignment : Variable → Cell → Bool)
    (atom : Variable) (cell : Cell) :
    PlanarThreeDM.VariableGadgetHolds fun triple =>
      matchingOfAssignment source assignment
        (.variable atom triple) cell := by
  rw [PlanarThreeDM.variableGadgetHolds_iff]
  cases value : assignment atom cell with
  | false =>
      right
      funext triple
      simp [matchingOfAssignment, value]
  | true =>
      left
      funext triple
      simp [matchingOfAssignment, value]

/-- At a used occurrence, the literal-side variable port carries exactly the
source literal truth value. -/
theorem matchingOfAssignment_literalPort {Variable : Type*}
    [DecidableEq Variable] (source : PeriodicCNF Variable)
    (assignment : Variable → Cell → Bool) (translate : Cell)
    (atom : Variable) (slot : OccurrenceSlot)
    (tagged : TaggedOccurrence Variable)
    (lookup : occurrenceAt source atom slot = some tagged) :
    matchingOfAssignment source assignment
        (.variable atom (slot.literalTriple tagged.1.value))
        (Cell.add translate tagged.1.offset) =
      PeriodicOneInThree.literalTruth
        assignment translate tagged.1 := by
  have atomEq :=
    (occurrenceAt_mem_and_atom source atom slot tagged lookup).2
  subst atom
  rw [matchingOfAssignment_variable, variableSelection_eq_beq]
  simp [PeriodicOneInThree.literalTruth]

/-- The other variable port carries the Boolean complement of the literal
truth value. -/
theorem matchingOfAssignment_complementPort {Variable : Type*}
    [DecidableEq Variable] (source : PeriodicCNF Variable)
    (assignment : Variable → Cell → Bool) (translate : Cell)
    (atom : Variable) (slot : OccurrenceSlot)
    (tagged : TaggedOccurrence Variable)
    (lookup : occurrenceAt source atom slot = some tagged) :
    matchingOfAssignment source assignment
        (.variable atom (slot.complementTriple tagged.1.value))
        (Cell.add translate tagged.1.offset) =
      !PeriodicOneInThree.literalTruth
        assignment translate tagged.1 := by
  have atomEq :=
    (occurrenceAt_mem_and_atom source atom slot tagged lookup).2
  subst atom
  rw [matchingOfAssignment_variable, variableSelection_eq_beq]
  cases truth :
      assignment tagged.1.atom (Cell.add translate tagged.1.offset) <;>
    cases value : tagged.1.value <;>
    simp [OccurrenceSlot.variableTripleValue_complementTriple,
      PeriodicOneInThree.literalTruth, truth, value]

/-- Reading the literal-side port through its reversed reference offset lands
at the literal's variable cell. -/
theorem matchingOfAssignment_literalIncidence {Variable : Type*}
    [DecidableEq Variable] (source : PeriodicCNF Variable)
    (assignment : Variable → Cell → Bool) (translate : Cell)
    (atom : Variable) (slot : OccurrenceSlot)
    (tagged : TaggedOccurrence Variable)
    (lookup : occurrenceAt source atom slot = some tagged) :
    (problem source).incidenceValue
        (matchingOfAssignment source assignment)
        ⟨.variable atom (slot.literalTriple tagged.1.value),
          reverseOffset tagged.1.offset⟩ translate =
      PeriodicOneInThree.literalTruth
        assignment translate tagged.1 := by
  simp only [TypedPeriodicThreeDM.incidenceValue, sub_reverseOffset]
  exact matchingOfAssignment_literalPort
    source assignment translate atom slot tagged lookup

/-- Reading the complementary port through the same reversed reference offset
likewise lands at the literal cell. -/
theorem matchingOfAssignment_complementIncidence {Variable : Type*}
    [DecidableEq Variable] (source : PeriodicCNF Variable)
    (assignment : Variable → Cell → Bool) (translate : Cell)
    (atom : Variable) (slot : OccurrenceSlot)
    (tagged : TaggedOccurrence Variable)
    (lookup : occurrenceAt source atom slot = some tagged) :
    (problem source).incidenceValue
        (matchingOfAssignment source assignment)
        ⟨.variable atom (slot.complementTriple tagged.1.value),
          reverseOffset tagged.1.offset⟩ translate =
      !PeriodicOneInThree.literalTruth
        assignment translate tagged.1 := by
  simp only [TypedPeriodicThreeDM.incidenceValue, sub_reverseOffset]
  exact matchingOfAssignment_complementPort
    source assignment translate atom slot tagged lookup

/-- The canonical literal, complementary, and auxiliary values satisfy the
paired-port clause truth table whenever the source clause is exact-one. -/
theorem canonical_clauseGadgetHolds {Variable : Type*}
    (assignment : Variable → Cell → Bool)
    (translate : Cell) (clause : PeriodicClause Variable)
    (sourceHolds :
      PeriodicOneInThree.ClauseHolds assignment translate clause) :
    PlanarThreeDM.ClauseGadgetHolds
        (PeriodicOneInThree.clauseValues assignment translate clause)
        ((PeriodicOneInThree.clauseValues
          assignment translate clause).map (!·))
        (PeriodicOneInThree.clauseValues assignment translate clause) := by
  exact
    (PlanarThreeDM.clauseGadgetHolds_complements_iff
      (PeriodicOneInThree.clauseValues assignment translate clause)
      (PeriodicOneInThree.clauseValues assignment translate clause)).mpr
        ⟨sourceHolds, rfl⟩

end PeriodicOneInThreeToThreeDM
end LeanTrominoes
