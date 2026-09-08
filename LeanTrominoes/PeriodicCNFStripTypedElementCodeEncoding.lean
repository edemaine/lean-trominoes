/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman
-/
import LeanTrominoes.PeriodicCNFStripTypedIncidenceElementCodes
import LeanTrominoes.PeriodicPlanarOneInThreeToThreeDMEncode
import LeanTrominoes.PeriodicThreeDMIncidenceTagElementOrder
import LeanTrominoes.ListRangeGetD

/-! # Structural element codes survive the natural-number encoding -/

namespace LeanTrominoes.PeriodicCNFStripReduction.TypedElementCode

open Gadget PeriodicThreeDM PeriodicPlanarOneInThreeToThreeDM

variable {Variable : Type*} [DecidableEq Variable]

/-- Read a structural name at its position in the encoded color class. -/
def encodedElement (source : PeriodicCNF Variable)
    (key : Variable × OccurrenceSlot → Nat) (element : WireColor × Nat) : Nat :=
  (elements source key element.1).getD element.2 0

private theorem map_getD_idxOf {Element : Type*} [DecidableEq Element]
    (values : List Element) (code : Element → Nat) (atom : Element)
    (member : atom ∈ values) :
    (values.map code).getD (values.idxOf atom) 0 = code atom := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_idxOf member]

/-- Numbering a genuine triple reference preserves its structural name. -/
theorem encodedElement_encodeTriple (source : PeriodicCNF Variable)
    (key : Variable × OccurrenceSlot → Nat) (triple : Triple Variable)
    (member : triple ∈ triples source) (color : WireColor) :
    encodedElement source key
        (color, (((problem source).encodeTriple triple).reference color).atom) =
      reference key (tripleReferences source triple) color := by
  have listed := problem_isWellFormed source triple member
  cases color with
  | red => exact map_getD_idxOf _ _ _ listed.1
  | green => exact map_getD_idxOf _ _ _ listed.2.1
  | blue => exact map_getD_idxOf _ _ _ listed.2.2


/-- The complete encoded incidence column keeps typed-triple and RGB order. -/
theorem incidenceTags_map_encodedElement (source : PeriodicCNF Variable)
    (key : Variable × OccurrenceSlot → Nat) :
    (encodedProblem source).incidenceTags.map (fun tag =>
        encodedElement source key ((encodedProblem source).incidenceElement tag)) =
      (triples source).flatMap (fun triple => incidenceColors.map fun color =>
        reference key (tripleReferences source triple) color) := by
  calc
    _ = (triples source).zipIdx.flatMap (fun tagged => incidenceColors.map fun color =>
        reference key (tripleReferences source tagged.1) color) := by
      unfold incidenceTags encodedProblem TypedProblem.encode
      rw [List.zipIdx_map, List.flatMap_map, List.map_flatMap]
      apply List.flatMap_congr
      intro tagged member
      simp only [tripleIncidenceTags, List.map_map]
      apply List.map_congr_left
      intro color _
      have indexed := List.mem_zipIdx' member
      have encodedAt :
          ((problem source).encode.triples.getD tagged.2 default) =
            (problem source).encodeTriple tagged.1 := by
        rw [List.getD_eq_getElem]
        · simpa only [TypedProblem.encode, List.getElem_map] using
            congrArg (problem source).encodeTriple indexed.2.symm
        · simpa only [TypedProblem.encode, List.length_map] using indexed.1
      change encodedElement source key (color,
        (((problem source).encode.triples.getD tagged.2 default).reference color).atom) = _
      rw [encodedAt]
      exact encodedElement_encodeTriple source key tagged.1
        (List.fst_mem_of_mem_zipIdx member) color
    _ = _ := by
      simpa only [List.flatMap_map] using congrArg
        (fun values : List (Triple Variable) => values.flatMap (fun triple =>
          incidenceColors.map fun color => reference key (tripleReferences source triple) color))
        (List.zipIdx_map_fst 0 (triples source))


/-- Structural names and encoded elements have identical color-class lengths. -/
theorem elements_length (source : PeriodicCNF Variable)
    (key : Variable × OccurrenceSlot → Nat) (color : WireColor) :
    (elements source key color).length = (encodedProblem source).elementCount color := by
  cases color <;> simp [elements, encodedProblem, TypedProblem.encode, problem,
    PeriodicThreeDM.elementCount]

/-- Enumerating an encoded color class recovers its structural code column. -/
theorem encodedElement_map_range (source : PeriodicCNF Variable)
    (key : Variable × OccurrenceSlot → Nat) (color : WireColor) :
    (List.range ((encodedProblem source).elementCount color)).map
        (fun atom => encodedElement source key (color, atom)) =
      elements source key color := by
  unfold encodedElement
  rw [← elements_length source key color]
  exact List.map_range_getD (elements source key color) 0


/-- Reading all numbered elements gives the color-major structural code list. -/
theorem encodedElement_map_colorMajor (source : PeriodicCNF Variable)
    (key : Variable × OccurrenceSlot → Nat) :
    (incidenceColors.flatMap (fun color =>
      (List.range ((encodedProblem source).elementCount color)).map (fun atom => (color, atom)))).map
        (encodedElement source key) =
      incidenceColors.flatMap (elements source key) := by
  rw [List.map_flatMap]
  apply List.flatMap_congr
  intro color _
  rw [List.map_map]
  exact encodedElement_map_range source key color

/-- Duplicate-free structural codes distinguish all valid colored elements.
No injectivity on unused typed constructors is needed. -/
theorem encodedElement_eq_iff (source : PeriodicCNF Variable)
    (key : Variable × OccurrenceSlot → Nat)
    (unique : (incidenceColors.flatMap (elements source key)).Nodup)
    (first second : WireColor × Nat)
    (firstLt : first.2 < (encodedProblem source).elementCount first.1)
    (secondLt : second.2 < (encodedProblem source).elementCount second.1) :
    encodedElement source key first = encodedElement source key second ↔ first = second := by
  constructor
  · intro equal
    have mappedUnique := unique
    rw [← encodedElement_map_colorMajor source key] at mappedUnique
    apply List.inj_on_of_nodup_map mappedUnique _ _ equal
    · apply List.mem_flatMap.mpr
      refine ⟨first.1, ?_, List.mem_map.mpr ⟨first.2, List.mem_range.mpr firstLt, rfl⟩⟩
      cases first.1 <;> simp [incidenceColors]
    · apply List.mem_flatMap.mpr
      refine ⟨second.1, ?_, List.mem_map.mpr ⟨second.2, List.mem_range.mpr secondLt, rfl⟩⟩
      cases second.1 <;> simp [incidenceColors]
  · rintro rfl
    rfl

end LeanTrominoes.PeriodicCNFStripReduction.TypedElementCode
