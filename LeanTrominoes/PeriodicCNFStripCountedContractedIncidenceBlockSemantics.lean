/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.FiniteAlphabetKeyedDelimitedBlockLookupBlockSemantics
import LeanTrominoes.PeriodicCNFStripCountedContractedIncidenceSemantics
import LeanTrominoes.PeriodicCNFStripKeyedContractedIncidenceSemantics

/-! # Complete-block semantics of counted contraction -/

noncomputable section

namespace LeanTrominoes.PeriodicCNFStripReduction
namespace CountedContractedIncidence

open PeriodicThreeDM

/-- Exact incidence bodies selected in element-major occurrence-rank order. -/
def selectedBodies
    (elementCodes sizes incidenceElementCodes : List Nat)
    (bodies : List (List AxisDirection)) : List (List AxisDirection) :=
  FiniteAlphabetKeyedDelimitedBlockLookup.expectedBodyList
    (queryKeys elementCodes sizes)
    (incidenceBlockKeys incidenceElementCodes)
    bodies

/-- Under the occurrence-key contract, selected bodies are the unique
candidate bodies recovered at the requested element/rank keys. -/
theorem selectedBodies_eq_map_alignedBody
    (elementCodes sizes incidenceElementCodes : List Nat)
    (bodies : List (List AxisDirection))
    (bodiesAligned :
      bodies.length = (incidenceBlockKeys incidenceElementCodes).length)
    (keysNodup : (incidenceBlockKeys incidenceElementCodes).Nodup)
    (queriesPresent : ∀ query ∈ queryKeys elementCodes sizes,
      query ∈ incidenceBlockKeys incidenceElementCodes) :
    selectedBodies elementCodes sizes incidenceElementCodes bodies =
      (queryKeys elementCodes sizes).map
        (FiniteAlphabetKeyedDelimitedBlockLookup.alignedBody
          (incidenceBlockKeys incidenceElementCodes) bodies) := by
  unfold selectedBodies
  exact
    FiniteAlphabetKeyedDelimitedBlockLookup.expectedBodyList_eq_map_alignedBody
      _ _ _ bodiesAligned.symm keysNodup queriesPresent

/-- The degree-driven role and query compilers emit one item per requested
incidence. -/
theorem roles_length_eq_queryKeys
    (elementCodes sizes : List Nat)
    (aligned : elementCodes.length = sizes.length)
    (valid : ∀ size ∈ sizes, size = 2 ∨ size = 3) :
    (roles sizes).length = (queryKeys elementCodes sizes).length := by
  induction sizes generalizing elementCodes with
  | nil =>
      have codesNil : elementCodes = [] :=
        List.eq_nil_of_length_eq_zero (by simpa using aligned)
      subst elementCodes
      rfl
  | cons size sizes induction =>
      cases elementCodes with
      | nil => simp at aligned
      | cons elementCode elementCodes =>
          have tailAligned : elementCodes.length = sizes.length := by
            simpa using aligned
          have headValid : size = 2 ∨ size = 3 := valid size (by simp)
          have tailValid : ∀ other ∈ sizes,
              other = 2 ∨ other = 3 := by
            intro other member
            exact valid other (by simp [member])
          rcases headValid with rfl | rfl <;>
            simp [induction elementCodes tailAligned tailValid]

/-- Complete-block keyed lookup serializes exactly its abstract selected body
list. -/
theorem selected_blocks_eq
    (elementCodes sizes incidenceElementCodes : List Nat)
    (bodies : List (List AxisDirection))
    (bodiesAligned :
      bodies.length = (incidenceBlockKeys incidenceElementCodes).length) :
    FiniteAlphabetKeyedDelimitedBlockLookup.selected
        (queryKeys elementCodes sizes)
        (incidenceBlockKeys incidenceElementCodes)
        (FiniteAlphabetDelimitedBlockJoin.blocks bodies) =
      FiniteAlphabetDelimitedBlockJoin.blocks
        (selectedBodies elementCodes sizes incidenceElementCodes bodies) := by
  rw [FiniteAlphabetKeyedDelimitedBlockLookup.selected_blocks
    _ _ _ bodiesAligned]
  exact FiniteAlphabetKeyedDelimitedBlockLookup.expectedBlocks_eq_blocks
    _ _ _

/-- Unique candidate keys covering every request select exactly one body per
requested incidence. -/
theorem selectedBodies_length
    (elementCodes sizes incidenceElementCodes : List Nat)
    (bodies : List (List AxisDirection))
    (bodiesAligned :
      bodies.length = (incidenceBlockKeys incidenceElementCodes).length)
    (keysNodup : (incidenceBlockKeys incidenceElementCodes).Nodup)
    (queriesPresent : ∀ query ∈ queryKeys elementCodes sizes,
      query ∈ incidenceBlockKeys incidenceElementCodes) :
    (selectedBodies elementCodes sizes incidenceElementCodes bodies).length =
      (queryKeys elementCodes sizes).length := by
  unfold selectedBodies
  exact FiniteAlphabetKeyedDelimitedBlockLookup.expectedBodyList_length
    _ _ _ bodiesAligned keysNodup queriesPresent

/-- Under the exact occurrence-key coverage contract, counted contraction of
complete incidence blocks is precisely the established contracted-direction
assembler on the selected role/body pairs. -/
theorem output_blocks
    (elementCodes sizes incidenceElementCodes : List Nat)
    (bodies : List (List AxisDirection))
    (elementColumnsAligned : elementCodes.length = sizes.length)
    (degreesValid : ∀ size ∈ sizes, size = 2 ∨ size = 3)
    (bodiesAligned :
      bodies.length = (incidenceBlockKeys incidenceElementCodes).length)
    (keysNodup : (incidenceBlockKeys incidenceElementCodes).Nodup)
    (queriesPresent : ∀ query ∈ queryKeys elementCodes sizes,
      query ∈ incidenceBlockKeys incidenceElementCodes) :
    output elementCodes sizes incidenceElementCodes
        (FiniteAlphabetDelimitedBlockJoin.blocks bodies) =
      ContractedDirectionAssembler.output
        (((roles sizes).zip
          (selectedBodies elementCodes sizes incidenceElementCodes bodies)
        ).flatMap fun pair =>
          ContractedDirectionAssembler.roleBlock pair.1 pair.2) := by
  unfold output
  apply KeyedContractedIncidence.output_of_selected_blocks
  · exact selected_blocks_eq
      elementCodes sizes incidenceElementCodes bodies bodiesAligned
  · rw [roles_length_eq_queryKeys
      elementCodes sizes elementColumnsAligned degreesValid]
    exact (selectedBodies_length
      elementCodes sizes incidenceElementCodes bodies bodiesAligned
      keysNodup queriesPresent).symm

end CountedContractedIncidence
end LeanTrominoes.PeriodicCNFStripReduction

end
