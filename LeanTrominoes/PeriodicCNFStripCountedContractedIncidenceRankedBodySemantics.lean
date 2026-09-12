/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripCountedContractedIncidenceRankedIndexSemantics

/-! # Direction bodies obtained from the shared counted incidence index order -/

namespace LeanTrominoes.PeriodicCNFStripReduction
namespace CountedContractedIncidence

/-- Read each direction body at its shared stable incidence index. -/
theorem queryBlock_map_alignedBody_eq_idxsOf_map_getD
    (incidenceElementCodes : List Nat)
    (bodies : List (List AxisDirection))
    (countLeThree : ∀ code ∈ incidenceElementCodes,
      incidenceElementCodes.count code ≤ 3)
    (elementCode size : Nat)
    (valid : size = 2 ∨ size = 3)
    (sizeEq : size = incidenceElementCodes.count elementCode) :
    (queryBlock elementCode size).map
        (FiniteAlphabetKeyedDelimitedBlockLookup.alignedBody
          (StableOccurrenceRanks.candidateKeys incidenceElementCodes)
          bodies) =
      (incidenceElementCodes.idxsOf elementCode).map fun index =>
        bodies.getD index [] := by
  unfold FiniteAlphabetKeyedDelimitedBlockLookup.alignedBody
  simpa only [List.map_map, List.map_flatMap, Function.comp_def] using
    congrArg (List.map (fun index => bodies.getD index []))
      (queryBlock_map_candidateIndex_eq_idxsOf
      incidenceElementCodes countLeThree elementCode size valid sizeEq)

/-- Direction bodies inherit the common element-major index ordering. -/
theorem queryKeys_map_alignedBody_eq_flatMap_idxsOf
    (elementCodes sizes incidenceElementCodes : List Nat)
    (bodies : List (List AxisDirection))
    (columnsAligned : elementCodes.length = sizes.length)
    (degreesValid : ∀ size ∈ sizes, size = 2 ∨ size = 3)
    (countsAgree : ∀ pair ∈ elementCodes.zip sizes,
      pair.2 = incidenceElementCodes.count pair.1)
    (countLeThree : ∀ code ∈ incidenceElementCodes,
      incidenceElementCodes.count code ≤ 3) :
    (queryKeys elementCodes sizes).map
        (FiniteAlphabetKeyedDelimitedBlockLookup.alignedBody
          (StableOccurrenceRanks.candidateKeys incidenceElementCodes)
          bodies) =
      elementCodes.flatMap fun elementCode =>
        (incidenceElementCodes.idxsOf elementCode).map fun index =>
          bodies.getD index [] := by
  unfold FiniteAlphabetKeyedDelimitedBlockLookup.alignedBody
  simpa only [List.map_map, List.map_flatMap, Function.comp_def] using
    congrArg (List.map (fun index => bodies.getD index []))
      (queryKeys_map_candidateIndex_eq_flatMap_idxsOf
      elementCodes sizes incidenceElementCodes columnsAligned degreesValid countsAgree countLeThree)

/-- The degree-expansion contract supplies the complete direction selection order. -/
theorem queryKeys_map_alignedBody_eq_flatMap_idxsOf_of_perm_expanded
    (elementCodes sizes incidenceElementCodes : List Nat)
    (bodies : List (List AxisDirection))
    (columnsAligned : elementCodes.length = sizes.length)
    (degreesValid : ∀ size ∈ sizes, size = 2 ∨ size = 3)
    (elementCodesNodup : elementCodes.Nodup)
    (incidencePermutation : incidenceElementCodes.Perm
      (expandedElementCodes (elementCodes.zip sizes))) :
    (queryKeys elementCodes sizes).map
        (FiniteAlphabetKeyedDelimitedBlockLookup.alignedBody
          (StableOccurrenceRanks.candidateKeys incidenceElementCodes)
          bodies) =
      elementCodes.flatMap fun elementCode =>
        (incidenceElementCodes.idxsOf elementCode).map fun index =>
          bodies.getD index [] := by
  unfold FiniteAlphabetKeyedDelimitedBlockLookup.alignedBody
  simpa only [List.map_map, List.map_flatMap, Function.comp_def] using
    congrArg (List.map (fun index => bodies.getD index []))
      (queryKeys_map_candidateIndex_eq_flatMap_idxsOf_of_perm_expanded
      elementCodes sizes incidenceElementCodes columnsAligned degreesValid elementCodesNodup incidencePermutation)

end CountedContractedIncidence
end LeanTrominoes.PeriodicCNFStripReduction
