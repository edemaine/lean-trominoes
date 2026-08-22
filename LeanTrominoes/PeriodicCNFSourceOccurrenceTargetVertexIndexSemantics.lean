/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFSourceOccurrenceTargetVertexIndexCompiler
import LeanTrominoes.PeriodicThreeSATThreeOccurrenceTargetIndex
import LeanTrominoes.UnaryAlignedAddSemantics

/-! # Semantics of compiled source occurrence target indices -/

namespace LeanTrominoes
namespace PeriodicCNF
namespace SourceOccurrenceTargetVertexIndices

private theorem zipWith_map_map
    {Value : Type*} (values : List Value)
    (first second : Value → Nat) :
    List.zipWith (· + ·) (values.map first) (values.map second) =
      values.map fun value => first value + second value := by
  induction values with
  | nil => rfl
  | cons value values induction =>
      simp only [List.map_cons, List.zipWith_cons_cons, induction]

private theorem idxOf_decidableEq_eq
    (item : ThreeOccurrenceVariable Nat)
    (items : List (ThreeOccurrenceVariable Nat)) :
    @List.idxOf (ThreeOccurrenceVariable Nat)
        instBEqOfDecidableEq item items = items.idxOf item := by
  induction items with
  | nil => rfl
  | cons head tail induction =>
      simp only [List.idxOf_cons, Bool.cond_eq_ite, beq_iff_eq]
      rw [induction]

/-- The compiled index stream is the pointwise sum of each atom's
last-occurrence-ordered block start and its rotated stable rank. -/
theorem indices_eq_map_zipIdx
    (source : SourceSplitRouteDescriptorTokens.Source) :
    indices source =
      (SourceOccurrenceAtomRanks.occurrenceAtoms
        source.formula).zipIdx.map fun tagged =>
          LastOccurrenceBlockStarts.blockStart
              (SourceOccurrenceAtomRanks.occurrenceAtoms source.formula)
              tagged.1 +
            UnaryRotatedRanksMachine.rotatedRank
              (((SourceOccurrenceAtomRanks.occurrenceAtoms
                source.formula).take tagged.2).count tagged.1)
              ((SourceOccurrenceAtomRanks.occurrenceAtoms
                source.formula).count tagged.1) := by
  unfold indices
  rw [UnaryAlignedAddMachine.sums_eq_zipWith
      (additionInput source).valid,
    additionInput_firsts, additionInput_seconds,
    SourceOccurrenceAtomPerOccurrenceBlockStarts.starts_eq_lastOccurrenceBlockStarts,
    SourceOccurrenceAtomRotatedRanks.ranks_eq_map_zipIdx]
  unfold LastOccurrenceBlockStarts.starts
  let atoms := SourceOccurrenceAtomRanks.occurrenceAtoms source.formula
  have firstMap : atoms.map
      (LastOccurrenceBlockStarts.blockStart atoms) =
      atoms.zipIdx.map fun tagged =>
        LastOccurrenceBlockStarts.blockStart atoms tagged.1 := by
    calc
      atoms.map (LastOccurrenceBlockStarts.blockStart atoms) =
          (atoms.zipIdx.map Prod.fst).map
            (LastOccurrenceBlockStarts.blockStart atoms) := by
        rw [List.zipIdx_map_fst]
      _ = atoms.zipIdx.map fun tagged =>
          LastOccurrenceBlockStarts.blockStart atoms tagged.1 := by
        rw [List.map_map]
        rfl
  rw [show SourceOccurrenceAtomRanks.occurrenceAtoms source.formula =
      atoms by rfl, firstMap]
  exact zipWith_map_map atoms.zipIdx
    (fun tagged => LastOccurrenceBlockStarts.blockStart atoms tagged.1)
    (fun tagged => UnaryRotatedRanksMachine.rotatedRank
      ((atoms.take tagged.2).count tagged.1) (atoms.count tagged.1))

@[simp] theorem indices_length
    (source : SourceSplitRouteDescriptorTokens.Source) :
    (indices source).length =
      (SourceOccurrenceAtomRanks.occurrenceAtoms source.formula).length := by
  rw [indices_eq_map_zipIdx]
  simp

theorem indices_getElem?
    (source : SourceSplitRouteDescriptorTokens.Source) (index : Nat) :
    (indices source)[index]? =
      ((SourceOccurrenceAtomRanks.occurrenceAtoms
        source.formula)[index]?).map fun atom =>
          LastOccurrenceBlockStarts.blockStart
              (SourceOccurrenceAtomRanks.occurrenceAtoms source.formula)
              atom +
            UnaryRotatedRanksMachine.rotatedRank
              (((SourceOccurrenceAtomRanks.occurrenceAtoms
                source.formula).take index).count atom)
              ((SourceOccurrenceAtomRanks.occurrenceAtoms
                source.formula).count atom) := by
  rw [indices_eq_map_zipIdx, List.getElem?_map, List.getElem?_zipIdx]
  simp [Function.comp_def]

/-- At a genuine positional source copy, the compiled value is exactly its
global variable-vertex index in the occurrence-split formula. -/
theorem indices_getElem?_eq_copy_target
    (source : SourceSplitRouteDescriptorTokens.Source)
    (tagged : ThreeOccurrenceVariable Nat × Nat)
    (taggedMember : tagged ∈
      (PeriodicThreeSATThree.allOccurrenceVariables
        source.formula).zipIdx) :
    (indices source)[tagged.2]? = some
      ((PeriodicThreeSATThree.rotatedOccurrenceVariables
        source.formula).idxOf tagged.1) := by
  rw [indices_getElem?]
  have atomLookup :
      (SourceOccurrenceAtomRanks.occurrenceAtoms
        source.formula)[tagged.2]? = some tagged.1.1 := by
    rw [SourceOccurrenceAtomRanks.occurrenceAtoms_eq_allOccurrenceVariables_fst,
      List.getElem?_map,
      (List.mem_zipIdx_iff_getElem?).mp taggedMember]
    rfl
  rw [atomLookup]
  simp only [Option.map_some]
  rw [← idxOf_decidableEq_eq]
  exact congrArg some
    (PeriodicThreeSATThree.occurrence_rotatedOccurrenceVariables_idxOf_decidableEq
      source.formula tagged taggedMember).symm

end SourceOccurrenceTargetVertexIndices
end PeriodicCNF
end LeanTrominoes
