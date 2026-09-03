/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFFormulaShapeFigureNineRoutePrefixIndexedProfileCoordinateBlocks

/-! # Metadata lookup from indexed Figure 9 coordinate streams -/

namespace LeanTrominoes
namespace PeriodicCNF
namespace FormulaShapeFigureNineRoutePrefix

open PlanarOneInThreeNoUnitsFigureNine

/-- A flattened coordinate stream and its blockwise parent projection locate
the corresponding metadata entry at every occurrence index. -/
theorem exists_metadata_of_indexedProfileCoordinateStream
    {Pair Metadata : Type} [Inhabited Pair]
    (coordinateOf : Pair → HeaderTemplateProfileCoordinate)
    (indices : List Nat) (pairs : List Pair)
    (blocks : List IndexedProfileCoordinateBlock)
    (metadata : List Metadata)
    (metadataParent : Metadata → ParentProfileCoordinate)
    (lengthEq : indices.length = pairs.length)
    (streamEq :
      List.zipWith (fun blockIndex pair =>
          (blockIndex, coordinateOf pair)) indices pairs =
        blocks.zipIdx.flatMap fun taggedBlock =>
          taggedBlock.1.coordinates.map fun coordinate =>
            (taggedBlock.2, coordinate))
    (parentEq :
      blocks.map IndexedProfileCoordinateBlock.parent =
        metadata.map metadataParent)
    (coordinateParent :
      ∀ block ∈ blocks, ∀ coordinate ∈ block.coordinates,
        coordinate.profile = block.parent.profile ∧
        coordinate.coordinate.clauseIndex = block.parent.clauseIndex)
    (index : Nat) (indexLt : index < pairs.length) :
    ∃ selectedMetadata,
      metadata[indices.getD index 0]? = some selectedMetadata ∧
      (coordinateOf (pairs.getD index default)).profile =
        (metadataParent selectedMetadata).profile ∧
      (coordinateOf (pairs.getD index default)).coordinate.clauseIndex =
        (metadataParent selectedMetadata).clauseIndex := by
  have indicesLt : index < indices.length := by
    simpa only [lengthEq] using indexLt
  have streamMember :
      (indices.getD index 0,
        coordinateOf (pairs.getD index default)) ∈
        List.zipWith (fun blockIndex pair =>
          (blockIndex, coordinateOf pair)) indices pairs := by
    apply List.mem_iff_getElem?.mpr
    refine ⟨index, ?_⟩
    simp only [List.getElem?_zipWith,
      List.getElem?_eq_getElem indicesLt,
      List.getElem?_eq_getElem indexLt]
    rw [List.getD_eq_getElem _ _ indicesLt,
      List.getD_eq_getElem _ _ indexLt]
  rw [streamEq] at streamMember
  rcases List.mem_flatMap.mp streamMember with
    ⟨taggedBlock, taggedBlockMember, coordinateMember⟩
  rcases List.mem_map.mp coordinateMember with
    ⟨coordinate, coordinateInBlock, coordinateEq⟩
  have blockLookup :
      blocks[taggedBlock.2]? = some taggedBlock.1 :=
    (List.mem_zipIdx_iff_getElem?).mp taggedBlockMember
  have parentLookup := congrArg
    (fun values => values[taggedBlock.2]?) parentEq
  simp only [List.getElem?_map, blockLookup, Option.map_some] at parentLookup
  rcases Option.map_eq_some_iff.mp parentLookup.symm with
    ⟨selectedMetadata, metadataLookup, metadataParentEq⟩
  have blockInvariant := coordinateParent taggedBlock.1
    (List.fst_mem_of_mem_zipIdx taggedBlockMember)
    coordinate coordinateInBlock
  have blockIndexEq :
      taggedBlock.2 = indices.getD index 0 :=
    congrArg Prod.fst coordinateEq
  have coordinateEq' :
      coordinate = coordinateOf (pairs.getD index default) :=
    congrArg Prod.snd coordinateEq
  refine ⟨selectedMetadata, ?_, ?_, ?_⟩
  · rw [← blockIndexEq]
    exact metadataLookup
  · exact
      (congrArg HeaderTemplateProfileCoordinate.profile coordinateEq').symm.trans
      (blockInvariant.1.trans
        (congrArg ParentProfileCoordinate.profile metadataParentEq.symm))
  · exact
      (congrArg
        (fun value : HeaderTemplateProfileCoordinate =>
          value.coordinate.clauseIndex) coordinateEq').symm.trans
      (blockInvariant.2.trans
        (congrArg ParentProfileCoordinate.clauseIndex metadataParentEq.symm))

end FormulaShapeFigureNineRoutePrefix
end PeriodicCNF
end LeanTrominoes
