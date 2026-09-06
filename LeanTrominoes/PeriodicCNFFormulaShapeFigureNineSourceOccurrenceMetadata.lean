/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman
-/
import LeanTrominoes.PeriodicCNFFormulaShapeFigureNineSourceOccurrences
import LeanTrominoes.PeriodicCNFFormulaShapeRetainedFigureNineDirectionExact
import LeanTrominoes.PeriodicCNFFormulaShapeRetainedFigureNineSourceTailData
import LeanTrominoes.PeriodicCNFFormulaShapeFigureNineRoutePrefixSemantics
import LeanTrominoes.PeriodicCNFFormulaShapeFigureNinePolarityRouteTailRouteOrderSemantics
import LeanTrominoes.PeriodicCNFFormulaShapeFigureNinePolarityRouteHeaderPrefixSemantics
import LeanTrominoes.PeriodicOneInThreeNoUnitsFigureNineMetadataParentProfileCoordinates
import LeanTrominoes.PositionedPeriodicCNFFormulaShapeProfiles

/-! # Exact metadata keys of complete Figure 9 source occurrences -/

namespace LeanTrominoes.PeriodicCNF.FormulaShapeFigureNinePolarityRouteTail

open FormulaShapeDirectionOrdering
open FormulaShapeFigureNinePolarityRouteHeader
open FormulaShapeFigureNineRoutePrefix
open PlanarOneInThreeNoUnitsFigureNine

/-- All finite header coordinates are checked together, including the bound
that rules out the total lookup's fallback literal. -/
theorem header_coordinate_invariants
    (profile : DirectedClauseProfile) (header : Header)
    (member : header ∈ sourceClauseHeaders profile) :
    let coordinate := headerTemplateProfileCoordinate header
    let parent : ParentProfileCoordinate :=
      ⟨coordinate.profile, coordinate.coordinate.clauseIndex⟩
    coordinate.profile = clauseProfile (orderedDirectedProfile profile) ∧
    coordinate.coordinate.literalIndex =
      (FormulaShapeFigureNineFinalClauseOrdering.reorderList
        (List.range parent.literalCount)).getD
          coordinate.coordinate.polarity.sourceLiteralIndex 0 ∧
    coordinate.coordinate.polarity.sourceLiteralIndex < parent.literalCount := by
  have checked : ∀ profile : DirectedClauseProfile,
      (sourceClauseHeaders profile).all (fun header => decide (
        let coordinate := headerTemplateProfileCoordinate header
        let parent : ParentProfileCoordinate :=
          ⟨coordinate.profile, coordinate.coordinate.clauseIndex⟩
        coordinate.profile = clauseProfile (orderedDirectedProfile profile) ∧
        coordinate.coordinate.literalIndex =
          (FormulaShapeFigureNineFinalClauseOrdering.reorderList
            (List.range parent.literalCount)).getD
              coordinate.coordinate.polarity.sourceLiteralIndex 0 ∧
        coordinate.coordinate.polarity.sourceLiteralIndex < parent.literalCount)) = true := by
    native_decide
  exact of_decide_eq_true ((List.all_eq_true.mp (checked profile)) header member)

/-- Metadata keys in original source-clause order. Every generated clause
retains its original parent, including when several parents have equal
finite profiles. -/
def profileMetadataKeysFrom (parent : Nat) :
    List UnaryProgramClauseProfile.ClauseProfile → List (Nat × Nat)
  | [] => []
  | profile :: profiles =>
      ((List.range (templateDrawingOfClauseProfile profile).formula.length).map
        fun localIndex => (parent, localIndex)) ++
      profileMetadataKeysFrom (parent + 1) profiles

def sourceMetadataKeysFrom (parent : Nat) :
    List FormulaShapeDirectionOrdering.Token → List (Nat × Nat)
  | [] => []
  | .variable :: source => sourceMetadataKeysFrom parent source
  | .clause profile :: source =>
      ((List.range (generatedClauseCount profile)).map
        fun localIndex => (parent, localIndex)) ++
      sourceMetadataKeysFrom (parent + 1) source

theorem sourceMetadataKeysFrom_eq_profiles
    (parent : Nat) (source : List FormulaShapeDirectionOrdering.Token) :
    sourceMetadataKeysFrom parent source =
      profileMetadataKeysFrom parent
        (FormulaShape.clauseProfiles (FormulaShapeDirectionOrdering.shape source)) := by
  rw [FormulaShapeDirectionOrdering.clauseProfiles_shape]
  induction source generalizing parent with
  | nil => rfl
  | cons token source induction =>
      cases token with
      | «variable» => simpa [sourceMetadataKeysFrom] using induction parent
      | clause profile =>
          simp only [sourceMetadataKeysFrom, List.filterMap_cons,
            profileMetadataKeysFrom, generatedClauseCount,
            clauseProfile_orderedDirectedProfile, induction]

private theorem header_clauseIndex_lt
    (profile : DirectedClauseProfile)
    (header : Header) (member : header ∈ sourceClauseHeaders profile) :
    (headerTemplateCoordinate header).clauseIndex <
      generatedClauseCount profile := by
  have coordinateMember : headerTemplateCoordinate header ∈
      (sourceClauseHeaders profile).map headerTemplateCoordinate :=
    List.mem_map.mpr ⟨header, member, rfl⟩
  rw [sourceClauseHeaders_map_headerTemplateCoordinate] at coordinateMember
  rcases List.mem_flatMap.mp coordinateMember with
    ⟨taggedClause, clauseMember, localMember⟩
  rcases List.mem_map.mp localMember with ⟨polarity, _, coordinateEq⟩
  have indexEq := congrArg HeaderTemplateCoordinate.clauseIndex coordinateEq
  rw [← indexEq]
  exact List.snd_lt_of_mem_zipIdx clauseMember

/-- The parent key and absolute generated-clause index belong to the same
indexed metadata stream. This is stronger than matching a finite profile. -/
theorem sourceOccurrencesFrom_metadataKey_mem
    (parentStart generatedStart : Nat)
    (source : List FormulaShapeDirectionOrdering.Token)
    (tailTables : List (List (List AxisDirection)))
    (occurrence : SourceOccurrence)
    (member : occurrence ∈
      sourceOccurrencesFrom parentStart generatedStart source tailTables) :
    (occurrence.metadataKey, occurrence.generatedClauseIndex) ∈
      (sourceMetadataKeysFrom parentStart source).zipIdx generatedStart := by
  induction source generalizing parentStart generatedStart tailTables with
  | nil => exact False.elim (List.not_mem_nil member)
  | cons token source induction =>
      cases token with
      | «variable» => exact induction _ _ _ member
      | clause profile =>
          rw [sourceOccurrencesFrom, List.mem_append] at member
          rw [sourceMetadataKeysFrom, List.zipIdx_append]
          rcases member with headMember | tailMember
          · rcases List.mem_map.mp headMember with ⟨header, headerMember, equality⟩
            subst occurrence
            apply List.mem_append_left
            have indexLt := header_clauseIndex_lt profile header headerMember
            rw [List.zipIdx_eq_map_add]
            apply List.mem_map.mpr
            refine ⟨((parentStart, (headerTemplateCoordinate header).clauseIndex),
              (headerTemplateCoordinate header).clauseIndex), ?_, rfl⟩
            apply List.mk_mem_zipIdx_iff_getElem?.mpr
            simp [indexLt]
          · apply List.mem_append_right
            simpa only [List.length_map, List.length_range] using
              induction (parentStart + 1)
                (generatedStart + generatedClauseCount profile)
                tailTables.tail tailMember

/-- Given equality of complete metadata keys, every occurrence retrieves
metadata with its own original parent and local generated-clause index. -/
theorem sourceOccurrences_metadataLookup
    {Metadata : Type}
    (source : List FormulaShapeDirectionOrdering.Token)
    (tailTables : List (List (List AxisDirection)))
    (metadata : List Metadata) (key : Metadata → Nat × Nat)
    (keysEq : metadata.map key = sourceMetadataKeysFrom 0 source)
    (occurrence : SourceOccurrence)
    (member : occurrence ∈ sourceOccurrences source tailTables) :
    ∃ selected,
      metadata[occurrence.generatedClauseIndex]? = some selected ∧
      key selected = occurrence.metadataKey := by
  have keyMember := sourceOccurrencesFrom_metadataKey_mem
    0 0 source tailTables occurrence member
  have lookup := List.mk_mem_zipIdx_iff_getElem?.mp keyMember
  rw [← keysEq, List.getElem?_map] at lookup
  exact Option.map_eq_some_iff.mp lookup

end LeanTrominoes.PeriodicCNF.FormulaShapeFigureNinePolarityRouteTail

namespace LeanTrominoes.PlanarOneInThreeNoUnitsFigureNine

open PeriodicCNF
open PeriodicCNF.ClauseProfileOccurrenceSplit
open PeriodicCNF.FormulaShapeOfFormula
open PeriodicCNF.FormulaShapeFigureNinePolarityRouteTail

theorem clauseMetadataFor_map_key
    {Variable : Type} [DecidableEq Variable]
    (parent figureNineStart : Nat) (clause : PositionedPeriodicClause Variable)
    (nonempty : clause.literals ≠ []) (width : clause.literals.length ≤ 3) :
    (clauseMetadataFor parent figureNineStart clause).map ClauseMetadata.key =
      (List.range (templateDrawingOfClauseProfile
        (clauseProfile (literalProfiles clause.literals))).formula.length).map
          fun localIndex => (parent, localIndex) := by
  have lengthEq := unitEliminationClausesFrom_length_eq_template
    parent figureNineStart clause nonempty width
  unfold clauseMetadataFor
  apply List.ext_getElem
  · simpa only [List.length_map, List.length_zipIdx, List.length_range]
      using lengthEq
  · intro index leftLt rightLt
    simp only [List.getElem_map, List.getElem_zipIdx, List.getElem_range,
      ClauseMetadata.key, Nat.zero_add]

private theorem formulaClauseMetadataFrom_map_key
    {Variable : Type} [DecidableEq Variable]
    (parent figureNineStart : Nat)
    (clauses : List (PositionedPeriodicClause Variable))
    (nonempty : ∀ clause ∈ clauses, clause.literals ≠ [])
    (width : ∀ clause ∈ clauses, clause.literals.length ≤ 3) :
    (formulaClauseMetadataFrom parent figureNineStart clauses).map ClauseMetadata.key =
      profileMetadataKeysFrom parent
        (clauses.map fun clause => clauseProfile (literalProfiles clause.literals)) := by
  induction clauses generalizing parent figureNineStart with
  | nil => rfl
  | cons clause clauses induction =>
      rw [formulaClauseMetadataFrom, List.map_append,
        clauseMetadataFor_map_key parent figureNineStart clause
          (nonempty clause (by simp)) (width clause (by simp))]
      rw [induction (parent + 1) _
        (by intro later member; exact nonempty later (by simp [member]))
        (by intro later member; exact width later (by simp [member]))]
      rfl

/-- The full key projection retains original source-clause identities, not
just the finite profiles of their generated clauses. -/
theorem formulaClauseMetadata_map_key
    {Variable : Type} [DecidableEq Variable]
    (source : PositionedPeriodicCNF Variable)
    (nonempty : ∀ clause ∈ source.clauses, clause.literals ≠ [])
    (width : source.erase.WidthAtMost 3) :
    (formulaClauseMetadata source).map ClauseMetadata.key =
      profileMetadataKeysFrom 0
        (source.clauses.map fun clause =>
          clauseProfile (literalProfiles clause.literals)) := by
  apply formulaClauseMetadataFrom_map_key 0 0 source.clauses nonempty
  intro clause member
  exact width clause.literals (List.mem_map.mpr ⟨clause, member, rfl⟩)

end LeanTrominoes.PlanarOneInThreeNoUnitsFigureNine

namespace LeanTrominoes.PeriodicCNF.FormulaShapeRetainedFigureNineDirection

open FormulaShapeFigureNinePolarityRouteTail
open PeriodicOrthocrossing
open PlanarOneInThreeNoUnitsFigureNine

/-- The retained metadata and occurrence streams share the complete parent
key schedule. No injectivity assumption on clause profiles is needed. -/
theorem metadata_map_key_eq_sourceMetadataKeys
    {Variable : Type} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (width : source.WidthAtMost 3)
    (nonempty : ∀ clause ∈ source.clauses, clause ≠ []) :
    (formulaClauseMetadata
      (retainedFigureNineClearancePositionedFormula source)).map ClauseMetadata.key =
      sourceMetadataKeysFrom 0 (descriptors source) := by
  rw [formulaClauseMetadata_map_key _
    (retainedFigureNineClearancePositionedFormula_clausesNonempty source nonempty)
    (retainedFigureNineClearancePositionedFormula_widthAtMostThree source width)]
  rw [sourceMetadataKeysFrom_eq_profiles]
  change _ = profileMetadataKeysFrom 0 (FormulaShape.clauseProfiles (shape source))
  rw [shape_eq_sourceShape source width nonempty,
    FormulaShapeRetainedFigureNineSource.clauseProfiles_shape,
    FormulaShapeOfFormula.profiles_erase]

end LeanTrominoes.PeriodicCNF.FormulaShapeRetainedFigureNineDirection

namespace LeanTrominoes.PeriodicCNF.FormulaShapeRetainedFigureNineSourceTail

open FormulaShapeFigureNinePolarityRouteTail
open FormulaShapeFigureNinePolarityRouteHeader
open FormulaShapeFigureNineSourceTail
open FormulaShapeDirectionOrdering
open PeriodicOrthocrossing
open PlanarOneInThreeNoUnitsFigureNine

/-- Proof-side occurrences of the retained source, with both original and
generated clause indices. -/
def occurrences {Variable : Type} [DecidableEq Variable]
    (source : PeriodicCNF Variable) : List SourceOccurrence :=
  sourceOccurrences (FormulaShapeRetainedFigureNineDirection.descriptors source)
    (tailTables source)

/-- A single witness ties the geometric metadata and direct header/tail to
the same original source clause. -/
structure OccurrenceWitness {Variable : Type} [DecidableEq Variable]
    (source : PeriodicCNF Variable) (occurrence : SourceOccurrence) where
  refinedClause : PositionedPeriodicClause (PeriodicPlanarThreeSATThreeVariable Variable)
  metadata : ClauseMetadata (PeriodicPlanarThreeSATThreeVariable Variable)
  sourceLookup :
    (retainedDrawingSourceScaledRefinedEightOccurrenceSplitPositionedFormula source).clauses[
      occurrence.parentClauseIndex]? = some refinedClause
  metadataLookup :
    (formulaClauseMetadata (retainedFigureNineClearancePositionedFormula source))[
      occurrence.generatedClauseIndex]? = some metadata
  metadataKey : metadata.key = occurrence.metadataKey
  profileEq : occurrence.profile = DirectedClauseProfile.ofClause
    (retainedDrawingSourceScaledNormalizedEightOccurrenceSplitIncidenceRoutes source)
    occurrence.parentClauseIndex refinedClause
  tailsEq : occurrence.orderedTails = orderedTailDirections
    (retainedDrawingSourceScaledNormalizedEightOccurrenceSplitIncidenceRoutes source)
    occurrence.parentClauseIndex refinedClause
  headerMember : occurrence.header ∈ sourceClauseHeaders occurrence.profile
  metadataSource : metadata.sourceClause =
    (PositionedPeriodicCNF.orderClauseByRouteDirection
      (retainedDrawingSourceScaledNormalizedEightOccurrenceSplitIncidenceRoutes source)
      occurrence.parentClauseIndex refinedClause).scale
        retainedFigureNineSourceClearanceFactor
  refinedNonempty : refinedClause.literals ≠ []
  refinedWidth : refinedClause.literals.length ≤ 3

private theorem clause_width_of_mem
    {Variable : Type} (formula : PositionedPeriodicCNF Variable)
    (width : formula.erase.WidthAtMost 3)
    {clause : PositionedPeriodicClause Variable} (member : clause ∈ formula.clauses) :
    clause.literals.length ≤ 3 :=
  width _ (List.mem_map.mpr ⟨clause, member, rfl⟩)

/-- The old profile and literal-coordinate projections follow from the
complete witness, without reconstructing a separate metadata witness. -/
theorem OccurrenceWitness.metadataCoordinates
    {Variable : Type} [DecidableEq Variable]
    {source : PeriodicCNF Variable} {occurrence : SourceOccurrence}
    (witness : OccurrenceWitness source occurrence) :
    let coordinate := FormulaShapeFigureNineRoutePrefix.headerTemplateProfileCoordinate
      occurrence.header
    coordinate.profile = witness.metadata.parentProfileCoordinate.profile ∧
    coordinate.coordinate.clauseIndex = witness.metadata.localClauseIndex ∧
    coordinate.coordinate.literalIndex =
      (FormulaShapeFigureNineFinalClauseOrdering.reorderList
        (List.range witness.metadata.parentProfileCoordinate.literalCount)).getD
          coordinate.coordinate.polarity.sourceLiteralIndex 0 ∧
    coordinate.coordinate.polarity.sourceLiteralIndex <
      witness.metadata.parentProfileCoordinate.literalCount := by
  obtain ⟨profileEq, literalEq, literalLt⟩ :=
    header_coordinate_invariants occurrence.profile occurrence.header witness.headerMember
  have profileSemantic :=
    FormulaShapeFigureNineRoutePrefix.clauseProfile_orderedDirectedProfile_ofClause
      (retainedDrawingSourceScaledNormalizedEightOccurrenceSplitIncidenceRoutes source)
      occurrence.parentClauseIndex witness.refinedClause
      witness.refinedNonempty witness.refinedWidth
  rw [witness.profileEq, profileSemantic] at profileEq
  have metadataProfile :
      (FormulaShapeFigureNineRoutePrefix.headerTemplateProfileCoordinate
        occurrence.header).profile = witness.metadata.parentProfileCoordinate.profile := by
    simpa only [ClauseMetadata.parentProfileCoordinate, witness.metadataSource,
      PositionedPeriodicClause.scale_literals] using profileEq
  have clauseEq :
      (FormulaShapeFigureNineRoutePrefix.headerTemplateProfileCoordinate
        occurrence.header).coordinate.clauseIndex = witness.metadata.localClauseIndex :=
    (congrArg Prod.snd witness.metadataKey).symm
  refine ⟨metadataProfile, clauseEq, ?_, ?_⟩
  · simpa only [metadataProfile, clauseEq, ClauseMetadata.parentProfileCoordinate]
      using literalEq
  · simpa only [metadataProfile, clauseEq, ClauseMetadata.parentProfileCoordinate]
      using literalLt

/-- An inherited occurrence's dynamic tail is the canonical route tail at
the original parent named by its metadata, even when other parents have the
same finite profile. -/
theorem OccurrenceWitness.inheritedTail
    {Variable : Type} [DecidableEq Variable]
    {source : PeriodicCNF Variable} {occurrence : SourceOccurrence}
    (witness : OccurrenceWitness source occurrence)
    (slot : ClauseProfilePolarityRouteOperation.SourceLiteralSlot)
    (query : LocalExtendedDirectionQuery)
    (prefixEq : occurrence.header.figurePrefix = .inherited slot query) :
    occurrence.pair.2 = Gadget.unitSubdivisionDirections
      (retainedDrawingSourceScaledClockwiseEightOccurrenceSplitIncidenceRoutes source
        witness.metadata.sourceClauseIndex
        (FormulaShapeFigureNinePolarityRouteHeader.sourceSlotNat slot)).tail := by
  have headerMember := witness.headerMember
  rw [witness.profileEq] at headerMember
  obtain ⟨index, descriptorEq⟩ :=
    exists_descriptorAt_eq_figurePrefix_of_mem_sourceClauseHeaders
      _ occurrence.header headerMember
  have selected := selectedTailDirections_descriptorAt_inherited_eq_canonicalRoute
    (retainedDrawingSourceScaledRefinedEightOccurrenceSplitPositionedFormula source)
    (retainedDrawingSourceScaledRefinedEightOccurrenceSplitPlacement source)
    (retainedDrawingSourceScaledNormalizedEightOccurrenceSplitIncidenceRoutes source)
    occurrence.parentClauseIndex witness.refinedClause witness.sourceLookup
    witness.refinedNonempty witness.refinedWidth occurrence.header.polarity index slot query
    (descriptorEq.trans prefixEq)
  have parentEq : witness.metadata.sourceClauseIndex = occurrence.parentClauseIndex :=
    congrArg Prod.fst witness.metadataKey
  rw [parentEq]
  change selectedTailDirections occurrence.orderedTails occurrence.header = _
  rw [witness.tailsEq]
  simpa only [descriptorEq,
    retainedDrawingSourceScaledClockwiseEightOccurrenceSplitIncidenceRoutes] using selected

/-- Construct the complete witness directly from stream membership. -/
theorem occurrenceWitness
    {Variable : Type} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (width : source.WidthAtMost 3)
    (nonempty : ∀ clause ∈ source.clauses, clause ≠ [])
    (occurrence : SourceOccurrence) (member : occurrence ∈ occurrences source) :
    Nonempty (OccurrenceWitness source occurrence) := by
  obtain ⟨refinedClause, sourceLookup, profileEq, tailsEq, headerMember⟩ :=
    sourceOccurrences_ofFormula_provenance
      (retainedDrawingSourceScaledRefinedEightOccurrenceSplitPositionedFormula source)
      (retainedDrawingSourceScaledNormalizedEightOccurrenceSplitIncidenceRoutes source)
      occurrence (by
        simpa only [occurrences, FormulaShapeRetainedFigureNineDirection.descriptors,
          tailTables] using member)
  obtain ⟨metadata, metadataLookup, metadataKey⟩ :=
    sourceOccurrences_metadataLookup
      (FormulaShapeRetainedFigureNineDirection.descriptors source)
      (tailTables source)
      (formulaClauseMetadata (retainedFigureNineClearancePositionedFormula source))
      ClauseMetadata.key
      (FormulaShapeRetainedFigureNineDirection.metadata_map_key_eq_sourceMetadataKeys
        source width nonempty) occurrence member
  have refinedMember := List.mk_mem_zipIdx_iff_getElem?.mpr sourceLookup
  let clockwiseClause := PositionedPeriodicCNF.orderClauseByRouteDirection
    (retainedDrawingSourceScaledNormalizedEightOccurrenceSplitIncidenceRoutes source)
    occurrence.parentClauseIndex refinedClause
  have clockwiseMember :
      (clockwiseClause, occurrence.parentClauseIndex) ∈
        (retainedDrawingSourceScaledClockwiseEightOccurrenceSplitPositionedFormula
          source).clauses.zipIdx :=
    PositionedPeriodicCNF.orderClauseByRouteDirection_mem _ refinedMember
  have clearanceMember :
      (clockwiseClause.scale retainedFigureNineSourceClearanceFactor,
        occurrence.parentClauseIndex) ∈
          (retainedFigureNineClearancePositionedFormula source).clauses.zipIdx := by
    rw [retainedFigureNineClearancePositionedFormula,
      PositionedPeriodicCNF.scale_clauses, List.zipIdx_map]
    exact List.mem_map.mpr ⟨(clockwiseClause, occurrence.parentClauseIndex),
      clockwiseMember, rfl⟩
  have metadataMember := List.mem_iff_getElem?.mpr
    ⟨occurrence.generatedClauseIndex, metadataLookup⟩
  have metadataValid := formulaClauseMetadata_valid
    (retainedFigureNineClearancePositionedFormula source) metadataMember
  have parentEq : metadata.sourceClauseIndex = occurrence.parentClauseIndex :=
    congrArg Prod.fst metadataKey
  have metadataSourceLookup := List.mk_mem_zipIdx_iff_getElem?.mp metadataValid.1
  rw [parentEq] at metadataSourceLookup
  have sourceEq := Option.some.inj (metadataSourceLookup.symm.trans
    (List.mk_mem_zipIdx_iff_getElem?.mp clearanceMember))
  have sourceMember := List.fst_mem_of_mem_zipIdx refinedMember
  have refinedNonempty :=
    retainedDrawingSourceScaledRefinedEightOccurrenceSplitPositionedFormula_clausesNonempty
      source nonempty refinedClause sourceMember
  have refinedWidth := clause_width_of_mem _
    (retainedDrawingSourceScaledRefinedEightOccurrenceSplitPositionedFormula_widthAtMostThree
      source width) sourceMember
  exact ⟨⟨refinedClause, metadata, sourceLookup, metadataLookup, metadataKey,
    profileEq, tailsEq, headerMember, sourceEq, refinedNonempty, refinedWidth⟩⟩

end LeanTrominoes.PeriodicCNF.FormulaShapeRetainedFigureNineSourceTail
