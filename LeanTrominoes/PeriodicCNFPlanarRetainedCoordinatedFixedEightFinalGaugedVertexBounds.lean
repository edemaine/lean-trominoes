import LeanTrominoes.PeriodicCNFPlanarRetainedCoordinatedFixedEightFigureNineClearanceVertexBounds
import LeanTrominoes.PeriodicCNFPlanarRetainedCoordinatedFixedEightFinalGaugedVertexSeparation
import LeanTrominoes.PeriodicMacrocellOrbitGeometry

/-!
# Fundamental-square bounds for final gauged Figure 9 vertices

The raw two-stage exact-one construction records every variable and clause
as a periodic representative of a finite `72 × 72` local address over a
clearance-source vertex.  The clearance vertices are strictly bounded, so
their natural refined representatives are strictly bounded as well.  This
module transports those bounds through the final canonical variable gauge.
-/

namespace LeanTrominoes
namespace PeriodicOrthocrossing

set_option maxHeartbeats 3000000

local instance finalGaugedVertexBoundsDecidableEq
    {Variable : Type*} [DecidableEq Variable] :
    DecidableEq
      (OneInThreeNoUnitVariable
        (PeriodicPlanarOneInThreeThreeRawVariable Variable)) :=
  PlanarOneInThreeNoUnitsFigureNine.nestedVariableDecidableEq

/-- A composed literal that is local to either exact-one replacement layer
has its actual physical occurrence at the natural point of its finite
`72 × 72` macrocell address.  That point lies strictly inside the final
fundamental square. -/
theorem retainedOrderedFixedEightComposedRawLocalLiteralPosition_inSquare
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (sourceLocal : source.IsLocal)
    (sourceWidth : source.WidthAtMost 3)
    (sourceOccurrences : source.OccurrencesAtMost 3)
    (sourceClausesNonempty :
      ∀ clause ∈ source.clauses, clause ≠ [])
    {clause :
      PositionedPeriodicClause
        (OneInThreeNoUnitVariable
          (PeriodicPlanarOneInThreeThreeRawVariable Variable))}
    {clauseIndex : Nat}
    (clauseMember :
      (clause, clauseIndex) ∈
        (retainedOrderedFixedEightPositionedPeriodicPlanarOneInThreeNoUnitsComposedRawFormula
          source).clauses.zipIdx)
    {literal :
      PeriodicLiteral
        (OneInThreeNoUnitVariable
          (PeriodicPlanarOneInThreeThreeRawVariable Variable))}
    {literalIndex : Nat}
    (literalMember :
      (literal, literalIndex) ∈ clause.literals.zipIdx)
    (localLiteral :
      ∀ sourceAtom : PeriodicPlanarThreeSATThreeVariable Variable,
        literal.atom ≠ .inl (.inl sourceAtom)) :
    let placement :=
      retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsComposedRawPlacement
        source
    0 < (placement.literalPosition literal).1 ∧
      (placement.literalPosition literal).1 < placement.period ∧
      0 < (placement.literalPosition literal).2 ∧
      (placement.literalPosition literal).2 < placement.period := by
  dsimp only
  rcases composedLiteralVariable_inMacrocellOrbit
      (retainedFigureNineClearancePositionedFormula source)
      (retainedFigureNineClearancePlacement source)
      (by simpa only [
        retainedOrderedFixedEightPositionedPeriodicPlanarOneInThreeNoUnitsComposedRawFormula]
        using clauseMember)
    literalMember with
    ⟨base, address, sourceData, _orbit, localPosition⟩
  have localPositionEq :
      (retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsComposedRawPlacement
          source).literalPosition literal =
        Cell.macrocellPosition finalFigureNineMacrocellScale
          base address.position := by
    simpa only [
      retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsComposedRawPlacement]
      using localPosition localLiteral
  clear localPosition localLiteral
  have baseInside :
      0 < base.1 ∧
        base.1 < (retainedFigureNineClearancePlacement source).period ∧
      0 < base.2 ∧
        base.2 < (retainedFigureNineClearancePlacement source).period := by
    generalize atomEq : literal.atom = atom at sourceData
    cases sourceData with
    | inherited sourceAtom sourceAtomMember =>
        exact retainedFigureNineClearancePlacement_position_inSquare_of_mem
          source sourceAtom sourceAtomMember
    | figureNineAuxiliary sourceClause sourceClauseIndex
        sourceClauseMember kind =>
        exact retainedFigureNineClearanceStoredClausePosition_inSquare_of_mem
          source sourceLocal sourceWidth sourceOccurrences
          sourceClausesNonempty sourceClause
          (List.fst_mem_of_mem_zipIdx sourceClauseMember)
    | unitEliminationAuxiliary sourceClause sourceClauseIndex
        sourceClauseMember figureNineClause figureNineClauseIndex
        localFigureNineClauseIndex localFigureNineClauseMember
        figureNineClauseMember figureNineMetadataLookup kind =>
        exact retainedFigureNineClearanceStoredClausePosition_inSquare_of_mem
          source sourceLocal sourceWidth sourceOccurrences
          sourceClausesNonempty sourceClause
          (List.fst_mem_of_mem_zipIdx sourceClauseMember)
  have naturalInside :=
    Cell.macrocellPosition_halfOpen_in_refined_square
      (factor := finalFigureNineMacrocellScale)
      (period := (retainedFigureNineClearancePlacement source).period)
      (by native_decide) baseInside
      (finalFigureNineLocalAddress_position_halfOpen address)
  rw [localPositionEq]
  have periodEq :
      (retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsComposedRawPlacement
        source).period =
        finalFigureNineMacrocellScale *
          (retainedFigureNineClearancePlacement source).period := by
    simp [retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsComposedRawPlacement,
      PlanarOneInThreeNoUnitsFigureNine.composedPlacement,
      PeriodicOneInThreeNoUnitsPositioned.placement,
      PeriodicOneInThreePositioned.placement,
      finalFigureNineMacrocellScale,
      PeriodicOneInThreeNoUnitsPositioned.gadgetScale,
      PlanarOneInThree.gadgetScale]
    omega
  rw [periodEq]
  simpa only [Nat.cast_mul] using naturalInside

/-- The coordinate residue of every genuine raw composed variable is the
natural bounded point selected by its finite Figure 9 macrocell address. -/
theorem retainedOrderedFixedEightComposedRawVariablePosition_residue_inSquare
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (sourceLocal : source.IsLocal)
    (sourceWidth : source.WidthAtMost 3)
    (sourceOccurrences : source.OccurrencesAtMost 3)
    (sourceClausesNonempty :
      ∀ clause ∈ source.clauses, clause ≠ [])
    (atom :
      OneInThreeNoUnitVariable
        (PeriodicPlanarOneInThreeThreeRawVariable Variable))
    (atomMember :
      atom ∈
        (retainedOrderedFixedEightPositionedPeriodicPlanarOneInThreeNoUnitsComposedRawFormula
          source).erase.variableOccurrences) :
    let placement :=
      retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsComposedRawPlacement
        source
    0 < (placement.position atom).1 % placement.period ∧
      (placement.position atom).1 % placement.period < placement.period ∧
      0 < (placement.position atom).2 % placement.period ∧
      (placement.position atom).2 % placement.period < placement.period := by
  dsimp only
  rcases retainedOrderedFixedEightComposedRawVariableOccurrence_inMacrocellOrbit
      source atomMember with
    ⟨base, address, sourceData, orbit⟩
  have baseInside :
      0 < base.1 ∧
        base.1 < (retainedFigureNineClearancePlacement source).period ∧
      0 < base.2 ∧
        base.2 < (retainedFigureNineClearancePlacement source).period := by
    cases sourceData with
    | inherited sourceAtom sourceAtomMember =>
        exact retainedFigureNineClearancePlacement_position_inSquare_of_mem
          source sourceAtom sourceAtomMember
    | figureNineAuxiliary sourceClause sourceClauseIndex
        sourceClauseMember kind =>
        exact retainedFigureNineClearanceStoredClausePosition_inSquare_of_mem
          source sourceLocal sourceWidth sourceOccurrences
          sourceClausesNonempty sourceClause
          (List.fst_mem_of_mem_zipIdx sourceClauseMember)
    | unitEliminationAuxiliary sourceClause sourceClauseIndex
        sourceClauseMember figureNineClause figureNineClauseIndex
        localFigureNineClauseIndex localFigureNineClauseMember
        figureNineClauseMember figureNineMetadataLookup kind =>
        exact retainedFigureNineClearanceStoredClausePosition_inSquare_of_mem
          source sourceLocal sourceWidth sourceOccurrences
          sourceClausesNonempty sourceClause
          (List.fst_mem_of_mem_zipIdx sourceClauseMember)
  have localInside :=
    finalFigureNineLocalAddress_position_halfOpen address
  have naturalInside :=
    Cell.macrocellPosition_halfOpen_in_refined_square
      (factor := finalFigureNineMacrocellScale)
      (period := (retainedFigureNineClearancePlacement source).period)
      (by native_decide) baseInside localInside
  have residueEq :=
    Cell.inMacrocellOrbit_residue_eq_macrocellPosition
      (factor := finalFigureNineMacrocellScale)
      (period := (retainedFigureNineClearancePlacement source).period)
      (by native_decide) baseInside localInside orbit
  have periodEq :
      (retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsComposedRawPlacement
        source).period =
        finalFigureNineMacrocellScale *
          (retainedFigureNineClearancePlacement source).period := by
    simp [retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsComposedRawPlacement,
      PlanarOneInThreeNoUnitsFigureNine.composedPlacement,
      PeriodicOneInThreeNoUnitsPositioned.placement,
      PeriodicOneInThreePositioned.placement,
      finalFigureNineMacrocellScale,
      PeriodicOneInThreeNoUnitsPositioned.gadgetScale,
      PlanarOneInThree.gadgetScale]
    omega
  rw [periodEq]
  simp only [Nat.cast_mul]
  have residueX :
      ((retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsComposedRawPlacement
        source).position atom).1 %
          (finalFigureNineMacrocellScale *
            (retainedFigureNineClearancePlacement source).period) =
        (Cell.macrocellPosition finalFigureNineMacrocellScale
          base address.position).1 :=
    congrArg Prod.fst residueEq
  have residueY :
      ((retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsComposedRawPlacement
        source).position atom).2 %
          (finalFigureNineMacrocellScale *
            (retainedFigureNineClearancePlacement source).period) =
        (Cell.macrocellPosition finalFigureNineMacrocellScale
          base address.position).2 :=
    congrArg Prod.snd residueEq
  rw [residueX, residueY]
  exact naturalInside

/-- Every genuine final variable vertex lies strictly inside the final
fundamental square after canonical quotient gauging. -/
theorem retainedOrderedFixedEightFinalGaugedVariablePosition_inSquare_of_mem
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (sourceLocal : source.IsLocal)
    (sourceWidth : source.WidthAtMost 3)
    (sourceOccurrences : source.OccurrencesAtMost 3)
    (sourceClausesNonempty :
      ∀ clause ∈ source.clauses, clause ≠ [])
    (atom :
      OneInThreeNoUnitVariable
        (PeriodicPlanarOneInThreeThreeRawVariable Variable))
    (atomMember :
      atom ∈
        (retainedOrderedFixedEightPositionedPeriodicPlanarOneInThreeNoUnitsFinalGaugedFormula
          source sourceLocal sourceWidth sourceOccurrences
          sourceClausesNonempty).erase.variableOccurrences) :
    0 <
        ((retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsFinalGaugedPlacement
          source).position atom).1 ∧
      ((retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsFinalGaugedPlacement
          source).position atom).1 <
        (retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsFinalGaugedPlacement
          source).period ∧
      0 <
        ((retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsFinalGaugedPlacement
          source).position atom).2 ∧
      ((retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsFinalGaugedPlacement
          source).position atom).2 <
        (retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsFinalGaugedPlacement
          source).period := by
  let rawPlacement :=
    retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsComposedRawPlacement
      source
  have rawMember :=
    finalGaugedVariableOccurrence_mem_composedRaw
      source sourceLocal sourceWidth sourceOccurrences
      sourceClausesNonempty atomMember
  have residueInside :=
    retainedOrderedFixedEightComposedRawVariablePosition_residue_inSquare
      source sourceLocal sourceWidth sourceOccurrences
      sourceClausesNonempty atom rawMember
  have gaugedInside :=
    PeriodicVariablePlacement.variableGauge_canonicalPositionGauge_position_inSquare
      rawPlacement
      (by
        simpa only [rawPlacement] using
          retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsComposedRawPlacement_period_pos
            source)
      atom (ne_of_gt residueInside.1)
      (ne_of_gt residueInside.2.2.1)
  simpa only [rawPlacement,
    retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsFinalGaugedPlacement,
    retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsFinalGauge,
    PeriodicVariablePlacement.variableGauge_period] using gaugedInside

/-- Exact clause provenance identifies the stored raw clause position with
the natural point of its finite two-stage macrocell address. -/
theorem FinalFigureNineClauseSource.position_eq_macrocellPosition
    {Variable : Type*}
    {source : PositionedPeriodicCNF Variable}
    {clause :
      PositionedPeriodicClause
        (OneInThreeNoUnitVariable (OneInThreeVariable Variable))}
    {clauseIndex : Nat} {base : Cell}
    {address : FinalFigureNineLocalAddress}
    (sourceData :
      FinalFigureNineClauseSource source clause clauseIndex base address) :
    clause.position =
      Cell.macrocellPosition finalFigureNineMacrocellScale
        base address.position := by
  cases sourceData with
  | generated sourceClause sourceClauseIndex sourceClauseMember
      figureNineClauseStart localFinalClauseIndex finalClause
      finalClauseIndex composedMetadataLookup figureNineClause
      figureNineClauseIndex localFigureNineClauseIndex
      localFigureNineClauseMember figureNineMetadataLookup
      unitClauseIndex unitClauseMember unitMetadataLookup =>
      have figureNinePosition :=
        PeriodicOneInThreePositioned.clauseGadget_position_eq_generatedClausePosition
          sourceClauseIndex sourceClause localFigureNineClauseMember
      have finalPosition :=
        PeriodicOneInThreeNoUnitsPositioned.clauseGadget_position_eq_generatedClausePosition
          figureNineClauseIndex figureNineClause unitClauseMember
      let figureNineLocal :=
        PeriodicOneInThreePositioned.generatedClauseLocalPosition
          localFigureNineClauseIndex.val
      let unitLocal :=
        PeriodicOneInThreeNoUnitsPositioned.generatedClauseLocalPosition
          figureNineClause.literals unitClauseIndex
      have figureNineMacrocell :
          figureNineClause.position =
            Cell.macrocellPosition 12 sourceClause.position
              figureNineLocal := by
        rw [figureNinePosition]
        exact
          PeriodicOneInThreePositioned.generatedClausePosition_eq_macrocellPosition
            sourceClause.position localFigureNineClauseIndex.val
      have finalMacrocell :
          clause.position =
            Cell.macrocellPosition 6 figureNineClause.position
              unitLocal := by
        rw [finalPosition]
        exact
          PeriodicOneInThreeNoUnitsPositioned.generatedClausePosition_eq_macrocellPosition
            figureNineClause unitClauseIndex
      rw [finalMacrocell, figureNineMacrocell]
      have composedMacrocell :
          Cell.macrocellPosition 6
              (Cell.macrocellPosition 12 sourceClause.position figureNineLocal)
              unitLocal =
            Cell.macrocellPosition 72 sourceClause.position
              (Cell.add (Cell.scale 6 figureNineLocal) unitLocal) := by
        apply Prod.ext <;>
          simp [Cell.macrocellPosition, Cell.add, Cell.scale] <;>
          ring
      rw [composedMacrocell]
      congr 1
      simp [figureNineLocal, unitLocal,
        FinalFigureNineLocalAddress.position,
        finalFigureNineClauseLocalPosition,
        finalUnitClauseLocal_position,
        PeriodicOneInThreeNoUnitsPositioned.gadgetScale,
        PeriodicOneInThreePositioned.generatedClauseLocalPosition]

/-- Every genuine raw composed stored clause lies strictly inside the final
physical fundamental square. -/
theorem retainedOrderedFixedEightComposedRawStoredClausePosition_inSquare_of_mem
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (sourceLocal : source.IsLocal)
    (sourceWidth : source.WidthAtMost 3)
    (sourceOccurrences : source.OccurrencesAtMost 3)
    (sourceClausesNonempty :
      ∀ clause ∈ source.clauses, clause ≠ [])
    (clause :
      PositionedPeriodicClause
        (OneInThreeNoUnitVariable
          (PeriodicPlanarOneInThreeThreeRawVariable Variable)))
    (clauseIndex : Nat)
    (clauseMember :
      (clause, clauseIndex) ∈
        (retainedOrderedFixedEightPositionedPeriodicPlanarOneInThreeNoUnitsComposedRawFormula
          source).clauses.zipIdx) :
    0 < clause.position.1 ∧
      clause.position.1 <
        (retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsComposedRawPlacement
          source).period ∧
      0 < clause.position.2 ∧
      clause.position.2 <
        (retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsComposedRawPlacement
          source).period := by
  rcases retainedOrderedFixedEightComposedRawClause_inMacrocellOrbit_withSource
      source clauseMember with
    ⟨base, address, sourceData, _orbit⟩
  have baseInside :
      0 < base.1 ∧
        base.1 < (retainedFigureNineClearancePlacement source).period ∧
      0 < base.2 ∧
        base.2 < (retainedFigureNineClearancePlacement source).period := by
    cases sourceData with
    | generated sourceClause sourceClauseIndex sourceClauseMember
        figureNineClauseStart localFinalClauseIndex finalClause
        finalClauseIndex composedMetadataLookup figureNineClause
        figureNineClauseIndex localFigureNineClauseIndex
        localFigureNineClauseMember figureNineMetadataLookup
        unitClauseIndex unitClauseMember unitMetadataLookup =>
        exact retainedFigureNineClearanceStoredClausePosition_inSquare_of_mem
          source sourceLocal sourceWidth sourceOccurrences
          sourceClausesNonempty sourceClause
          (List.fst_mem_of_mem_zipIdx sourceClauseMember)
  have naturalInside :=
    Cell.macrocellPosition_halfOpen_in_refined_square
      (factor := finalFigureNineMacrocellScale)
      (period := (retainedFigureNineClearancePlacement source).period)
      (by native_decide) baseInside
      (finalFigureNineLocalAddress_position_halfOpen address)
  rw [FinalFigureNineClauseSource.position_eq_macrocellPosition sourceData]
  have periodEq :
      (retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsComposedRawPlacement
        source).period =
        finalFigureNineMacrocellScale *
          (retainedFigureNineClearancePlacement source).period := by
    simp [retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsComposedRawPlacement,
      PlanarOneInThreeNoUnitsFigureNine.composedPlacement,
      PeriodicOneInThreeNoUnitsPositioned.placement,
      PeriodicOneInThreePositioned.placement,
      finalFigureNineMacrocellScale,
      PeriodicOneInThreeNoUnitsPositioned.gadgetScale,
      PlanarOneInThree.gadgetScale]
    omega
  rw [periodEq]
  simpa only [Nat.cast_mul] using naturalInside

end PeriodicOrthocrossing
end LeanTrominoes
