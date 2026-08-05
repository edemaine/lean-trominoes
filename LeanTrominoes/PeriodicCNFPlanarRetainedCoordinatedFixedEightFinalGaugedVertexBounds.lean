import LeanTrominoes.PeriodicCNFPlanarRetainedCoordinatedFixedEightFigureNineClearanceVertexBounds
import LeanTrominoes.PeriodicCNFPlanarRetainedCoordinatedFixedEightFinalGaugedVertexSeparation
import LeanTrominoes.PeriodicCNFPlanarRetainedCoordinatedFixedEightOrderedFigureNineSemantics
import LeanTrominoes.PeriodicMacrocellOrbitGeometry
import LeanTrominoes.PositionedPeriodicCNFVariableGaugeClauseMembership

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

/-- If both a literal occurrence and its canonically gauged variable
representative lie in the same strict fundamental square, their difference
cannot be a nonzero whole-period translation. -/
theorem PeriodicVariablePlacement.canonicalPositionGauge_literalOffset_eq_zero
    {Variable : Type*}
    (placement : PeriodicVariablePlacement Variable)
    (periodPositive : 0 < placement.period)
    (literal : PeriodicLiteral Variable)
    (gaugedPositionInside :
      0 < ((placement.variableGauge
          placement.canonicalPositionGauge).position literal.atom).1 ∧
        ((placement.variableGauge
            placement.canonicalPositionGauge).position literal.atom).1 <
          placement.period ∧
        0 < ((placement.variableGauge
          placement.canonicalPositionGauge).position literal.atom).2 ∧
        ((placement.variableGauge
            placement.canonicalPositionGauge).position literal.atom).2 <
          placement.period)
    (literalPositionInside :
      0 < (placement.literalPosition literal).1 ∧
        (placement.literalPosition literal).1 < placement.period ∧
        0 < (placement.literalPosition literal).2 ∧
        (placement.literalPosition literal).2 < placement.period) :
    (literal.variableGauge placement.canonicalPositionGauge).offset =
      (0, 0) := by
  have invariant :=
    PeriodicVariablePlacement.variableGauge_literalPosition
      placement placement.canonicalPositionGauge literal
  cases gaugedPositionEq :
      (placement.variableGauge
        placement.canonicalPositionGauge).position literal.atom with
  | mk variableX variableY =>
      cases literalPositionEq : placement.literalPosition literal with
      | mk literalX literalY =>
          cases gaugedOffsetEq :
              (literal.variableGauge
                placement.canonicalPositionGauge).offset with
          | mk offsetX offsetY =>
              rw [literalPositionEq] at invariant
              simp only [PeriodicVariablePlacement.literalPosition,
                PeriodicLiteral.variableGauge_atom] at invariant
              rw [gaugedPositionEq, gaugedOffsetEq] at invariant
              have horizontal :
                  variableX + (placement.period : Int) * offsetX =
                    literalX := by
                simpa [
                  PeriodicVariablePlacement.translation,
                  Cell.add, Cell.scale] using
                    congrArg Prod.fst invariant
              have vertical :
                  variableY + (placement.period : Int) * offsetY =
                    literalY := by
                simpa [
                  PeriodicVariablePlacement.translation,
                  Cell.add, Cell.scale] using
                    congrArg Prod.snd invariant
              simp only [gaugedPositionEq] at gaugedPositionInside
              simp only [literalPositionEq] at literalPositionInside
              have periodIntPositive : 0 < (placement.period : Int) := by
                exact_mod_cast periodPositive
              have offsetXZero : offsetX = 0 := by
                by_contra nonzero
                have sign : offsetX ≤ -1 ∨ 1 ≤ offsetX := by omega
                rcases sign with negative | positive <;> nlinarith
              have offsetYZero : offsetY = 0 := by
                by_contra nonzero
                have sign : offsetY ≤ -1 ∨ 1 ≤ offsetY := by omega
                rcases sign with negative | positive <;> nlinarith
              simp [offsetXZero, offsetYZero]

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

/-- The final route-direction sort chooses a local auxiliary occurrence as
the first literal of every binary or ternary clause. -/
theorem retainedOrderedFixedEightFinalClockwiseClause_exists_localAnchor
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (sourceLocal : source.IsLocal)
    (sourceWidth : source.WidthAtMost 3)
    (sourceOccurrences : source.OccurrencesAtMost 3)
    (sourceClausesNonempty :
      ∀ clause ∈ source.clauses, clause ≠ [])
    {orderedClause :
      PositionedPeriodicClause
        (OneInThreeNoUnitVariable
          (PeriodicPlanarOneInThreeThreeRawVariable Variable))}
    {clauseIndex : Nat}
    (orderedClauseMember :
      (orderedClause, clauseIndex) ∈
        (retainedOrderedFixedEightPositionedPeriodicPlanarOneInThreeNoUnitsFinalClockwiseFormula
          source sourceLocal sourceWidth sourceOccurrences
          sourceClausesNonempty).clauses.zipIdx) :
    ∃ rawClause anchorLiteral anchorLiteralIndex rest,
      (rawClause, clauseIndex) ∈
          (retainedOrderedFixedEightPositionedPeriodicPlanarOneInThreeNoUnitsComposedRawFormula
            source).clauses.zipIdx ∧
        (anchorLiteral, anchorLiteralIndex) ∈
          rawClause.literals.zipIdx ∧
        orderedClause.literals = anchorLiteral :: rest ∧
        ∀ sourceAtom : PeriodicPlanarThreeSATThreeVariable Variable,
          anchorLiteral.atom ≠ .inl (.inl sourceAtom) := by
  let rawFormula :=
    retainedOrderedFixedEightPositionedPeriodicPlanarOneInThreeNoUnitsComposedRawFormula
      source
  let routes :=
    retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsComposedRawNormalizedIncidenceRoutes
      source sourceLocal sourceWidth sourceOccurrences
      sourceClausesNonempty
  have orderedClauseMember' :
      (orderedClause, clauseIndex) ∈
        (PositionedPeriodicCNF.orderClausesByRouteDirection
          rawFormula routes).clauses.zipIdx := by
    simpa only [rawFormula, routes,
      retainedOrderedFixedEightPositionedPeriodicPlanarOneInThreeNoUnitsFinalClockwiseFormula]
      using orderedClauseMember
  rcases PositionedPeriodicCNF.exists_sourceClause_of_orderedClause_mem
      routes orderedClauseMember' with
    ⟨rawClause, rawClauseMember, orderedClauseEq⟩
  have rawArity :=
    retainedOrderedFixedEightPositionedPeriodicPlanarOneInThreeNoUnitsComposedRawFormula_arityTwoOrThree
      source rawClause.literals
      (by
        exact List.mem_map.mpr
          ⟨rawClause, List.fst_mem_of_mem_zipIdx rawClauseMember, rfl⟩)
  rcases rawArity with binary | ternary
  · have orderedLength : orderedClause.literals.length = 2 := by
      rw [orderedClauseEq,
        PositionedPeriodicCNF.orderClauseByRouteDirection_length]
      exact binary
    rcases List.length_eq_two.mp orderedLength with
      ⟨anchorLiteral, otherLiteral, orderedLiteralsEq⟩
    have anchorOrderedMember : anchorLiteral ∈ orderedClause.literals := by
      simp [orderedLiteralsEq]
    have anchorRawMember : anchorLiteral ∈ rawClause.literals :=
      (PositionedPeriodicCNF.orderClauseByRouteDirection_literals_perm
        routes clauseIndex rawClause).mem_iff.mp (by
          simpa [orderedClauseEq] using anchorOrderedMember)
    rcases List.mem_iff_getElem.mp anchorRawMember with
      ⟨anchorLiteralIndex, anchorLiteralIndexLt, anchorLiteralAt⟩
    have taggedAnchorMember :
        (anchorLiteral, anchorLiteralIndex) ∈
          rawClause.literals.zipIdx := by
      rw [List.mem_zipIdx_iff_getElem?, List.getElem?_eq_some_iff]
      exact ⟨anchorLiteralIndexLt, anchorLiteralAt⟩
    have localAnchor :=
      PlanarOneInThreeNoUnitsFigureNine.binaryClause_literal_not_original
        (retainedFigureNineClearancePositionedFormula source)
        (by simpa only [rawFormula,
          retainedOrderedFixedEightPositionedPeriodicPlanarOneInThreeNoUnitsComposedRawFormula]
          using rawClauseMember)
        binary anchorRawMember
    exact ⟨rawClause, anchorLiteral, anchorLiteralIndex,
      [otherLiteral], rawClauseMember, taggedAnchorMember,
      orderedLiteralsEq, localAnchor⟩
  · rcases List.length_eq_three.mp ternary with
      ⟨first, second, third, rawLiteralsEq⟩
    have orderedRoutes :=
      retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsComposedRawNormalizedIncidenceRoutes_ternaryClauseRoutesInUnitEliminationOrder
        source sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty
    have orderedLiteralsEq :=
      PositionedPeriodicCNF.orderClauseByRouteDirection_literals_eq_two_zero_one_of_unitEliminationOrder
        (placement :=
          retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsComposedRawPlacement
            source)
        orderedRoutes
        (by simpa only [rawFormula] using rawClauseMember)
        rawLiteralsEq
    have thirdLocal :=
      PlanarOneInThreeNoUnitsFigureNine.ternaryClause_thirdLiteral_not_original
        (retainedFigureNineClearancePositionedFormula source)
        (by simpa only [rawFormula,
          retainedOrderedFixedEightPositionedPeriodicPlanarOneInThreeNoUnitsComposedRawFormula]
          using rawClauseMember)
        ternary
    rcases thirdLocal with
      ⟨thirdLiteral, thirdLiteralMember, thirdLiteralLocal⟩
    have thirdLiteralEq : thirdLiteral = third := by
      simpa [rawLiteralsEq] using thirdLiteralMember
    subst thirdLiteral
    refine ⟨rawClause, third, 2, [first, second],
      rawClauseMember, ?_, ?_, thirdLiteralLocal⟩
    · simpa [rawLiteralsEq]
    · rw [orderedClauseEq]
      exact orderedLiteralsEq

/-- Gauging sends the selected local anchor to offset zero, so the final
canonical clause representative is exactly its unchanged raw stored point. -/
theorem retainedOrderedFixedEightFinalGaugedCanonicalClausePosition_eq_rawPosition
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (sourceLocal : source.IsLocal)
    (sourceWidth : source.WidthAtMost 3)
    (sourceOccurrences : source.OccurrencesAtMost 3)
    (sourceClausesNonempty :
      ∀ clause ∈ source.clauses, clause ≠ [])
    {gaugedClause :
      PositionedPeriodicClause
        (OneInThreeNoUnitVariable
          (PeriodicPlanarOneInThreeThreeRawVariable Variable))}
    {clauseIndex : Nat}
    (gaugedClauseMember :
      (gaugedClause, clauseIndex) ∈
        (retainedOrderedFixedEightPositionedPeriodicPlanarOneInThreeNoUnitsFinalGaugedFormula
          source sourceLocal sourceWidth sourceOccurrences
          sourceClausesNonempty).clauses.zipIdx) :
    ∃ rawClause,
      (rawClause, clauseIndex) ∈
          (retainedOrderedFixedEightPositionedPeriodicPlanarOneInThreeNoUnitsComposedRawFormula
            source).clauses.zipIdx ∧
        PositionedPeriodicCNF.canonicalClausePosition
            (retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsFinalGaugedPlacement
              source)
            gaugedClause = rawClause.position := by
  let rawPlacement :=
    retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsComposedRawPlacement
      source
  let gauge :=
    retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsFinalGauge
      source
  let orderedFormula :=
    retainedOrderedFixedEightPositionedPeriodicPlanarOneInThreeNoUnitsFinalClockwiseFormula
      source sourceLocal sourceWidth sourceOccurrences
      sourceClausesNonempty
  have gaugedClauseMember' :
      (gaugedClause, clauseIndex) ∈
        (orderedFormula.variableGauge gauge).clauses.zipIdx := by
    simpa only [orderedFormula, gauge,
      retainedOrderedFixedEightPositionedPeriodicPlanarOneInThreeNoUnitsFinalGaugedFormula]
      using gaugedClauseMember
  rcases PositionedPeriodicCNF.exists_sourceClause_of_variableGaugeClause_mem
      orderedFormula gauge gaugedClauseMember' with
    ⟨orderedClause, orderedClauseMember, gaugedClauseEq⟩
  rcases retainedOrderedFixedEightFinalClockwiseClause_exists_localAnchor
      source sourceLocal sourceWidth sourceOccurrences
      sourceClausesNonempty
      (by simpa only [orderedFormula] using orderedClauseMember) with
    ⟨rawClause, anchorLiteral, anchorLiteralIndex, rest,
      rawClauseMember, anchorLiteralMember, orderedLiteralsEq,
      localAnchor⟩
  have atomMember :
      anchorLiteral.atom ∈
        (retainedOrderedFixedEightPositionedPeriodicPlanarOneInThreeNoUnitsComposedRawFormula
          source).erase.variableOccurrences := by
    unfold PeriodicCNF.variableOccurrences
    apply List.mem_flatMap.mpr
    refine ⟨rawClause.literals, ?_, ?_⟩
    · exact List.mem_map.mpr
        ⟨rawClause, List.fst_mem_of_mem_zipIdx rawClauseMember, rfl⟩
    · exact List.mem_map.mpr
        ⟨anchorLiteral,
          List.fst_mem_of_mem_zipIdx anchorLiteralMember, rfl⟩
  have residueInside :=
    retainedOrderedFixedEightComposedRawVariablePosition_residue_inSquare
      source sourceLocal sourceWidth sourceOccurrences
      sourceClausesNonempty anchorLiteral.atom atomMember
  have gaugedPositionInside :=
    PeriodicVariablePlacement.variableGauge_canonicalPositionGauge_position_inSquare
      rawPlacement
      (by
        simpa only [rawPlacement] using
          retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsComposedRawPlacement_period_pos
            source)
      anchorLiteral.atom (ne_of_gt residueInside.1)
      (ne_of_gt residueInside.2.2.1)
  have literalPositionInside :=
    retainedOrderedFixedEightComposedRawLocalLiteralPosition_inSquare
      source sourceLocal sourceWidth sourceOccurrences
      sourceClausesNonempty rawClauseMember anchorLiteralMember
      localAnchor
  have anchorOffsetZero :
      (anchorLiteral.variableGauge gauge).offset = (0, 0) := by
    apply
      PeriodicVariablePlacement.canonicalPositionGauge_literalOffset_eq_zero
        rawPlacement
        (by
          simpa only [rawPlacement] using
            retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsComposedRawPlacement_period_pos
              source)
        anchorLiteral
    · simpa only [rawPlacement, gauge,
        retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsFinalGauge]
        using gaugedPositionInside
    · simpa only [rawPlacement] using literalPositionInside
  have gaugedAnchorZero :
      PeriodicCNF.clauseAnchor gaugedClause.literals = (0, 0) := by
    rw [gaugedClauseEq]
    simp [PeriodicClause.variableGauge, orderedLiteralsEq,
      PeriodicCNF.clauseAnchor, anchorOffsetZero]
  refine ⟨rawClause, rawClauseMember, ?_⟩
  rw [PositionedPeriodicCNF.canonicalClausePosition, gaugedAnchorZero]
  simp [gaugedClauseEq, rawPlacement, gauge,
    retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsFinalGaugedPlacement,
    PeriodicVariablePlacement.translation, Cell.sub, Cell.scale]

/-- Every final gauged canonical clause vertex lies strictly inside the
final fundamental square. -/
theorem retainedOrderedFixedEightFinalGaugedCanonicalClausePosition_inSquare_of_mem
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (sourceLocal : source.IsLocal)
    (sourceWidth : source.WidthAtMost 3)
    (sourceOccurrences : source.OccurrencesAtMost 3)
    (sourceClausesNonempty :
      ∀ clause ∈ source.clauses, clause ≠ [])
    {gaugedClause :
      PositionedPeriodicClause
        (OneInThreeNoUnitVariable
          (PeriodicPlanarOneInThreeThreeRawVariable Variable))}
    {clauseIndex : Nat}
    (gaugedClauseMember :
      (gaugedClause, clauseIndex) ∈
        (retainedOrderedFixedEightPositionedPeriodicPlanarOneInThreeNoUnitsFinalGaugedFormula
          source sourceLocal sourceWidth sourceOccurrences
          sourceClausesNonempty).clauses.zipIdx) :
    let position :=
      PositionedPeriodicCNF.canonicalClausePosition
        (retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsFinalGaugedPlacement
          source)
        gaugedClause
    0 < position.1 ∧
      position.1 <
        (retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsFinalGaugedPlacement
          source).period ∧
      0 < position.2 ∧
      position.2 <
        (retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsFinalGaugedPlacement
          source).period := by
  dsimp only
  rcases
      retainedOrderedFixedEightFinalGaugedCanonicalClausePosition_eq_rawPosition
        source sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty gaugedClauseMember with
    ⟨rawClause, rawClauseMember, positionEq⟩
  have rawBounds :=
    retainedOrderedFixedEightComposedRawStoredClausePosition_inSquare_of_mem
      source sourceLocal sourceWidth sourceOccurrences
      sourceClausesNonempty rawClause clauseIndex rawClauseMember
  rw [positionEq]
  simpa only [
    retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsFinalGaugedPlacement,
    PeriodicVariablePlacement.variableGauge_period] using rawBounds

end PeriodicOrthocrossing
end LeanTrominoes
