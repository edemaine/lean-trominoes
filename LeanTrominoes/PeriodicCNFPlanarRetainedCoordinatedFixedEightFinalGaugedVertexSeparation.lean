import LeanTrominoes.PeriodicCNFPlanarRetainedCoordinatedFixedEightFinalGaugedVariableSeparation
import LeanTrominoes.PeriodicCNFPlanarRetainedCoordinatedFixedEightFinalGaugedClauseSeparation

/-!
# Vertex separation in the final canonical gauge

Variable and clause vertices use disjoint constructors in the finite Figure
Nine macrocell address table.  This rules out mixed collisions modulo the raw
period and, after accounting for the final gauges, completes `Nodup` for the
full final incidence-vertex position list.
-/

namespace LeanTrominoes
namespace PeriodicOrthocrossing

set_option maxHeartbeats 5000000

attribute [local instance] finalGaugedVariableSeparationDecidableEq

attribute [local irreducible]
  retainedOrderedFixedEightPositionedPeriodicPlanarOneInThreeNoUnitsFinalGaugedFormula
  retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsFinalGaugedPlacement

/-- A genuine raw variable occurrence cannot occupy the stored-position
orbit of a genuine raw clause.  Their finite macrocell address constructors
are disjoint. -/
theorem retainedOrderedFixedEightComposedRawVariablePosition_ne_translated_clausePosition
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    {atom :
      OneInThreeNoUnitVariable
        (PeriodicPlanarOneInThreeThreeRawVariable Variable)}
    (atomMember :
      atom ∈
        (retainedOrderedFixedEightPositionedPeriodicPlanarOneInThreeNoUnitsComposedRawFormula
          source).erase.variableOccurrences)
    {clause :
      PositionedPeriodicClause
        (OneInThreeNoUnitVariable
          (PeriodicPlanarOneInThreeThreeRawVariable Variable))}
    {clauseIndex : Nat}
    (clauseMember :
      (clause, clauseIndex) ∈
        (retainedOrderedFixedEightPositionedPeriodicPlanarOneInThreeNoUnitsComposedRawFormula
          source).clauses.zipIdx)
    (relativeTranslate : Cell) :
    (retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsComposedRawPlacement
        source).position atom ≠
      Cell.add
        ((retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsComposedRawPlacement
            source).translation relativeTranslate)
        clause.position := by
  intro positionsEqual
  rcases
      retainedOrderedFixedEightComposedRawVariableOccurrence_inMacrocellOrbit
        source atomMember with
    ⟨variableBase, variableAddress, variableSource, variableOrbit⟩
  rcases
      retainedOrderedFixedEightComposedRawClause_inMacrocellOrbit_withSource
        source clauseMember with
    ⟨clauseBase, clauseAddress, clauseSource, clauseOrbit⟩
  have rawPeriod :
      (retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsComposedRawPlacement
          source).period =
        finalFigureNineMacrocellScale *
          (retainedFigureNineClearancePlacement source).period := by
    simp [
      retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsComposedRawPlacement,
      PlanarOneInThreeNoUnitsFigureNine.composedPlacement,
      PeriodicOneInThreePositioned.placement,
      PeriodicOneInThreeNoUnitsPositioned.placement,
      finalFigureNineMacrocellScale,
      PlanarOneInThree.gadgetScale,
      PeriodicOneInThreeNoUnitsPositioned.gadgetScale]
    omega
  have refinedPositionsEqual :
      (retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsComposedRawPlacement
          source).position atom =
        Cell.add
          (Cell.scale
            (finalFigureNineMacrocellScale *
              (retainedFigureNineClearancePlacement source).period)
            relativeTranslate)
          clause.position := by
    rw [PeriodicVariablePlacement.translation, rawPeriod] at positionsEqual
    exact positionsEqual
  rcases Cell.inMacrocellOrbit_eq_periodTranslate
      (show 0 < finalFigureNineMacrocellScale by native_decide)
      (finalFigureNineLocalAddress_position_halfOpen variableAddress)
      (finalFigureNineLocalAddress_position_halfOpen clauseAddress)
      variableOrbit clauseOrbit refinedPositionsEqual with
    ⟨_baseTranslate, _basesEqual, localPositionsEqual⟩
  have addressesEqual : variableAddress = clauseAddress :=
    finalFigureNineLocalAddress_position_injective localPositionsEqual
  cases variableSource <;> cases clauseSource <;> simp at addressesEqual

/-- No genuine final variable vertex equals a genuine final canonical clause
vertex. -/
theorem retainedOrderedFixedEightFinalGaugedVariablePosition_ne_canonicalClausePosition
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (sourceLocal : source.IsLocal)
    (sourceWidth : source.WidthAtMost 3)
    (sourceOccurrences : source.OccurrencesAtMost 3)
    (sourceClausesNonempty :
      ∀ clause ∈ source.clauses, clause ≠ [])
    {atom :
      OneInThreeNoUnitVariable
        (PeriodicPlanarOneInThreeThreeRawVariable Variable)}
    (atomMember :
      atom ∈
        (retainedOrderedFixedEightPositionedPeriodicPlanarOneInThreeNoUnitsFinalGaugedFormula
          source sourceLocal sourceWidth sourceOccurrences
          sourceClausesNonempty).erase.variableOccurrences)
    {clause :
      PositionedPeriodicClause
        (OneInThreeNoUnitVariable
          (PeriodicPlanarOneInThreeThreeRawVariable Variable))}
    {clauseIndex : Nat}
    (clauseMember :
      (clause, clauseIndex) ∈
        (retainedOrderedFixedEightPositionedPeriodicPlanarOneInThreeNoUnitsFinalGaugedFormula
          source sourceLocal sourceWidth sourceOccurrences
          sourceClausesNonempty).clauses.zipIdx) :
    (retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsFinalGaugedPlacement
        source).position atom ≠
      PositionedPeriodicCNF.canonicalClausePosition
        (retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsFinalGaugedPlacement
          source) clause := by
  intro positionsEqual
  have rawAtomMember :=
    finalGaugedVariableOccurrence_mem_composedRaw
      source sourceLocal sourceWidth sourceOccurrences sourceClausesNonempty
      atomMember
  rcases exists_composedRawClause_of_finalGaugedClause_mem
      source sourceLocal sourceWidth sourceOccurrences sourceClausesNonempty
      clauseMember with
    ⟨rawClause, rawClauseMember, storedPositionEqual⟩
  let relativeTranslate :=
    Cell.sub
      (retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsFinalGauge
        source atom)
      (PeriodicCNF.clauseAnchor clause.literals)
  have rawPositionsEqual :
      (retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsComposedRawPlacement
          source).position atom =
        Cell.add
          ((retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsComposedRawPlacement
              source).translation relativeTranslate)
          rawClause.position := by
    rw [← storedPositionEqual]
    rcases atomPositionEq :
        (retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsComposedRawPlacement
          source).position atom with
      ⟨atomX, atomY⟩
    rcases clausePositionEq : clause.position with ⟨clauseX, clauseY⟩
    rcases gaugeEq :
        retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsFinalGauge
          source atom with
      ⟨gaugeX, gaugeY⟩
    rcases anchorEq : PeriodicCNF.clauseAnchor clause.literals with
      ⟨anchorX, anchorY⟩
    simp only [
      retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsFinalGaugedPlacement,
      PeriodicVariablePlacement.variableGauge,
      PositionedPeriodicCNF.canonicalClausePosition,
      PeriodicVariablePlacement.translation, Cell.add, Cell.sub, Cell.scale,
      relativeTranslate, atomPositionEq, clausePositionEq, gaugeEq, anchorEq,
      Prod.mk.injEq] at positionsEqual ⊢
    constructor
    · linear_combination positionsEqual.1
    · linear_combination positionsEqual.2
  exact
    retainedOrderedFixedEightComposedRawVariablePosition_ne_translated_clausePosition
      source rawAtomMember rawClauseMember relativeTranslate rawPositionsEqual

private theorem variableClausePositions_disjoint_of
    {Variable : Type*} [DecidableEq Variable]
    (formula : PositionedPeriodicCNF Variable)
    (placement : PeriodicVariablePlacement Variable)
    (separate :
      ∀ {atom : Variable},
        atom ∈ formula.erase.variableOccurrences →
        ∀ {clause : PositionedPeriodicClause Variable}
            {clauseIndex : Nat},
          (clause, clauseIndex) ∈ formula.clauses.zipIdx →
          placement.position atom ≠
            PositionedPeriodicCNF.canonicalClausePosition
              placement clause) :
    List.Disjoint
      (formula.erase.incidenceVariableVertices.map
        (PositionedPeriodicCNF.incidenceVariableVertexPosition placement))
      (formula.clauses.map
        (PositionedPeriodicCNF.canonicalClausePosition
          placement)) := by
  rw [List.disjoint_left]
  intro position variablePositionMember clausePositionMember
  rw [PeriodicCNF.incidenceVariableVertices, List.map_map,
    List.mem_map] at variablePositionMember
  rcases variablePositionMember with
    ⟨atom, atomMember, variablePositionEq⟩
  rw [List.mem_map] at clausePositionMember
  rcases clausePositionMember with
    ⟨clause, clauseMember, clausePositionEq⟩
  rcases List.mem_iff_getElem?.mp clauseMember with
    ⟨clauseIndex, clauseLookup⟩
  have indexedClauseMember :
      (clause, clauseIndex) ∈ formula.clauses.zipIdx :=
    List.mem_zipIdx_iff_getElem?.mpr clauseLookup
  exact
    (separate (List.mem_dedup.mp atomMember) indexedClauseMember)
      (variablePositionEq.trans clausePositionEq.symm)

/-- The variable-position prefix and canonical clause-position suffix of the
final incidence drawing are disjoint. -/
theorem retainedOrderedFixedEightFinalGaugedVariableClausePositions_disjoint
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (sourceLocal : source.IsLocal)
    (sourceWidth : source.WidthAtMost 3)
    (sourceOccurrences : source.OccurrencesAtMost 3)
    (sourceClausesNonempty :
      ∀ clause ∈ source.clauses, clause ≠ []) :
    List.Disjoint
      ((retainedOrderedFixedEightPositionedPeriodicPlanarOneInThreeNoUnitsFinalGaugedFormula
          source sourceLocal sourceWidth sourceOccurrences
          sourceClausesNonempty).erase.incidenceVariableVertices.map
        (PositionedPeriodicCNF.incidenceVariableVertexPosition
          (retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsFinalGaugedPlacement
            source)))
      ((retainedOrderedFixedEightPositionedPeriodicPlanarOneInThreeNoUnitsFinalGaugedFormula
          source sourceLocal sourceWidth sourceOccurrences
          sourceClausesNonempty).clauses.map
        (PositionedPeriodicCNF.canonicalClausePosition
          (retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsFinalGaugedPlacement
            source))) := by
  exact variableClausePositions_disjoint_of
    (formula :=
      retainedOrderedFixedEightPositionedPeriodicPlanarOneInThreeNoUnitsFinalGaugedFormula
        source sourceLocal sourceWidth sourceOccurrences sourceClausesNonempty)
    (placement :=
      retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsFinalGaugedPlacement
        source)
    (by
      intro atom atomMember clause clauseIndex clauseMember
      exact
        retainedOrderedFixedEightFinalGaugedVariablePosition_ne_canonicalClausePosition
          source sourceLocal sourceWidth sourceOccurrences sourceClausesNonempty
          atomMember clauseMember)

private theorem incidenceVertexPositions_nodup_of
    {Variable : Type*} [DecidableEq Variable]
    (formula : PositionedPeriodicCNF Variable)
    (placement : PeriodicVariablePlacement Variable)
    (variableNodup :
      (formula.erase.incidenceVariableVertices.map
        (PositionedPeriodicCNF.incidenceVariableVertexPosition
          placement)).Nodup)
    (clauseNodup :
      (formula.clauses.map
        (PositionedPeriodicCNF.canonicalClausePosition placement)).Nodup)
    (disjoint :
      List.Disjoint
        (formula.erase.incidenceVariableVertices.map
          (PositionedPeriodicCNF.incidenceVariableVertexPosition
            placement))
        (formula.clauses.map
          (PositionedPeriodicCNF.canonicalClausePosition placement))) :
    (formula.incidenceVertexPositions placement).Nodup := by
  rw [PositionedPeriodicCNF.incidenceVertexPositions_eq_variablePrefix_append]
  exact List.Nodup.append variableNodup clauseNodup disjoint

/-- All variable and clause prototype positions in the final incidence
drawing are pairwise distinct. -/
theorem retainedOrderedFixedEightFinalGaugedIncidenceVertexPositions_nodup
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (sourceLocal : source.IsLocal)
    (sourceWidth : source.WidthAtMost 3)
    (sourceOccurrences : source.OccurrencesAtMost 3)
    (sourceClausesNonempty :
      ∀ clause ∈ source.clauses, clause ≠ []) :
    (PositionedPeriodicCNF.incidenceVertexPositions
      (retainedOrderedFixedEightPositionedPeriodicPlanarOneInThreeNoUnitsFinalGaugedFormula
        source sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty)
      (retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsFinalGaugedPlacement
        source)).Nodup := by
  exact incidenceVertexPositions_nodup_of
    (formula :=
      retainedOrderedFixedEightPositionedPeriodicPlanarOneInThreeNoUnitsFinalGaugedFormula
        source sourceLocal sourceWidth sourceOccurrences sourceClausesNonempty)
    (placement :=
      retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsFinalGaugedPlacement
        source)
    (retainedOrderedFixedEightFinalGaugedVariablePositions_nodup
      source sourceLocal sourceWidth sourceOccurrences sourceClausesNonempty)
    (retainedOrderedFixedEightFinalGaugedCanonicalClausePositions_nodup
      source sourceLocal sourceWidth sourceOccurrences sourceClausesNonempty)
    (retainedOrderedFixedEightFinalGaugedVariableClausePositions_disjoint
      source sourceLocal sourceWidth sourceOccurrences sourceClausesNonempty)

end PeriodicOrthocrossing
end LeanTrominoes
