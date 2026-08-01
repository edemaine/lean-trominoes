import LeanTrominoes.RetainedAngularFanFinalDirectSourceSharedTargetData
import LeanTrominoes.PeriodicEightOccurrenceSplitAngularSuffixSeparation

/-!
# Cross-clause separation of final occurrence suffixes

The final Figure 7 suffixes are disjoint for genuine incidences in
different copied source clauses.  Different canonical variable centers use
the separated-macrocell theorem.  At one shared center, the two distinct
tagged occurrences receive different slots in their common angular order,
so the finite eight-spoke atlas supplies the separation.
-/

namespace LeanTrominoes
namespace PeriodicOrthocrossing

open OccurrenceSplitRing
open PeriodicEightOccurrenceSplit
open PeriodicEightOccurrenceSplitPositioned
open PeriodicThreeSATThree
open PlanarThreeSAT.EmbeddedCNFIncidenceDrawing

set_option maxHeartbeats 2000000

/-- Scaled Figure 7 suffixes belonging to different genuine final source
clauses are contact-free, even when their canonical variable centers
coincide. -/
theorem retainedFinalCrossClauseOccurrenceSuffixes_strictlyAvoid
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (sourceLocal : formula.IsLocal)
    (sourceWidth : formula.WidthAtMost 3)
    (sourceOccurrences : formula.OccurrencesAtMost 3)
    (sourceClausesNonempty :
      ∀ clause ∈ formula.clauses, clause ≠ [])
    {firstClause secondClause :
      PositionedPeriodicClause
        (WrappedPeriodicPlanarSATVariable Variable)}
    {firstClauseIndex secondClauseIndex : Nat}
    (firstClauseMember :
      (firstClause, firstClauseIndex) ∈
        (finalCoordinatedSource formula).clauses.zipIdx)
    (secondClauseMember :
      (secondClause, secondClauseIndex) ∈
        (finalCoordinatedSource formula).clauses.zipIdx)
    {firstLiteral secondLiteral :
      PeriodicLiteral (WrappedPeriodicPlanarSATVariable Variable)}
    {firstLiteralIndex secondLiteralIndex : Nat}
    (firstLiteralMember :
      (firstLiteral, firstLiteralIndex) ∈
        firstClause.literals.zipIdx)
    (secondLiteralMember :
      (secondLiteral, secondLiteralIndex) ∈
        secondClause.literals.zipIdx)
    (clauseIndicesDifferent :
      firstClauseIndex ≠ secondClauseIndex) :
    let source :=
      (finalCoordinatedSource formula).scale
        retainedAngularFanSourceClearanceFactor
    let placement :=
      (finalCoordinatedPlacement formula).scale
        retainedAngularFanSourceClearanceFactor
    let routes :=
      PositionedPeriodicCNF.scaleIncidenceRoutes
        retainedAngularFanSourceClearanceFactor
        (finalCoordinatedSourceRoutes formula)
    let order := angularOccurrenceOrder source.erase routes
    let firstScaledClause :=
      firstClause.scale retainedAngularFanSourceClearanceFactor
    let secondScaledClause :=
      secondClause.scale retainedAngularFanSourceClearanceFactor
    RoutesStrictlyAvoidEachOther
      (scalePolyline retainedTerminalFanRoutingRefinement
        (angularOccurrenceSuffix placement order
          firstScaledClause firstLiteral
          firstClauseIndex firstLiteralIndex))
      (scalePolyline retainedTerminalFanRoutingRefinement
        (angularOccurrenceSuffix placement order
          secondScaledClause secondLiteral
          secondClauseIndex secondLiteralIndex)) := by
  dsimp only
  let source :=
    (finalCoordinatedSource formula).scale
      retainedAngularFanSourceClearanceFactor
  let placement :=
    (finalCoordinatedPlacement formula).scale
      retainedAngularFanSourceClearanceFactor
  let routes :=
    PositionedPeriodicCNF.scaleIncidenceRoutes
      retainedAngularFanSourceClearanceFactor
      (finalCoordinatedSourceRoutes formula)
  let order := angularOccurrenceOrder source.erase routes
  let firstScaledClause :=
    firstClause.scale retainedAngularFanSourceClearanceFactor
  let secondScaledClause :=
    secondClause.scale retainedAngularFanSourceClearanceFactor
  by_cases centersEqual :
      PositionedPeriodicCNF.canonicalLiteralPosition
          (finalCoordinatedPlacement formula)
          firstClause firstLiteral =
        PositionedPeriodicCNF.canonicalLiteralPosition
          (finalCoordinatedPlacement formula)
          secondClause secondLiteral
  · have atomsEqual :
        firstLiteral.atom = secondLiteral.atom :=
      retainedFinalCanonicalLiteralPositions_eq_imp_atoms_eq
        formula sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty
        firstClauseMember secondClauseMember
        firstLiteralMember secondLiteralMember centersEqual
    let firstOccurrence :
        ThreeOccurrenceVariable
          (WrappedPeriodicPlanarSATVariable Variable) :=
      (firstLiteral.atom, firstClauseIndex, firstLiteralIndex)
    let secondOccurrence :
        ThreeOccurrenceVariable
          (WrappedPeriodicPlanarSATVariable Variable) :=
      (secondLiteral.atom, secondClauseIndex, secondLiteralIndex)
    let ordered := order.copies firstLiteral.atom
    have firstScaledClauseMember :
        (firstScaledClause, firstClauseIndex) ∈
          source.clauses.zipIdx := by
      dsimp only [source, firstScaledClause]
      rw [PositionedPeriodicCNF.scale_clauses, List.zipIdx_map]
      exact List.mem_map.mpr
        ⟨(firstClause, firstClauseIndex), firstClauseMember, rfl⟩
    have secondScaledClauseMember :
        (secondScaledClause, secondClauseIndex) ∈
          source.clauses.zipIdx := by
      dsimp only [source, secondScaledClause]
      rw [PositionedPeriodicCNF.scale_clauses, List.zipIdx_map]
      exact List.mem_map.mpr
        ⟨(secondClause, secondClauseIndex), secondClauseMember, rfl⟩
    have firstTagged :=
      taggedLiteral_mem_of_positioned_members
        source firstScaledClauseMember firstLiteralMember
    have secondTagged :=
      taggedLiteral_mem_of_positioned_members
        source secondScaledClauseMember secondLiteralMember
    have firstOccurrenceMember :
        firstOccurrence ∈
          occurrenceVariables source.erase firstLiteral.atom := by
      exact occurrenceVariables_mem _ firstTagged
    have secondOccurrenceMember :
        secondOccurrence ∈
          occurrenceVariables source.erase firstLiteral.atom := by
      simpa [secondOccurrence, atomsEqual] using
        (occurrenceVariables_mem _ secondTagged)
    have firstOrderedMember : firstOccurrence ∈ ordered := by
      exact
        (order.mem_iff firstLiteral.atom firstOccurrence).mpr
          firstOccurrenceMember
    have secondOrderedMember : secondOccurrence ∈ ordered := by
      exact
        (order.mem_iff firstLiteral.atom secondOccurrence).mpr
          secondOccurrenceMember
    have occurrenceValuesDifferent :
        firstOccurrence ≠ secondOccurrence := by
      intro occurrencesEqual
      apply clauseIndicesDifferent
      exact congrArg (fun occurrence => occurrence.2.1) occurrencesEqual
    have indicesDifferent :
        angularOccurrenceIndex order firstLiteral
            firstClauseIndex firstLiteralIndex ≠
          angularOccurrenceIndex order secondLiteral
            secondClauseIndex secondLiteralIndex := by
      intro indicesEqual
      apply occurrenceValuesDifferent
      apply idxOf_injective_on ordered
        firstOrderedMember secondOrderedMember
      simpa [ordered, firstOccurrence, secondOccurrence,
        angularOccurrenceIndex, indexedOccurrence, atomsEqual]
        using indicesEqual
    let firstSlot :=
      retainedFinalCoordinatedOccurrenceSlot
        formula firstLiteral firstClauseIndex firstLiteralIndex
    let secondSlot :=
      retainedFinalCoordinatedOccurrenceSlot
        formula secondLiteral secondClauseIndex secondLiteralIndex
    have firstSlotVal :
        firstSlot.val =
          angularOccurrenceIndex order firstLiteral
            firstClauseIndex firstLiteralIndex := by
      simpa [source, routes, order, firstSlot,
        finalCoordinatedSource, finalCoordinatedSourceRoutes] using
        retainedFinalCoordinatedOccurrenceSlot_val
          formula sourceLocal sourceWidth sourceOccurrences
          sourceClausesNonempty firstClauseMember firstLiteralMember
    have secondSlotVal :
        secondSlot.val =
          angularOccurrenceIndex order secondLiteral
            secondClauseIndex secondLiteralIndex := by
      simpa [source, routes, order, secondSlot,
        finalCoordinatedSource, finalCoordinatedSourceRoutes] using
        retainedFinalCoordinatedOccurrenceSlot_val
          formula sourceLocal sourceWidth sourceOccurrences
          sourceClausesNonempty secondClauseMember secondLiteralMember
    have firstIndexLt :
        angularOccurrenceIndex order firstLiteral
            firstClauseIndex firstLiteralIndex < 8 := by
      rw [← firstSlotVal]
      exact firstSlot.isLt
    have secondIndexLt :
        angularOccurrenceIndex order secondLiteral
            secondClauseIndex secondLiteralIndex < 8 := by
      rw [← secondSlotVal]
      exact secondSlot.isLt
    have scaledCentersEqual :
        PositionedPeriodicCNF.canonicalLiteralPosition
            placement firstScaledClause firstLiteral =
          PositionedPeriodicCNF.canonicalLiteralPosition
            placement secondScaledClause secondLiteral := by
      simpa [placement, firstScaledClause, secondScaledClause,
        PositionedPeriodicCNF.CanonicalRetainedRayIncidenceRoutes.canonicalLiteralPosition_scale]
        using
          congrArg
            (Cell.scale retainedAngularFanSourceClearanceFactor)
            centersEqual
    have originsEqual :
        angularFanOccurrenceOrigin placement firstLiteral.atom
            (incidenceRelativeOffset firstScaledClause firstLiteral) =
          angularFanOccurrenceOrigin placement secondLiteral.atom
            (incidenceRelativeOffset secondScaledClause secondLiteral) := by
      rw [angularFanOccurrenceOrigin_incidenceRelativeOffset,
        angularFanOccurrenceOrigin_incidenceRelativeOffset,
        scaledCentersEqual]
    have unscaledAvoid :
        RoutesStrictlyAvoidEachOther
          (angularOccurrenceSuffix placement order
            firstScaledClause firstLiteral
            firstClauseIndex firstLiteralIndex)
          (angularOccurrenceSuffix placement order
            secondScaledClause secondLiteral
            secondClauseIndex secondLiteralIndex) := by
      unfold angularOccurrenceSuffix
      exact
        angularFanSpokeRoutesAt_strictlyAvoid_of_sameOrigin
          placement firstLiteral.atom secondLiteral.atom
          (incidenceRelativeOffset firstScaledClause firstLiteral)
          (incidenceRelativeOffset secondScaledClause secondLiteral)
          (angularOccurrenceIndex order firstLiteral
            firstClauseIndex firstLiteralIndex)
          (angularOccurrenceIndex order secondLiteral
            secondClauseIndex secondLiteralIndex)
          firstIndexLt secondIndexLt indicesDifferent originsEqual
    exact
      unscaledAvoid.scalePolyline
        (by norm_num [retainedTerminalFanRoutingRefinement])
  · apply
      scaledAngularOccurrenceSuffix_strictlyAvoid_of_centers_ne
        placement order firstScaledClause secondScaledClause
        firstLiteral secondLiteral
        firstClauseIndex firstLiteralIndex
        secondClauseIndex secondLiteralIndex
        retainedTerminalFanRoutingRefinement
    · norm_num [retainedTerminalFanRoutingRefinement]
    · intro scaledCentersEqual
      apply centersEqual
      apply Cell.scale_injective
        (show
          (retainedAngularFanSourceClearanceFactor : Int) ≠ 0 by
          exact_mod_cast
            ne_of_gt retainedAngularFanSourceClearanceFactor_pos)
      simpa [placement, firstScaledClause, secondScaledClause,
        PositionedPeriodicCNF.CanonicalRetainedRayIncidenceRoutes.canonicalLiteralPosition_scale]
        using scaledCentersEqual

end PeriodicOrthocrossing
end LeanTrominoes
