import LeanTrominoes.RetainedAngularFanFinalCoordinatedRoutes

/-!
# Validity of final coordinated direct routes

A validated direct-source choice replaces the ordinary source fan while
retaining the established, scaled Figure 7 occurrence suffix.  This file
proves that the coordinated prefix meets that suffix at exactly the same
fan-boundary point.  Consequently each substituted route has the canonical
endpoints and remains orthogonal.
-/

namespace LeanTrominoes
namespace PeriodicOrthocrossing

open PeriodicEightOccurrenceSplit
open PeriodicEightOccurrenceSplitPositioned
open PeriodicThreeSATThree
open OccurrenceSplitRing

set_option maxHeartbeats 2000000

/-- A validated coordinated direct prefix and the unchanged scaled Figure 7
suffix meet at exactly the same fan-boundary point. -/
theorem retainedFinalCoordinatedDirectOccurrenceRoute_boundary
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (sourceLocal : formula.IsLocal)
    (sourceWidth : formula.WidthAtMost 3)
    (sourceOccurrences : formula.OccurrencesAtMost 3)
    (sourceClausesNonempty :
      ∀ clause ∈ formula.clauses, clause ≠ [])
    (choice : RetainedDirectSourceRouteChoice)
    {clause :
      PositionedPeriodicClause
        (WrappedPeriodicPlanarSATVariable Variable)}
    {clauseIndex : Nat}
    (clauseMember :
      (clause, clauseIndex) ∈
        (retainedDeduplicatedGaugedWrappedDrawingPositionedPeriodicPlanarSATFormula
          formula).clauses.zipIdx)
    {literal :
      PeriodicLiteral (WrappedPeriodicPlanarSATVariable Variable)}
    {literalIndex : Nat}
    (literalMember :
      (literal, literalIndex) ∈ clause.literals.zipIdx)
    (choiceLookup :
      retainedFinalDirectSourceRouteChoice?
          formula clauseIndex literalIndex =
        some choice) :
    let source :=
      (retainedDeduplicatedGaugedWrappedDrawingPositionedPeriodicPlanarSATFormula
        formula).scale retainedAngularFanSourceClearanceFactor
    let placement :=
      (retainedGaugedWrappedDrawingPeriodicPlanarSATPlacement
        formula).scale retainedAngularFanSourceClearanceFactor
    let routes :=
      PositionedPeriodicCNF.scaleIncidenceRoutes
        retainedAngularFanSourceClearanceFactor
        (retainedDeduplicatedGaugedWrappedDrawingPeriodicPlanarSATIncidenceRoutes
          formula)
    let slot :=
      retainedFinalCoordinatedOccurrenceSlot
        formula literal clauseIndex literalIndex
    (choice.completeRoute slot).getLast? =
      (scalePolyline retainedTerminalFanRoutingRefinement
        (angularOccurrenceSuffix placement
          (angularOccurrenceOrder source.erase routes)
          (clause.scale retainedAngularFanSourceClearanceFactor)
          literal clauseIndex literalIndex)).head? := by
  dsimp only
  let sourceCertificate :=
    retainedPlanarSATCertificate formula
      sourceLocal sourceWidth sourceOccurrences
      sourceClausesNonempty
  have rawEndpoints :=
    retainedDeduplicatedGaugedWrappedDrawingPeriodicPlanarSATIncidenceRoutes_endpoints
      formula
      sourceCertificate.graphWellFormed
      sourceCertificate.graphDegreeAtMostThree
      sourceCertificate.graphIsLocal
      clauseMember literalMember
  have rawLastD :
      (retainedDeduplicatedGaugedWrappedDrawingPeriodicPlanarSATIncidenceRoutes
        formula clauseIndex literalIndex).getLastD (0, 0) =
        PositionedPeriodicCNF.canonicalLiteralPosition
          (retainedGaugedWrappedDrawingPeriodicPlanarSATPlacement formula)
          clause literal := by
    simp [List.getLastD_eq_getLast?, rawEndpoints.2]
  have fits :
      FitsEightSlots
        (angularOccurrenceOrder
          ((retainedDeduplicatedGaugedWrappedDrawingPositionedPeriodicPlanarSATFormula
            formula).scale retainedAngularFanSourceClearanceFactor).erase
          (PositionedPeriodicCNF.scaleIncidenceRoutes
            retainedAngularFanSourceClearanceFactor
            (retainedDeduplicatedGaugedWrappedDrawingPeriodicPlanarSATIncidenceRoutes
              formula))) := by
    rw [PositionedPeriodicCNF.erase_scale,
      angularOccurrenceOrder_scaleIncidenceRoutes
        (retainedDeduplicatedGaugedWrappedDrawingPositionedPeriodicPlanarSATFormula
          formula).erase
        retainedAngularFanSourceClearanceFactor_pos
        (retainedDeduplicatedGaugedWrappedDrawingPeriodicPlanarSATIncidenceRoutes
          formula)]
    simpa [retainedDrawingAngularOccurrenceOrder,
      retainedPlanarSATFormula] using
      retainedDrawingAngularOccurrenceOrder_fitsEightSlots
        sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty
  have scaledClauseMember :
      (clause.scale retainedAngularFanSourceClearanceFactor, clauseIndex) ∈
        ((retainedDeduplicatedGaugedWrappedDrawingPositionedPeriodicPlanarSATFormula
          formula).scale retainedAngularFanSourceClearanceFactor).clauses.zipIdx := by
    rw [PositionedPeriodicCNF.scale_clauses, List.zipIdx_map]
    exact List.mem_map.mpr
      ⟨(clause, clauseIndex), clauseMember, rfl⟩
  have taggedMember :=
    taggedLiteral_mem_of_positioned_members
      ((retainedDeduplicatedGaugedWrappedDrawingPositionedPeriodicPlanarSATFormula
        formula).scale retainedAngularFanSourceClearanceFactor)
      scaledClauseMember literalMember
  have copyMember :
      (literal.atom, clauseIndex, literalIndex) ∈
        occurrenceVariables
          ((retainedDeduplicatedGaugedWrappedDrawingPositionedPeriodicPlanarSATFormula
            formula).scale retainedAngularFanSourceClearanceFactor).erase
          literal.atom :=
    occurrenceVariables_mem _ taggedMember
  have indexLt :
      angularOccurrenceIndex
          (angularOccurrenceOrder
            ((retainedDeduplicatedGaugedWrappedDrawingPositionedPeriodicPlanarSATFormula
              formula).scale retainedAngularFanSourceClearanceFactor).erase
            (PositionedPeriodicCNF.scaleIncidenceRoutes
              retainedAngularFanSourceClearanceFactor
              (retainedDeduplicatedGaugedWrappedDrawingPeriodicPlanarSATIncidenceRoutes
                formula)))
          literal clauseIndex literalIndex < 8 := by
    simpa [angularOccurrenceIndex, indexedOccurrence,
      retainedAngularTerminalSlot_val] using
      (retainedAngularTerminalSlot
        ((retainedDeduplicatedGaugedWrappedDrawingPositionedPeriodicPlanarSATFormula
          formula).scale retainedAngularFanSourceClearanceFactor).erase
        (PositionedPeriodicCNF.scaleIncidenceRoutes
          retainedAngularFanSourceClearanceFactor
          (retainedDeduplicatedGaugedWrappedDrawingPeriodicPlanarSATIncidenceRoutes
            formula))
        fits literal.atom
        (literal.atom, clauseIndex, literalIndex)
        copyMember).isLt
  have slotVal :
      (retainedFinalCoordinatedOccurrenceSlot
        formula literal clauseIndex literalIndex).val =
        angularOccurrenceIndex
          (angularOccurrenceOrder
            ((retainedDeduplicatedGaugedWrappedDrawingPositionedPeriodicPlanarSATFormula
              formula).scale retainedAngularFanSourceClearanceFactor).erase
            (PositionedPeriodicCNF.scaleIncidenceRoutes
              retainedAngularFanSourceClearanceFactor
              (retainedDeduplicatedGaugedWrappedDrawingPeriodicPlanarSATIncidenceRoutes
                formula)))
          literal clauseIndex literalIndex := by
    exact boundedRetainedTerminalSlot_val_of_lt indexLt
  rw [choice.completeRoute_getLast_eq_scaledLocalLast]
  rw [← retainedFinalDirectSourceRouteChoice_route_getLastD
    formula clauseIndex literalIndex choice choiceLookup]
  rw [rawLastD]
  simp only [angularOccurrenceSuffix_head?, scalePolyline,
    List.head?_map, Option.map_some]
  rw [angularFanBoundaryPositionAt_eq_scaledCenter_add_offset]
  rw [slotVal]
  rw [PeriodicVariablePlacement.translation_scale]
  simp only [PositionedPeriodicCNF.canonicalLiteralPosition,
    incidenceRelativeOffset]
  rcases positionEq :
      (retainedGaugedWrappedDrawingPeriodicPlanarSATPlacement
        formula).position literal.atom with ⟨x, y⟩
  rcases translationEq :
      (retainedGaugedWrappedDrawingPeriodicPlanarSATPlacement
        formula).translation
        (Cell.sub literal.offset
          (PeriodicCNF.clauseAnchor clause.literals)) with ⟨dx, dy⟩
  rcases
      angularFanBoundaryOffset
        (angularOccurrenceIndex
          (angularOccurrenceOrder
            ((retainedDeduplicatedGaugedWrappedDrawingPositionedPeriodicPlanarSATFormula
              formula).scale retainedAngularFanSourceClearanceFactor).erase
            (PositionedPeriodicCNF.scaleIncidenceRoutes
              retainedAngularFanSourceClearanceFactor
              (retainedDeduplicatedGaugedWrappedDrawingPeriodicPlanarSATIncidenceRoutes
                formula)))
          literal clauseIndex literalIndex) with ⟨ox, oy⟩
  apply congrArg some
  apply Prod.ext <;>
    simp [retainedTerminalFanTotalRefinement_eq,
      retainedTerminalFanRoutingRefinement,
      retainedAngularFanSourceClearanceFactor,
      PeriodicVariablePlacement.scale,
      PositionedPeriodicClause.scale,
      PeriodicEightOccurrenceSplitPositioned.refinementScale,
      positionEq, translationEq,
      Cell.add, Cell.scale] <;>
    ring

/-- Every genuine validated direct occurrence route has the same canonical
endpoints as the established fixed-eight route and is orthogonal. -/
theorem retainedFinalCoordinatedDirectOccurrenceRoute_valid
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (sourceLocal : formula.IsLocal)
    (sourceWidth : formula.WidthAtMost 3)
    (sourceOccurrences : formula.OccurrencesAtMost 3)
    (sourceClausesNonempty :
      ∀ clause ∈ formula.clauses, clause ≠ [])
    (choice : RetainedDirectSourceRouteChoice)
    {clause :
      PositionedPeriodicClause
        (WrappedPeriodicPlanarSATVariable Variable)}
    {clauseIndex : Nat}
    (clauseMember :
      (clause, clauseIndex) ∈
        (retainedDeduplicatedGaugedWrappedDrawingPositionedPeriodicPlanarSATFormula
          formula).clauses.zipIdx)
    {literal :
      PeriodicLiteral (WrappedPeriodicPlanarSATVariable Variable)}
    {literalIndex : Nat}
    (literalMember :
      (literal, literalIndex) ∈ clause.literals.zipIdx)
    (choiceLookup :
      retainedFinalDirectSourceRouteChoice?
          formula clauseIndex literalIndex =
        some choice) :
    let source :=
      (retainedDeduplicatedGaugedWrappedDrawingPositionedPeriodicPlanarSATFormula
        formula).scale retainedAngularFanSourceClearanceFactor
    let placement :=
      (retainedGaugedWrappedDrawingPeriodicPlanarSATPlacement
        formula).scale retainedAngularFanSourceClearanceFactor
    let routes :=
      PositionedPeriodicCNF.scaleIncidenceRoutes
        retainedAngularFanSourceClearanceFactor
        (retainedDeduplicatedGaugedWrappedDrawingPeriodicPlanarSATIncidenceRoutes
          formula)
    let scaledClause :=
      clause.scale retainedAngularFanSourceClearanceFactor
    let route :=
      retainedFinalCoordinatedDirectOccurrenceRoute
        formula choice scaledClause literal clauseIndex literalIndex
    route.head? =
        some
          (Cell.scale retainedTerminalFanTotalRefinement
            (PositionedPeriodicCNF.canonicalClausePosition
              placement scaledClause)) ∧
      route.getLast? =
        some
          (Cell.scale retainedTerminalFanRoutingRefinement
            (PositionedPeriodicCNF.canonicalLiteralPosition
              (PeriodicEightOccurrenceSplitPositioned.placement
                placement)
              (PeriodicEightOccurrenceSplitPositioned.occurrenceClause
                (occurrencePortsOfAngularOrder
                  source.erase
                  (angularOccurrenceOrder source.erase routes))
                clauseIndex scaledClause)
              (occurrenceLiteral
                (occurrencePortsOfAngularOrder
                  source.erase
                  (angularOccurrenceOrder source.erase routes))
                clauseIndex literalIndex literal))) ∧
      OrthogonalPolyline route := by
  dsimp only
  let sourceCertificate :=
    retainedPlanarSATCertificate formula
      sourceLocal sourceWidth sourceOccurrences
      sourceClausesNonempty
  have rawEndpoints :=
    retainedDeduplicatedGaugedWrappedDrawingPeriodicPlanarSATIncidenceRoutes_endpoints
      formula
      sourceCertificate.graphWellFormed
      sourceCertificate.graphDegreeAtMostThree
      sourceCertificate.graphIsLocal
      clauseMember literalMember
  have rawHeadD :
      (retainedDeduplicatedGaugedWrappedDrawingPeriodicPlanarSATIncidenceRoutes
        formula clauseIndex literalIndex).headD (0, 0) =
        PositionedPeriodicCNF.canonicalClausePosition
          (retainedGaugedWrappedDrawingPeriodicPlanarSATPlacement formula)
          clause := by
    simp [rawEndpoints.1]
  let slot :=
    retainedFinalCoordinatedOccurrenceSlot
      formula literal clauseIndex literalIndex
  have prefixHead :
      (choice.completeRoute slot).head? =
        some
          (Cell.scale retainedTerminalFanTotalRefinement
            (PositionedPeriodicCNF.canonicalClausePosition
              ((retainedGaugedWrappedDrawingPeriodicPlanarSATPlacement
                formula).scale retainedAngularFanSourceClearanceFactor)
              (clause.scale retainedAngularFanSourceClearanceFactor))) := by
    rw [choice.completeRoute_head_eq_scaledLocalHead]
    rw [← retainedFinalDirectSourceRouteChoice_route_headD
      formula clauseIndex literalIndex choice choiceLookup]
    rw [rawHeadD, PositionedPeriodicCNF.canonicalClausePosition_scale]
    simp [retainedAngularFanSourceClearanceFactor]
  have boundary :=
    retainedFinalCoordinatedDirectOccurrenceRoute_boundary formula
      sourceLocal sourceWidth sourceOccurrences sourceClausesNonempty
      choice clauseMember literalMember choiceLookup
  have scaledClauseMember :
      (clause.scale retainedAngularFanSourceClearanceFactor, clauseIndex) ∈
        ((retainedDeduplicatedGaugedWrappedDrawingPositionedPeriodicPlanarSATFormula
          formula).scale retainedAngularFanSourceClearanceFactor).clauses.zipIdx := by
    rw [PositionedPeriodicCNF.scale_clauses, List.zipIdx_map]
    exact List.mem_map.mpr
      ⟨(clause, clauseIndex), clauseMember, rfl⟩
  have suffixHead :=
    angularOccurrenceSuffix_head?
      ((retainedGaugedWrappedDrawingPeriodicPlanarSATPlacement
        formula).scale retainedAngularFanSourceClearanceFactor)
      (angularOccurrenceOrder
        ((retainedDeduplicatedGaugedWrappedDrawingPositionedPeriodicPlanarSATFormula
          formula).scale retainedAngularFanSourceClearanceFactor).erase
        (PositionedPeriodicCNF.scaleIncidenceRoutes
          retainedAngularFanSourceClearanceFactor
          (retainedDeduplicatedGaugedWrappedDrawingPeriodicPlanarSATIncidenceRoutes
            formula)))
      (clause.scale retainedAngularFanSourceClearanceFactor)
      literal clauseIndex literalIndex
  have scaledSuffixHead :
      (scalePolyline retainedTerminalFanRoutingRefinement
        (angularOccurrenceSuffix
          ((retainedGaugedWrappedDrawingPeriodicPlanarSATPlacement
            formula).scale retainedAngularFanSourceClearanceFactor)
          (angularOccurrenceOrder
            ((retainedDeduplicatedGaugedWrappedDrawingPositionedPeriodicPlanarSATFormula
              formula).scale retainedAngularFanSourceClearanceFactor).erase
            (PositionedPeriodicCNF.scaleIncidenceRoutes
              retainedAngularFanSourceClearanceFactor
              (retainedDeduplicatedGaugedWrappedDrawingPeriodicPlanarSATIncidenceRoutes
                formula)))
          (clause.scale retainedAngularFanSourceClearanceFactor)
          literal clauseIndex literalIndex)).head? =
        some
          (Cell.scale retainedTerminalFanRoutingRefinement
            (angularFanBoundaryPositionAt
              ((retainedGaugedWrappedDrawingPeriodicPlanarSATPlacement
                formula).scale retainedAngularFanSourceClearanceFactor)
              literal.atom
              (incidenceRelativeOffset
                (clause.scale retainedAngularFanSourceClearanceFactor)
                literal)
              (angularOccurrenceIndex
                (angularOccurrenceOrder
                  ((retainedDeduplicatedGaugedWrappedDrawingPositionedPeriodicPlanarSATFormula
                    formula).scale retainedAngularFanSourceClearanceFactor).erase
                  (PositionedPeriodicCNF.scaleIncidenceRoutes
                    retainedAngularFanSourceClearanceFactor
                    (retainedDeduplicatedGaugedWrappedDrawingPeriodicPlanarSATIncidenceRoutes
                      formula)))
                literal clauseIndex literalIndex))) := by
    simpa using congrArg
      (Option.map
        (Cell.scale retainedTerminalFanRoutingRefinement))
      suffixHead
  have prefixLast := boundary.trans scaledSuffixHead
  have suffixLast :=
    angularOccurrenceSuffix_getLast?
      ((retainedDeduplicatedGaugedWrappedDrawingPositionedPeriodicPlanarSATFormula
        formula).scale retainedAngularFanSourceClearanceFactor)
      ((retainedGaugedWrappedDrawingPeriodicPlanarSATPlacement
        formula).scale retainedAngularFanSourceClearanceFactor)
      (angularOccurrenceOrder
        ((retainedDeduplicatedGaugedWrappedDrawingPositionedPeriodicPlanarSATFormula
          formula).scale retainedAngularFanSourceClearanceFactor).erase
        (PositionedPeriodicCNF.scaleIncidenceRoutes
          retainedAngularFanSourceClearanceFactor
          (retainedDeduplicatedGaugedWrappedDrawingPeriodicPlanarSATIncidenceRoutes
            formula)))
      scaledClauseMember
      literalMember
  have scaledSuffixLast :
      (scalePolyline retainedTerminalFanRoutingRefinement
        (angularOccurrenceSuffix
          ((retainedGaugedWrappedDrawingPeriodicPlanarSATPlacement
            formula).scale retainedAngularFanSourceClearanceFactor)
          (angularOccurrenceOrder
            ((retainedDeduplicatedGaugedWrappedDrawingPositionedPeriodicPlanarSATFormula
              formula).scale retainedAngularFanSourceClearanceFactor).erase
            (PositionedPeriodicCNF.scaleIncidenceRoutes
              retainedAngularFanSourceClearanceFactor
              (retainedDeduplicatedGaugedWrappedDrawingPeriodicPlanarSATIncidenceRoutes
                formula)))
          (clause.scale retainedAngularFanSourceClearanceFactor)
          literal clauseIndex literalIndex)).getLast? =
        some
          (Cell.scale retainedTerminalFanRoutingRefinement
            (PositionedPeriodicCNF.canonicalLiteralPosition
              (PeriodicEightOccurrenceSplitPositioned.placement
                ((retainedGaugedWrappedDrawingPeriodicPlanarSATPlacement
                  formula).scale retainedAngularFanSourceClearanceFactor))
              (PeriodicEightOccurrenceSplitPositioned.occurrenceClause
                (occurrencePortsOfAngularOrder
                  ((retainedDeduplicatedGaugedWrappedDrawingPositionedPeriodicPlanarSATFormula
                    formula).scale retainedAngularFanSourceClearanceFactor).erase
                  (angularOccurrenceOrder
                    ((retainedDeduplicatedGaugedWrappedDrawingPositionedPeriodicPlanarSATFormula
                      formula).scale retainedAngularFanSourceClearanceFactor).erase
                    (PositionedPeriodicCNF.scaleIncidenceRoutes
                      retainedAngularFanSourceClearanceFactor
                      (retainedDeduplicatedGaugedWrappedDrawingPeriodicPlanarSATIncidenceRoutes
                        formula))))
                  clauseIndex
                  (clause.scale retainedAngularFanSourceClearanceFactor))
              (occurrenceLiteral
                (occurrencePortsOfAngularOrder
                  ((retainedDeduplicatedGaugedWrappedDrawingPositionedPeriodicPlanarSATFormula
                    formula).scale retainedAngularFanSourceClearanceFactor).erase
                  (angularOccurrenceOrder
                    ((retainedDeduplicatedGaugedWrappedDrawingPositionedPeriodicPlanarSATFormula
                      formula).scale retainedAngularFanSourceClearanceFactor).erase
                    (PositionedPeriodicCNF.scaleIncidenceRoutes
                      retainedAngularFanSourceClearanceFactor
                      (retainedDeduplicatedGaugedWrappedDrawingPeriodicPlanarSATIncidenceRoutes
                        formula))))
                  clauseIndex literalIndex literal))) := by
    simpa using congrArg
      (Option.map
        (Cell.scale retainedTerminalFanRoutingRefinement))
      suffixLast
  have prefixOrthogonal :
      OrthogonalPolyline (choice.completeRoute slot) :=
    choice.completeRoute_orthogonal slot
  have suffixOrthogonal :
      OrthogonalPolyline
        (scalePolyline retainedTerminalFanRoutingRefinement
          (angularOccurrenceSuffix
            ((retainedGaugedWrappedDrawingPeriodicPlanarSATPlacement
              formula).scale retainedAngularFanSourceClearanceFactor)
            (angularOccurrenceOrder
              ((retainedDeduplicatedGaugedWrappedDrawingPositionedPeriodicPlanarSATFormula
                formula).scale retainedAngularFanSourceClearanceFactor).erase
              (PositionedPeriodicCNF.scaleIncidenceRoutes
                retainedAngularFanSourceClearanceFactor
                (retainedDeduplicatedGaugedWrappedDrawingPeriodicPlanarSATIncidenceRoutes
                  formula)))
            (clause.scale retainedAngularFanSourceClearanceFactor)
            literal clauseIndex literalIndex)) :=
    (angularOccurrenceSuffix_orthogonal
      ((retainedGaugedWrappedDrawingPeriodicPlanarSATPlacement
        formula).scale retainedAngularFanSourceClearanceFactor)
      (angularOccurrenceOrder
        ((retainedDeduplicatedGaugedWrappedDrawingPositionedPeriodicPlanarSATFormula
          formula).scale retainedAngularFanSourceClearanceFactor).erase
        (PositionedPeriodicCNF.scaleIncidenceRoutes
          retainedAngularFanSourceClearanceFactor
          (retainedDeduplicatedGaugedWrappedDrawingPeriodicPlanarSATIncidenceRoutes
            formula)))
      (clause.scale retainedAngularFanSourceClearanceFactor)
      literal clauseIndex literalIndex).scalePolyline
        (by simp [retainedTerminalFanRoutingRefinement])
  unfold retainedFinalCoordinatedDirectOccurrenceRoute
  refine ⟨joinAtEndpoint_head? prefixHead, ?_, ?_⟩
  · exact joinAtEndpoint_getLast?
      prefixLast scaledSuffixHead scaledSuffixLast
  · exact prefixOrthogonal.joinAtEndpoint
      suffixOrthogonal prefixLast scaledSuffixHead

end PeriodicOrthocrossing
end LeanTrominoes
