import LeanTrominoes.RetainedAngularFanFinalCoordinatedRoutes
import LeanTrominoes.RetainedAngularFanOccurrenceSplice
import LeanTrominoes.RetainedAngularFanSourceEscapedSplice
import LeanTrominoes.RetainedAngularTerminalDataProfile

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
        (finalCoordinatedSource formula).clauses.zipIdx)
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

/-- Canonical endpoints of one genuine incidence in the named final source
interface. -/
theorem finalCoordinatedSourceRoutes_endpoints
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (sourceLocal : formula.IsLocal)
    (sourceWidth : formula.WidthAtMost 3)
    (sourceOccurrences : formula.OccurrencesAtMost 3)
    (sourceClausesNonempty :
      ∀ clause ∈ formula.clauses, clause ≠ [])
    {clause :
      PositionedPeriodicClause
        (WrappedPeriodicPlanarSATVariable Variable)}
    {clauseIndex : Nat}
    (clauseMember :
      (clause, clauseIndex) ∈
        (finalCoordinatedSource formula).clauses.zipIdx)
    {literal :
      PeriodicLiteral (WrappedPeriodicPlanarSATVariable Variable)}
    {literalIndex : Nat}
    (literalMember :
      (literal, literalIndex) ∈ clause.literals.zipIdx) :
    (finalCoordinatedSourceRoutes
        formula clauseIndex literalIndex).head? =
        some
          (PositionedPeriodicCNF.canonicalClausePosition
            (finalCoordinatedPlacement formula) clause) ∧
      (finalCoordinatedSourceRoutes
        formula clauseIndex literalIndex).getLast? =
        some
          (PositionedPeriodicCNF.canonicalLiteralPosition
            (finalCoordinatedPlacement formula) clause literal) := by
  let sourceCertificate :=
    retainedPlanarSATCertificate formula
      sourceLocal sourceWidth sourceOccurrences
      sourceClausesNonempty
  exact
    retainedDeduplicatedGaugedWrappedDrawingPeriodicPlanarSATIncidenceRoutes_endpoints
      formula
      sourceCertificate.graphWellFormed
      sourceCertificate.graphDegreeAtMostThree
      sourceCertificate.graphIsLocal
      clauseMember literalMember

/-- Every genuine incidence in the named final source has a terminal
segment. -/
theorem finalCoordinatedSourceRoutes_length_ge_two
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (sourceLocal : formula.IsLocal)
    (sourceWidth : formula.WidthAtMost 3)
    (sourceOccurrences : formula.OccurrencesAtMost 3)
    (sourceClausesNonempty :
      ∀ clause ∈ formula.clauses, clause ≠ [])
    {clause :
      PositionedPeriodicClause
        (WrappedPeriodicPlanarSATVariable Variable)}
    {clauseIndex : Nat}
    (clauseMember :
      (clause, clauseIndex) ∈
        (finalCoordinatedSource formula).clauses.zipIdx)
    {literal :
      PeriodicLiteral (WrappedPeriodicPlanarSATVariable Variable)}
    {literalIndex : Nat}
    (literalMember :
      (literal, literalIndex) ∈ clause.literals.zipIdx) :
    2 ≤
      (finalCoordinatedSourceRoutes
        formula clauseIndex literalIndex).length := by
  let sourceCertificate :=
    retainedPlanarSATCertificate formula
      sourceLocal sourceWidth sourceOccurrences
      sourceClausesNonempty
  let retainedClausesNonempty :=
    retainedDrawingPlanarSATFormula_clausesNonempty_of_source
      formula sourceClausesNonempty
  exact
    retainedDeduplicatedGaugedWrappedDrawingPeriodicPlanarSATIncidenceRoutes_length_ge_two
      formula
      sourceCertificate.graphWellFormed
      sourceCertificate.graphDegreeAtMostThree
      sourceCertificate.graphIsLocal
      retainedClausesNonempty
      clauseMember literalMember

/-- Every genuine incidence in the named final source follows retained ray
directions. -/
theorem finalCoordinatedSourceRoutes_retainedRay
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (sourceLocal : formula.IsLocal)
    (sourceWidth : formula.WidthAtMost 3)
    (sourceOccurrences : formula.OccurrencesAtMost 3)
    (sourceClausesNonempty :
      ∀ clause ∈ formula.clauses, clause ≠ [])
    {clause :
      PositionedPeriodicClause
        (WrappedPeriodicPlanarSATVariable Variable)}
    {clauseIndex : Nat}
    (clauseMember :
      (clause, clauseIndex) ∈
        (finalCoordinatedSource formula).clauses.zipIdx)
    {literal :
      PeriodicLiteral (WrappedPeriodicPlanarSATVariable Variable)}
    {literalIndex : Nat}
    (literalMember :
      (literal, literalIndex) ∈ clause.literals.zipIdx) :
    RetainedRayPolyline
      (finalCoordinatedSourceRoutes
        formula clauseIndex literalIndex) := by
  let sourceCertificate :=
    retainedPlanarSATCertificate formula
      sourceLocal sourceWidth sourceOccurrences
      sourceClausesNonempty
  let retainedClausesNonempty :=
    retainedDrawingPlanarSATFormula_clausesNonempty_of_source
      formula sourceClausesNonempty
  exact
    retainedDeduplicatedGaugedWrappedDrawingPeriodicPlanarSATIncidenceRoutes_retainedRay
      formula
      sourceCertificate.graphWellFormed
      sourceCertificate.graphDegreeAtMostThree
      sourceCertificate.graphIsLocal
      retainedClausesNonempty
      (clause, clauseIndex) clauseMember
      (literal, literalIndex) literalMember

/-- The terminal vector of one genuine final source incidence classifies to
the total terminal-data projection. -/
theorem finalCoordinatedSourceRoute_classified
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (sourceLocal : formula.IsLocal)
    (sourceWidth : formula.WidthAtMost 3)
    (sourceOccurrences : formula.OccurrencesAtMost 3)
    (sourceClausesNonempty :
      ∀ clause ∈ formula.clauses, clause ≠ [])
    {clause :
      PositionedPeriodicClause
        (WrappedPeriodicPlanarSATVariable Variable)}
    {clauseIndex : Nat}
    (clauseMember :
      (clause, clauseIndex) ∈
        (finalCoordinatedSource formula).clauses.zipIdx)
    {literal :
      PeriodicLiteral (WrappedPeriodicPlanarSATVariable Variable)}
    {literalIndex : Nat}
    (literalMember :
      (literal, literalIndex) ∈ clause.literals.zipIdx) :
    let rawRoute :=
      finalCoordinatedSourceRoutes formula clauseIndex literalIndex
    let rawTerminal :=
      classifiedRetainedTerminalData
        (routeTerminalVector rawRoute)
    retainedTerminalDirectionClassify
        (routeTerminalVector rawRoute) =
      some rawTerminal := by
  dsimp only
  let rawRoute :=
    finalCoordinatedSourceRoutes formula clauseIndex literalIndex
  let rawTerminal :=
    classifiedRetainedTerminalData
      (routeTerminalVector rawRoute)
  have rawLength :=
    finalCoordinatedSourceRoutes_length_ge_two
      formula sourceLocal sourceWidth sourceOccurrences
      sourceClausesNonempty
      clauseMember literalMember
  have rawRetained :=
    finalCoordinatedSourceRoutes_retainedRay
      formula sourceLocal sourceWidth sourceOccurrences
      sourceClausesNonempty
      clauseMember literalMember
  exact
    retainedTerminalDirectionClassify_classifiedRetainedTerminalData
      (rawRetained.routeTerminalVector_retained rawLength)

/-- Source scaling preserves the minimum length of a genuine final
incidence. -/
theorem finalCoordinatedScaledSourceRoute_length_ge_two
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (sourceLocal : formula.IsLocal)
    (sourceWidth : formula.WidthAtMost 3)
    (sourceOccurrences : formula.OccurrencesAtMost 3)
    (sourceClausesNonempty :
      ∀ clause ∈ formula.clauses, clause ≠ [])
    {clause :
      PositionedPeriodicClause
        (WrappedPeriodicPlanarSATVariable Variable)}
    {clauseIndex : Nat}
    (clauseMember :
      (clause, clauseIndex) ∈
        (finalCoordinatedSource formula).clauses.zipIdx)
    {literal :
      PeriodicLiteral (WrappedPeriodicPlanarSATVariable Variable)}
    {literalIndex : Nat}
    (literalMember :
      (literal, literalIndex) ∈ clause.literals.zipIdx) :
    2 ≤
      (scalePolyline retainedAngularFanSourceClearanceFactor
        (finalCoordinatedSourceRoutes
          formula clauseIndex literalIndex)).length := by
  simpa [scalePolyline] using
    finalCoordinatedSourceRoutes_length_ge_two
      formula sourceLocal sourceWidth sourceOccurrences
      sourceClausesNonempty clauseMember literalMember

/-- Source scaling transports the exact terminal classification of a
genuine final incidence. -/
theorem finalCoordinatedScaledSourceRoute_classified
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (sourceLocal : formula.IsLocal)
    (sourceWidth : formula.WidthAtMost 3)
    (sourceOccurrences : formula.OccurrencesAtMost 3)
    (sourceClausesNonempty :
      ∀ clause ∈ formula.clauses, clause ≠ [])
    {clause :
      PositionedPeriodicClause
        (WrappedPeriodicPlanarSATVariable Variable)}
    {clauseIndex : Nat}
    (clauseMember :
      (clause, clauseIndex) ∈
        (finalCoordinatedSource formula).clauses.zipIdx)
    {literal :
      PeriodicLiteral (WrappedPeriodicPlanarSATVariable Variable)}
    {literalIndex : Nat}
    (literalMember :
      (literal, literalIndex) ∈ clause.literals.zipIdx) :
    let rawRoute :=
      finalCoordinatedSourceRoutes formula clauseIndex literalIndex
    let rawTerminal :=
      classifiedRetainedTerminalData
        (routeTerminalVector rawRoute)
    retainedTerminalDirectionClassify
        (routeTerminalVector
          (scalePolyline retainedAngularFanSourceClearanceFactor
            rawRoute)) =
      some
        (scaleRetainedTerminalData
          retainedAngularFanSourceClearanceFactor rawTerminal) := by
  dsimp only
  exact
    routeTerminalVector_scale_classified
      retainedAngularFanSourceClearanceFactor_pos
      (finalCoordinatedSourceRoute_classified
        formula sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty clauseMember literalMember)

/-- Source scaling preserves the retained-ray certificate of a genuine
final incidence. -/
theorem finalCoordinatedScaledSourceRoute_retainedRay
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (sourceLocal : formula.IsLocal)
    (sourceWidth : formula.WidthAtMost 3)
    (sourceOccurrences : formula.OccurrencesAtMost 3)
    (sourceClausesNonempty :
      ∀ clause ∈ formula.clauses, clause ≠ [])
    {clause :
      PositionedPeriodicClause
        (WrappedPeriodicPlanarSATVariable Variable)}
    {clauseIndex : Nat}
    (clauseMember :
      (clause, clauseIndex) ∈
        (finalCoordinatedSource formula).clauses.zipIdx)
    {literal :
      PeriodicLiteral (WrappedPeriodicPlanarSATVariable Variable)}
    {literalIndex : Nat}
    (literalMember :
      (literal, literalIndex) ∈ clause.literals.zipIdx) :
    RetainedRayPolyline
      (scalePolyline retainedAngularFanSourceClearanceFactor
        (finalCoordinatedSourceRoutes
          formula clauseIndex literalIndex)) :=
  (finalCoordinatedSourceRoutes_retainedRay
    formula sourceLocal sourceWidth sourceOccurrences
    sourceClausesNonempty clauseMember literalMember).scale
      (by native_decide)

/-- Source scaling transports the clause endpoint of a genuine final
incidence. -/
theorem finalCoordinatedScaledSourceRoute_head
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (sourceLocal : formula.IsLocal)
    (sourceWidth : formula.WidthAtMost 3)
    (sourceOccurrences : formula.OccurrencesAtMost 3)
    (sourceClausesNonempty :
      ∀ clause ∈ formula.clauses, clause ≠ [])
    {clause :
      PositionedPeriodicClause
        (WrappedPeriodicPlanarSATVariable Variable)}
    {clauseIndex : Nat}
    (clauseMember :
      (clause, clauseIndex) ∈
        (finalCoordinatedSource formula).clauses.zipIdx)
    {literal :
      PeriodicLiteral (WrappedPeriodicPlanarSATVariable Variable)}
    {literalIndex : Nat}
    (literalMember :
      (literal, literalIndex) ∈ clause.literals.zipIdx) :
    (scalePolyline retainedAngularFanSourceClearanceFactor
      (finalCoordinatedSourceRoutes
        formula clauseIndex literalIndex)).head? =
      some
        (Cell.scale retainedAngularFanSourceClearanceFactor
          (PositionedPeriodicCNF.canonicalClausePosition
            (finalCoordinatedPlacement formula) clause)) := by
  simpa [scalePolyline] using congrArg
    (Option.map
      (Cell.scale retainedAngularFanSourceClearanceFactor))
    (finalCoordinatedSourceRoutes_endpoints
      formula sourceLocal sourceWidth sourceOccurrences
      sourceClausesNonempty clauseMember literalMember).1

/-- The classified terminal length of every genuine final incidence is
positive. -/
theorem finalCoordinatedSourceRoute_terminal_length_positive
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (sourceLocal : formula.IsLocal)
    (sourceWidth : formula.WidthAtMost 3)
    (sourceOccurrences : formula.OccurrencesAtMost 3)
    (sourceClausesNonempty :
      ∀ clause ∈ formula.clauses, clause ≠ [])
    {clause :
      PositionedPeriodicClause
        (WrappedPeriodicPlanarSATVariable Variable)}
    {clauseIndex : Nat}
    (clauseMember :
      (clause, clauseIndex) ∈
        (finalCoordinatedSource formula).clauses.zipIdx)
    {literal :
      PeriodicLiteral (WrappedPeriodicPlanarSATVariable Variable)}
    {literalIndex : Nat}
    (literalMember :
      (literal, literalIndex) ∈ clause.literals.zipIdx) :
    0 <
      (classifiedRetainedTerminalData
        (routeTerminalVector
          (finalCoordinatedSourceRoutes
            formula clauseIndex literalIndex))).2 := by
  apply classifiedRetainedTerminalData_length_positive
  exact
    (finalCoordinatedSourceRoutes_retainedRay
      formula sourceLocal sourceWidth sourceOccurrences
      sourceClausesNonempty clauseMember literalMember).routeTerminalVector_retained
        (finalCoordinatedSourceRoutes_length_ge_two
          formula sourceLocal sourceWidth sourceOccurrences
          sourceClausesNonempty clauseMember literalMember)

/-- Every scaled genuine final terminal has room for the fixed delayed-lane
escape. -/
theorem finalCoordinatedScaledSourceRoute_escapeFits
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (sourceLocal : formula.IsLocal)
    (sourceWidth : formula.WidthAtMost 3)
    (sourceOccurrences : formula.OccurrencesAtMost 3)
    (sourceClausesNonempty :
      ∀ clause ∈ formula.clauses, clause ≠ [])
    {clause :
      PositionedPeriodicClause
        (WrappedPeriodicPlanarSATVariable Variable)}
    {clauseIndex : Nat}
    (clauseMember :
      (clause, clauseIndex) ∈
        (finalCoordinatedSource formula).clauses.zipIdx)
    {literal :
      PeriodicLiteral (WrappedPeriodicPlanarSATVariable Variable)}
    {literalIndex : Nat}
    (literalMember :
      (literal, literalIndex) ∈ clause.literals.zipIdx) :
    let rawRoute :=
      finalCoordinatedSourceRoutes formula clauseIndex literalIndex
    let rawTerminal :=
      classifiedRetainedTerminalData
        (routeTerminalVector rawRoute)
    retainedTerminalFanOuterSourceEscapeLength ≤
      retainedTerminalFanOuterRadialLength
        (scaleRetainedTerminalData
          retainedAngularFanSourceClearanceFactor rawTerminal) := by
  dsimp only
  rw [show retainedAngularFanSourceClearanceFactor = 4 by rfl]
  exact
    retainedTerminalFanOuterSourceEscape_fits_scale_four
      (classifiedRetainedTerminalData
        (routeTerminalVector
          (finalCoordinatedSourceRoutes
            formula clauseIndex literalIndex)))
      (finalCoordinatedSourceRoute_terminal_length_positive
        formula sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty clauseMember literalMember)

/-- The delayed-lane fallback prefix starts at the scaled source clause,
reaches its explicit fan-boundary point, and remains orthogonal. -/
theorem retainedFinalEscapedFallbackBoundaryPrefix_valid
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (sourceLocal : formula.IsLocal)
    (sourceWidth : formula.WidthAtMost 3)
    (sourceOccurrences : formula.OccurrencesAtMost 3)
    (sourceClausesNonempty :
      ∀ clause ∈ formula.clauses, clause ≠ [])
    {clause :
      PositionedPeriodicClause
        (WrappedPeriodicPlanarSATVariable Variable)}
    {clauseIndex : Nat}
    (clauseMember :
      (clause, clauseIndex) ∈
        (finalCoordinatedSource formula).clauses.zipIdx)
    {literal :
      PeriodicLiteral (WrappedPeriodicPlanarSATVariable Variable)}
    {literalIndex : Nat}
    (literalMember :
      (literal, literalIndex) ∈ clause.literals.zipIdx) :
    let rawRoute :=
      finalCoordinatedSourceRoutes formula clauseIndex literalIndex
    let rawTerminal :=
      classifiedRetainedTerminalData
        (routeTerminalVector rawRoute)
    let slot :=
      retainedFinalCoordinatedOccurrenceSlot
        formula literal clauseIndex literalIndex
    let boundaryPrefix :=
      PeriodicEightOccurrenceSplit.retainedAngularFanEscapedSplicedBoundaryRoute
        (scalePolyline retainedAngularFanSourceClearanceFactor
          rawRoute)
        (scaleRetainedTerminalData
          retainedAngularFanSourceClearanceFactor rawTerminal)
        slot
    boundaryPrefix.head? =
        some
          (Cell.scale retainedTerminalFanTotalRefinement
            (Cell.scale retainedAngularFanSourceClearanceFactor
              (PositionedPeriodicCNF.canonicalClausePosition
                (finalCoordinatedPlacement formula) clause))) ∧
      boundaryPrefix.getLast? =
        some
          (Cell.add
            (Cell.scale retainedTerminalFanTotalRefinement
              ((scalePolyline retainedAngularFanSourceClearanceFactor
                rawRoute).getLastD (0, 0)))
            (Cell.scale retainedTerminalFanRoutingRefinement
              (angularFanBoundaryOffset slot.val))) ∧
      OrthogonalPolyline boundaryPrefix := by
  dsimp only
  let rawRoute :=
    finalCoordinatedSourceRoutes formula clauseIndex literalIndex
  let rawTerminal :=
    classifiedRetainedTerminalData
      (routeTerminalVector rawRoute)
  let slot :=
    retainedFinalCoordinatedOccurrenceSlot
      formula literal clauseIndex literalIndex
  exact
    PeriodicEightOccurrenceSplit.retainedAngularFanEscapedSplicedBoundaryRoute_valid
      (scalePolyline retainedAngularFanSourceClearanceFactor rawRoute)
      (scaleRetainedTerminalData
        retainedAngularFanSourceClearanceFactor rawTerminal)
      slot
      (finalCoordinatedScaledSourceRoute_length_ge_two
        formula sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty clauseMember literalMember)
      (finalCoordinatedScaledSourceRoute_classified
        formula sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty clauseMember literalMember)
      (finalCoordinatedScaledSourceRoute_retainedRay
        formula sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty clauseMember literalMember)
      (finalCoordinatedScaledSourceRoute_head
        formula sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty clauseMember literalMember)
      (finalCoordinatedScaledSourceRoute_escapeFits
        formula sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty clauseMember literalMember)

/-- The delayed-lane fallback prefix reaches exactly the same fan-boundary
point as the established Figure 7 occurrence suffix. -/
theorem retainedFinalEscapedFallbackOccurrenceRoute_boundary
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (sourceLocal : formula.IsLocal)
    (sourceWidth : formula.WidthAtMost 3)
    (sourceOccurrences : formula.OccurrencesAtMost 3)
    (sourceClausesNonempty :
      ∀ clause ∈ formula.clauses, clause ≠ [])
    {clause :
      PositionedPeriodicClause
        (WrappedPeriodicPlanarSATVariable Variable)}
    {clauseIndex : Nat}
    (clauseMember :
      (clause, clauseIndex) ∈
        (finalCoordinatedSource formula).clauses.zipIdx)
    {literal :
      PeriodicLiteral (WrappedPeriodicPlanarSATVariable Variable)}
    {literalIndex : Nat}
    (literalMember :
      (literal, literalIndex) ∈ clause.literals.zipIdx) :
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
    let rawRoute :=
      finalCoordinatedSourceRoutes formula clauseIndex literalIndex
    let rawTerminal :=
      classifiedRetainedTerminalData
        (routeTerminalVector rawRoute)
    let slot :=
      retainedFinalCoordinatedOccurrenceSlot
        formula literal clauseIndex literalIndex
    (PeriodicEightOccurrenceSplit.retainedAngularFanEscapedSplicedBoundaryRoute
      (scalePolyline retainedAngularFanSourceClearanceFactor
        rawRoute)
      (scaleRetainedTerminalData
        retainedAngularFanSourceClearanceFactor rawTerminal)
      slot).getLast? =
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
  let rawRoute :=
    finalCoordinatedSourceRoutes formula clauseIndex literalIndex
  let slot :=
    retainedFinalCoordinatedOccurrenceSlot
      formula literal clauseIndex literalIndex
  have prefixValid :=
    retainedFinalEscapedFallbackBoundaryPrefix_valid formula
      sourceLocal sourceWidth sourceOccurrences sourceClausesNonempty
      clauseMember literalMember
  have rawEndpoints :=
    retainedDeduplicatedGaugedWrappedDrawingPeriodicPlanarSATIncidenceRoutes_endpoints
      formula
      sourceCertificate.graphWellFormed
      sourceCertificate.graphDegreeAtMostThree
      sourceCertificate.graphIsLocal
      clauseMember literalMember
  have rawLastD :
      rawRoute.getLastD (0, 0) =
        PositionedPeriodicCNF.canonicalLiteralPosition
          (finalCoordinatedPlacement formula)
          clause literal := by
    simp [rawRoute, finalCoordinatedSourceRoutes,
      finalCoordinatedPlacement, List.getLastD_eq_getLast?,
      rawEndpoints.2]
  have fits :
      FitsEightSlots
        (angularOccurrenceOrder
          ((finalCoordinatedSource formula).scale
            retainedAngularFanSourceClearanceFactor).erase
          (PositionedPeriodicCNF.scaleIncidenceRoutes
            retainedAngularFanSourceClearanceFactor
            (finalCoordinatedSourceRoutes formula))) := by
    rw [PositionedPeriodicCNF.erase_scale,
      angularOccurrenceOrder_scaleIncidenceRoutes
        (finalCoordinatedSource formula).erase
        retainedAngularFanSourceClearanceFactor_pos
        (finalCoordinatedSourceRoutes formula)]
    simpa [finalCoordinatedSource, finalCoordinatedSourceRoutes,
      retainedDrawingAngularOccurrenceOrder,
      retainedPlanarSATFormula] using
      retainedDrawingAngularOccurrenceOrder_fitsEightSlots
        sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty
  have scaledClauseMember :
      (clause.scale retainedAngularFanSourceClearanceFactor, clauseIndex) ∈
        ((finalCoordinatedSource formula).scale
          retainedAngularFanSourceClearanceFactor).clauses.zipIdx := by
    rw [PositionedPeriodicCNF.scale_clauses, List.zipIdx_map]
    exact List.mem_map.mpr
      ⟨(clause, clauseIndex), clauseMember, rfl⟩
  have taggedMember :=
    taggedLiteral_mem_of_positioned_members
      ((finalCoordinatedSource formula).scale
        retainedAngularFanSourceClearanceFactor)
      scaledClauseMember literalMember
  have copyMember :
      (literal.atom, clauseIndex, literalIndex) ∈
        occurrenceVariables
          ((finalCoordinatedSource formula).scale
            retainedAngularFanSourceClearanceFactor).erase
          literal.atom :=
    occurrenceVariables_mem _ taggedMember
  have indexLt :
      angularOccurrenceIndex
          (angularOccurrenceOrder
            ((finalCoordinatedSource formula).scale
              retainedAngularFanSourceClearanceFactor).erase
            (PositionedPeriodicCNF.scaleIncidenceRoutes
              retainedAngularFanSourceClearanceFactor
              (finalCoordinatedSourceRoutes formula)))
          literal clauseIndex literalIndex < 8 := by
    simpa [angularOccurrenceIndex, indexedOccurrence,
      retainedAngularTerminalSlot_val] using
      (retainedAngularTerminalSlot
        ((finalCoordinatedSource formula).scale
          retainedAngularFanSourceClearanceFactor).erase
        (PositionedPeriodicCNF.scaleIncidenceRoutes
          retainedAngularFanSourceClearanceFactor
          (finalCoordinatedSourceRoutes formula))
        fits literal.atom
        (literal.atom, clauseIndex, literalIndex)
        copyMember).isLt
  have slotVal :
      slot.val =
        angularOccurrenceIndex
          (angularOccurrenceOrder
            ((finalCoordinatedSource formula).scale
              retainedAngularFanSourceClearanceFactor).erase
            (PositionedPeriodicCNF.scaleIncidenceRoutes
              retainedAngularFanSourceClearanceFactor
              (finalCoordinatedSourceRoutes formula)))
          literal clauseIndex literalIndex := by
    exact boundedRetainedTerminalSlot_val_of_lt indexLt
  rw [prefixValid.2.1]
  rw [scalePolyline_getLastD, rawLastD]
  simp only [angularOccurrenceSuffix_head?, scalePolyline,
    List.head?_map, Option.map_some]
  rw [angularFanBoundaryPositionAt_eq_scaledCenter_add_offset]
  rw [slotVal]
  rw [PeriodicVariablePlacement.translation_scale]
  simp only [PositionedPeriodicCNF.canonicalLiteralPosition,
    incidenceRelativeOffset]
  rcases positionEq :
      (finalCoordinatedPlacement formula).position
        literal.atom with ⟨x, y⟩
  rcases translationEq :
      (finalCoordinatedPlacement formula).translation
        (Cell.sub literal.offset
          (PeriodicCNF.clauseAnchor clause.literals)) with ⟨dx, dy⟩
  rcases
      angularFanBoundaryOffset
        (angularOccurrenceIndex
          (angularOccurrenceOrder
            ((finalCoordinatedSource formula).scale
              retainedAngularFanSourceClearanceFactor).erase
            (PositionedPeriodicCNF.scaleIncidenceRoutes
              retainedAngularFanSourceClearanceFactor
              (finalCoordinatedSourceRoutes formula)))
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

/-- Every genuine delayed-lane fallback occurrence route has the same
canonical endpoints as the established fixed-eight route and is
orthogonal. -/
theorem retainedFinalEscapedFallbackOccurrenceRoute_valid
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (sourceLocal : formula.IsLocal)
    (sourceWidth : formula.WidthAtMost 3)
    (sourceOccurrences : formula.OccurrencesAtMost 3)
    (sourceClausesNonempty :
      ∀ clause ∈ formula.clauses, clause ≠ [])
    {clause :
      PositionedPeriodicClause
        (WrappedPeriodicPlanarSATVariable Variable)}
    {clauseIndex : Nat}
    (clauseMember :
      (clause, clauseIndex) ∈
        (finalCoordinatedSource formula).clauses.zipIdx)
    {literal :
      PeriodicLiteral (WrappedPeriodicPlanarSATVariable Variable)}
    {literalIndex : Nat}
    (literalMember :
      (literal, literalIndex) ∈ clause.literals.zipIdx) :
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
    let scaledClause :=
      clause.scale retainedAngularFanSourceClearanceFactor
    let route :=
      retainedFinalEscapedFallbackOccurrenceRoute
        formula scaledClause literal clauseIndex literalIndex
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
  let scaledClause :=
    clause.scale retainedAngularFanSourceClearanceFactor
  let rawRoute :=
    finalCoordinatedSourceRoutes formula clauseIndex literalIndex
  let rawTerminal :=
    classifiedRetainedTerminalData
      (routeTerminalVector rawRoute)
  let slot :=
    retainedFinalCoordinatedOccurrenceSlot
      formula literal clauseIndex literalIndex
  let boundaryPrefix :=
    PeriodicEightOccurrenceSplit.retainedAngularFanEscapedSplicedBoundaryRoute
      (scalePolyline retainedAngularFanSourceClearanceFactor rawRoute)
      (scaleRetainedTerminalData
        retainedAngularFanSourceClearanceFactor rawTerminal)
      slot
  have prefixValid :=
    retainedFinalEscapedFallbackBoundaryPrefix_valid
      formula sourceLocal sourceWidth sourceOccurrences
      sourceClausesNonempty clauseMember literalMember
  have prefixHead :
      boundaryPrefix.head? =
        some
          (Cell.scale retainedTerminalFanTotalRefinement
            (PositionedPeriodicCNF.canonicalClausePosition
              placement scaledClause)) := by
    rw [prefixValid.1]
    exact congrArg some
      (congrArg (Cell.scale retainedTerminalFanTotalRefinement)
        (PositionedPeriodicCNF.canonicalClausePosition_scale
          retainedAngularFanSourceClearanceFactor
          (finalCoordinatedPlacement formula) clause).symm)
  have prefixBoundary :=
    retainedFinalEscapedFallbackOccurrenceRoute_boundary
      formula sourceLocal sourceWidth sourceOccurrences
      sourceClausesNonempty clauseMember literalMember
  have scaledClauseMember :
      (scaledClause, clauseIndex) ∈ source.clauses.zipIdx := by
    rw [PositionedPeriodicCNF.scale_clauses, List.zipIdx_map]
    exact List.mem_map.mpr
      ⟨(clause, clauseIndex), clauseMember, rfl⟩
  have valid :=
    PeriodicEightOccurrenceSplit.retainedAngularFanOccurrenceRoute_valid_of_prefix
      source placement routes scaledClauseMember literalMember
      boundaryPrefix
      (Cell.scale retainedTerminalFanTotalRefinement
        (PositionedPeriodicCNF.canonicalClausePosition
          placement scaledClause))
      prefixHead prefixBoundary prefixValid.2.2
  simpa [retainedFinalEscapedFallbackOccurrenceRoute,
    source, placement, routes, scaledClause,
    rawRoute, rawTerminal, slot, boundaryPrefix] using valid

end PeriodicOrthocrossing
end LeanTrominoes
