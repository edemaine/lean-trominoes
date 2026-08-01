import LeanTrominoes.RetainedAngularFanFinalCoordinatedVariableRouteOrder
import LeanTrominoes.PeriodicCNFPlanarFixedEightOneInThreeVariableRouteOrder

/-!
# Nondegeneracy of final coordinated routes

Figure 9 preserves an inherited route's terminal direction provided that
the inherited route contains a genuine final edge.  This file first proves
that fact for the complete retained angular-fan family, including appended
implication-cycle routes.  It then specializes through source-first scaling
and transfers nondegeneracy to the final coordinated family.
-/

namespace LeanTrominoes
namespace PeriodicEightOccurrenceSplit

open PeriodicEightOccurrenceSplitPositioned
open PeriodicThreeSATThree

set_option maxHeartbeats 2000000

/-- Joining a nonempty prefix to a suffix containing an edge leaves an
edge in the completed route. -/
private theorem joinAtEndpoint_length_ge_two_of_head
    {α : Type*} {first second : List α} {point : α}
    (firstHead : first.head? = some point)
    (secondLength : 2 ≤ second.length) :
    2 ≤ (joinAtEndpoint first second).length := by
  cases first with
  | nil =>
      simp at firstHead
  | cons firstPoint firstTail =>
      cases second with
      | nil =>
          simp at secondLength
      | cons secondPoint secondTail =>
          cases secondTail with
          | nil =>
              simp at secondLength
          | cons secondNext secondRest =>
              simp [joinAtEndpoint]
              omega

/-- Every genuine route in the complete retained angular-fan family
contains a final edge. -/
theorem retainedAngularFanSplicedIncidenceRoutes_length_ge_two
    {Variable : Type*} [DecidableEq Variable]
    (source : PositionedPeriodicCNF Variable)
    (placement : PeriodicVariablePlacement Variable)
    (routes : PositionedPeriodicCNF.IncidenceRoutes)
    (fits :
      FitsEightSlots
        (angularOccurrenceOrder source.erase routes))
    (certificate :
      RetainedOccurrenceTerminalCertificate
        source.erase routes)
    (endpoints :
      ∀ clause clauseIndex,
        (clause, clauseIndex) ∈ source.clauses.zipIdx →
        ∀ literal literalIndex,
          (literal, literalIndex) ∈ clause.literals.zipIdx →
          (routes clauseIndex literalIndex).head? =
              some
                (PositionedPeriodicCNF.canonicalClausePosition
                  placement clause) ∧
            (routes clauseIndex literalIndex).getLast? =
              some
                (PositionedPeriodicCNF.canonicalLiteralPosition
                  placement clause literal))
    (lengths :
      ∀ clause clauseIndex,
        (clause, clauseIndex) ∈ source.clauses.zipIdx →
        ∀ literal literalIndex,
          (literal, literalIndex) ∈ clause.literals.zipIdx →
          2 ≤ (routes clauseIndex literalIndex).length)
    (retainedRoutes :
      ∀ clause clauseIndex,
        (clause, clauseIndex) ∈ source.clauses.zipIdx →
        ∀ literal literalIndex,
          (literal, literalIndex) ∈ clause.literals.zipIdx →
          RetainedRayPolyline
            (routes clauseIndex literalIndex))
    {clause :
      PositionedPeriodicClause
        (ThreeOccurrenceVariable Variable)}
    {clauseIndex : Nat}
    (clauseMember :
      (clause, clauseIndex) ∈
        (retainedAngularFanRefinedFormula
          source placement routes).clauses.zipIdx)
    {literal :
      PeriodicLiteral
        (ThreeOccurrenceVariable Variable)}
    {literalIndex : Nat}
    (literalMember :
      (literal, literalIndex) ∈ clause.literals.zipIdx) :
    2 ≤
      (retainedAngularFanSplicedIncidenceRoutes
        source placement routes
        clauseIndex literalIndex).length := by
  let order :=
    angularOccurrenceOrder source.erase routes
  let occurrencePorts :=
    occurrencePortsOfAngularOrder source.erase order
  rw [retainedAngularFanRefinedFormula,
    PositionedPeriodicCNF.scale_clauses,
    List.zipIdx_map] at clauseMember
  rcases List.mem_map.mp clauseMember with
    ⟨taggedClause, taggedClauseMember, taggedClauseEqual⟩
  rcases taggedClause with ⟨baseClause, baseIndex⟩
  have clauseIndexEqual :
      baseIndex = clauseIndex :=
    congrArg Prod.snd taggedClauseEqual
  have scaledClauseEqual :
      baseClause.scale retainedTerminalFanRoutingRefinement =
        clause :=
    congrArg Prod.fst taggedClauseEqual
  subst clauseIndex
  subst clause
  have baseLiteralMember :
      (literal, literalIndex) ∈ baseClause.literals.zipIdx := by
    simpa using literalMember
  by_cases occurrenceIndex :
      baseIndex <
        (PeriodicEightOccurrenceSplitPositioned.occurrenceClauses
          source occurrencePorts).length
  · have copiedClauseMember :=
      occurrenceClauseMember_of_formula_member
        source placement order taggedClauseMember
        (by simpa [occurrencePorts] using occurrenceIndex)
    rcases
        occurrenceMetadata_of_members
          source occurrencePorts copiedClauseMember
          baseLiteralMember with
      ⟨metadata, sourceLiteral,
        _metadataClauseEqual, metadataIndex,
        sourceClauseMember, sourceLiteralMember,
        _copiedLiteralEqual⟩
    have sourceClauseMemberAt :
        (metadata.sourceClause, baseIndex) ∈
          source.clauses.zipIdx := by
      simpa [metadataIndex] using sourceClauseMember
    rw [
      retainedAngularFanSplicedIncidenceRoutes_occurrence
        source placement routes baseIndex literalIndex
        (by simpa [occurrencePorts] using occurrenceIndex),
      retainedAngularFanSplicedOccurrenceRoutes_of_members
        source placement routes
        sourceClauseMemberAt sourceLiteralMember]
    unfold retainedAngularFanSplicedOccurrenceRoute
    apply joinAtEndpoint_length_ge_two_of_head
      (retainedAngularFanBoundaryIncidenceRoutes_valid
        source placement routes fits certificate
        endpoints lengths retainedRoutes
        sourceClauseMemberAt sourceLiteralMember).1
    simpa [scalePolyline] using
      angularOccurrenceSuffix_length_ge_two
        placement order metadata.sourceClause sourceLiteral
        baseIndex literalIndex
  · have cycleClauseMember :=
      cycleClauseMember_of_formula_member
        source placement occurrencePorts
        taggedClauseMember
        (by simpa [occurrencePorts] using occurrenceIndex)
    have clauseIndexDecomposition :
        baseIndex =
          (PeriodicEightOccurrenceSplitPositioned.occurrenceClauses
            source occurrencePorts).length +
            (baseIndex -
              (PeriodicEightOccurrenceSplitPositioned.occurrenceClauses
                source occurrencePorts).length) := by
      omega
    rw [clauseIndexDecomposition,
      retainedAngularFanSplicedIncidenceRoutes_cycle]
    simpa [scalePolyline] using
      allCycleRoutes_length_ge_two
        source placement cycleClauseMember baseLiteralMember

/-- Source-first scaling preserves complete retained-route
nondegeneracy. -/
theorem
    retainedAngularFanSourceScaledSplicedIncidenceRoutes_length_ge_two
    {Variable : Type*} [DecidableEq Variable]
    {factor : Nat}
    (factorPositive : 0 < factor)
    (source : PositionedPeriodicCNF Variable)
    (placement : PeriodicVariablePlacement Variable)
    (family :
      PositionedPeriodicCNF.CanonicalRetainedRayIncidenceRoutes
        source placement)
    (fits :
      FitsEightSlots
        (angularOccurrenceOrder source.erase family.routes))
    (certificate :
      RetainedOccurrenceTerminalCertificate
        source.erase family.routes)
    (lengths :
      ∀ clause clauseIndex,
        (clause, clauseIndex) ∈ source.clauses.zipIdx →
        ∀ literal literalIndex,
          (literal, literalIndex) ∈ clause.literals.zipIdx →
          2 ≤ (family.routes clauseIndex literalIndex).length)
    {clause :
      PositionedPeriodicClause
        (ThreeOccurrenceVariable Variable)}
    {clauseIndex : Nat}
    (clauseMember :
      (clause, clauseIndex) ∈
        (retainedAngularFanSourceScaledRefinedFormula
          factor source placement family.routes).clauses.zipIdx)
    {literal :
      PeriodicLiteral
        (ThreeOccurrenceVariable Variable)}
    {literalIndex : Nat}
    (literalMember :
      (literal, literalIndex) ∈ clause.literals.zipIdx) :
    2 ≤
      (retainedAngularFanSourceScaledSplicedIncidenceRoutes
        factor source placement family.routes
        clauseIndex literalIndex).length := by
  let scaledFamily :=
    family.scale factorPositive
  have scaledFits :
      FitsEightSlots
        (angularOccurrenceOrder
          (source.scale factor).erase
          scaledFamily.routes) := by
    change
      FitsEightSlots
        (angularOccurrenceOrder
          (source.scale factor).erase
          (PositionedPeriodicCNF.scaleIncidenceRoutes
            factor family.routes))
    rw [PositionedPeriodicCNF.erase_scale,
      angularOccurrenceOrder_scaleIncidenceRoutes
        source.erase factorPositive family.routes]
    exact fits
  have scaledCertificate :
      RetainedOccurrenceTerminalCertificate
        (source.scale factor).erase
        scaledFamily.routes := by
    change
      RetainedOccurrenceTerminalCertificate
        (source.scale factor).erase
        (PositionedPeriodicCNF.scaleIncidenceRoutes
          factor family.routes)
    simpa only [PositionedPeriodicCNF.erase_scale] using
      certificate.scaleIncidenceRoutes factorPositive
  have scaledLengths :
      ∀ scaledClause scaledClauseIndex,
        (scaledClause, scaledClauseIndex) ∈
          (source.scale factor).clauses.zipIdx →
        ∀ scaledLiteral scaledLiteralIndex,
          (scaledLiteral, scaledLiteralIndex) ∈
            scaledClause.literals.zipIdx →
          2 ≤
            (scaledFamily.routes
              scaledClauseIndex scaledLiteralIndex).length := by
    intro scaledClause scaledClauseIndex scaledClauseMember
      scaledLiteral scaledLiteralIndex scaledLiteralMember
    rw [PositionedPeriodicCNF.scale_clauses,
      List.zipIdx_map] at scaledClauseMember
    rcases List.mem_map.mp scaledClauseMember with
      ⟨taggedClause, taggedClauseMember, taggedClauseEqual⟩
    have clauseIndexEqual :
        taggedClause.2 = scaledClauseIndex :=
      congrArg Prod.snd taggedClauseEqual
    have scaledClauseEqual :
        taggedClause.1.scale factor = scaledClause :=
      congrArg Prod.fst taggedClauseEqual
    subst scaledClauseIndex
    subst scaledClause
    have sourceLiteralMember :
        (scaledLiteral, scaledLiteralIndex) ∈
          taggedClause.1.literals.zipIdx := by
      simpa using scaledLiteralMember
    change
      2 ≤
        (scalePolyline factor
          (family.routes
            taggedClause.2 scaledLiteralIndex)).length
    simpa [
      scalePolyline] using
      lengths taggedClause.1 taggedClause.2 taggedClauseMember
        scaledLiteral scaledLiteralIndex sourceLiteralMember
  change
    2 ≤
      (retainedAngularFanSplicedIncidenceRoutes
        (source.scale factor)
        (placement.scale factor)
        scaledFamily.routes
        clauseIndex literalIndex).length
  exact
    retainedAngularFanSplicedIncidenceRoutes_length_ge_two
      (source.scale factor)
      (placement.scale factor)
      scaledFamily.routes
      scaledFits scaledCertificate
      scaledFamily.endpoints scaledLengths scaledFamily.retained
      clauseMember literalMember

/-- Route-field form of source-first retained-route nondegeneracy.  This
avoids exposing a large family record at concrete specializations. -/
theorem
    retainedAngularFanSourceScaledSplicedIncidenceRoutes_length_ge_two_of_routes
    {Variable : Type*} [DecidableEq Variable]
    {factor : Nat}
    (factorPositive : 0 < factor)
    (source : PositionedPeriodicCNF Variable)
    (placement : PeriodicVariablePlacement Variable)
    (routes : PositionedPeriodicCNF.IncidenceRoutes)
    (fits :
      FitsEightSlots
        (angularOccurrenceOrder source.erase routes))
    (certificate :
      RetainedOccurrenceTerminalCertificate
        source.erase routes)
    (endpoints :
      ∀ clause clauseIndex,
        (clause, clauseIndex) ∈ source.clauses.zipIdx →
        ∀ literal literalIndex,
          (literal, literalIndex) ∈ clause.literals.zipIdx →
          (routes clauseIndex literalIndex).head? =
              some
                (PositionedPeriodicCNF.canonicalClausePosition
                  placement clause) ∧
            (routes clauseIndex literalIndex).getLast? =
              some
                (PositionedPeriodicCNF.canonicalLiteralPosition
                  placement clause literal))
    (lengths :
      ∀ clause clauseIndex,
        (clause, clauseIndex) ∈ source.clauses.zipIdx →
        ∀ literal literalIndex,
          (literal, literalIndex) ∈ clause.literals.zipIdx →
          2 ≤ (routes clauseIndex literalIndex).length)
    (retainedRoutes :
      ∀ clause clauseIndex,
        (clause, clauseIndex) ∈ source.clauses.zipIdx →
        ∀ literal literalIndex,
          (literal, literalIndex) ∈ clause.literals.zipIdx →
          RetainedRayPolyline
            (routes clauseIndex literalIndex))
    {clause :
      PositionedPeriodicClause
        (ThreeOccurrenceVariable Variable)}
    {clauseIndex : Nat}
    (clauseMember :
      (clause, clauseIndex) ∈
        (retainedAngularFanSourceScaledRefinedFormula
          factor source placement routes).clauses.zipIdx)
    {literal :
      PeriodicLiteral
        (ThreeOccurrenceVariable Variable)}
    {literalIndex : Nat}
    (literalMember :
      (literal, literalIndex) ∈ clause.literals.zipIdx) :
    2 ≤
      (retainedAngularFanSourceScaledSplicedIncidenceRoutes
        factor source placement routes
        clauseIndex literalIndex).length := by
  let family :
      PositionedPeriodicCNF.CanonicalRetainedRayIncidenceRoutes
        source placement :=
    { routes := routes
      endpoints := endpoints
      retained := retainedRoutes }
  simpa only [family] using
    retainedAngularFanSourceScaledSplicedIncidenceRoutes_length_ge_two
      factorPositive source placement family fits certificate lengths
      clauseMember literalMember

end PeriodicEightOccurrenceSplit

namespace PeriodicOrthocrossing

open PeriodicEightOccurrenceSplit
open PeriodicThreeSATThree

set_option maxHeartbeats 2000000

/-- The retained source routes fit the eight Figure 7 ports. -/
private theorem retainedSourceRoutesForRouteLength_fits
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (sourceLocal : source.IsLocal)
    (sourceWidth : source.WidthAtMost 3)
    (sourceOccurrences : source.OccurrencesAtMost 3)
    (sourceClausesNonempty :
      ∀ clause ∈ source.clauses, clause ≠ []) :
    FitsEightSlots
      (angularOccurrenceOrder
        (retainedDeduplicatedGaugedWrappedDrawingPositionedPeriodicPlanarSATFormula
          source).erase
        (retainedDeduplicatedGaugedWrappedDrawingPeriodicPlanarSATIncidenceRoutes
          source)) := by
  simpa [retainedDrawingAngularOccurrenceOrder,
    retainedPlanarSATFormula] using
    retainedDrawingAngularOccurrenceOrder_fitsEightSlots
      sourceLocal sourceWidth sourceOccurrences
      sourceClausesNonempty

/-- The retained source routes have the classified terminal data needed by
angular fans. -/
private theorem retainedSourceRoutesForRouteLength_certificate
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (sourceLocal : source.IsLocal)
    (sourceWidth : source.WidthAtMost 3)
    (sourceOccurrences : source.OccurrencesAtMost 3)
    (sourceClausesNonempty :
      ∀ clause ∈ source.clauses, clause ≠ []) :
    RetainedOccurrenceTerminalCertificate
      (retainedDeduplicatedGaugedWrappedDrawingPositionedPeriodicPlanarSATFormula
        source).erase
      (retainedDeduplicatedGaugedWrappedDrawingPeriodicPlanarSATIncidenceRoutes
        source) := by
  let sourceCertificate :=
    retainedPlanarSATCertificate source
      sourceLocal sourceWidth sourceOccurrences
      sourceClausesNonempty
  let retainedClausesNonempty :=
    retainedDrawingPlanarSATFormula_clausesNonempty_of_source
      source sourceClausesNonempty
  exact
    retainedDeduplicatedGaugedWrappedDrawingPeriodicPlanarSATOccurrence_terminalCertificate
      source
      sourceCertificate.graphWellFormed
      sourceCertificate.graphDegreeAtMostThree
      sourceCertificate.graphIsLocal
      retainedClausesNonempty

/-- The retained source routes have canonical endpoints. -/
private theorem retainedSourceRoutesForRouteLength_endpoints
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (sourceLocal : source.IsLocal)
    (sourceWidth : source.WidthAtMost 3)
    (sourceOccurrences : source.OccurrencesAtMost 3)
    (sourceClausesNonempty :
      ∀ clause ∈ source.clauses, clause ≠ []) :
    ∀ sourceClause sourceClauseIndex,
      (sourceClause, sourceClauseIndex) ∈
        (retainedDeduplicatedGaugedWrappedDrawingPositionedPeriodicPlanarSATFormula
          source).clauses.zipIdx →
      ∀ sourceLiteral sourceLiteralIndex,
        (sourceLiteral, sourceLiteralIndex) ∈
          sourceClause.literals.zipIdx →
        (retainedDeduplicatedGaugedWrappedDrawingPeriodicPlanarSATIncidenceRoutes
            source sourceClauseIndex sourceLiteralIndex).head? =
            some
              (PositionedPeriodicCNF.canonicalClausePosition
                (retainedGaugedWrappedDrawingPeriodicPlanarSATPlacement source)
                sourceClause) ∧
          (retainedDeduplicatedGaugedWrappedDrawingPeriodicPlanarSATIncidenceRoutes
              source sourceClauseIndex sourceLiteralIndex).getLast? =
            some
              (PositionedPeriodicCNF.canonicalLiteralPosition
                (retainedGaugedWrappedDrawingPeriodicPlanarSATPlacement source)
                sourceClause sourceLiteral) := by
  let certificate :=
    retainedPlanarSATCertificate source
      sourceLocal sourceWidth sourceOccurrences
      sourceClausesNonempty
  intro sourceClause sourceClauseIndex sourceClauseMember
    sourceLiteral sourceLiteralIndex sourceLiteralMember
  exact
    retainedDeduplicatedGaugedWrappedDrawingPeriodicPlanarSATIncidenceRoutes_endpoints
      source
      certificate.graphWellFormed
      certificate.graphDegreeAtMostThree
      certificate.graphIsLocal
      sourceClauseMember sourceLiteralMember

/-- Every retained source route already contains an edge. -/
private theorem retainedSourceRoutesForRouteLength_lengths
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (sourceLocal : source.IsLocal)
    (sourceWidth : source.WidthAtMost 3)
    (sourceOccurrences : source.OccurrencesAtMost 3)
    (sourceClausesNonempty :
      ∀ clause ∈ source.clauses, clause ≠ []) :
    ∀ sourceClause sourceClauseIndex,
      (sourceClause, sourceClauseIndex) ∈
        (retainedDeduplicatedGaugedWrappedDrawingPositionedPeriodicPlanarSATFormula
          source).clauses.zipIdx →
      ∀ sourceLiteral sourceLiteralIndex,
        (sourceLiteral, sourceLiteralIndex) ∈
          sourceClause.literals.zipIdx →
        2 ≤
          (retainedDeduplicatedGaugedWrappedDrawingPeriodicPlanarSATIncidenceRoutes
            source sourceClauseIndex sourceLiteralIndex).length := by
  let sourceCertificate :=
    retainedPlanarSATCertificate source
      sourceLocal sourceWidth sourceOccurrences
      sourceClausesNonempty
  let retainedClausesNonempty :=
    retainedDrawingPlanarSATFormula_clausesNonempty_of_source
      source sourceClausesNonempty
  intro sourceClause sourceClauseIndex sourceClauseMember
    sourceLiteral sourceLiteralIndex sourceLiteralMember
  exact
    retainedDeduplicatedGaugedWrappedDrawingPeriodicPlanarSATIncidenceRoutes_length_ge_two
      source
      sourceCertificate.graphWellFormed
      sourceCertificate.graphDegreeAtMostThree
      sourceCertificate.graphIsLocal
      retainedClausesNonempty
      sourceClauseMember sourceLiteralMember

/-- Every retained source route satisfies the retained-ray slope
certificate. -/
private theorem retainedSourceRoutesForRouteLength_retained
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (sourceLocal : source.IsLocal)
    (sourceWidth : source.WidthAtMost 3)
    (sourceOccurrences : source.OccurrencesAtMost 3)
    (sourceClausesNonempty :
      ∀ clause ∈ source.clauses, clause ≠ []) :
    ∀ sourceClause sourceClauseIndex,
      (sourceClause, sourceClauseIndex) ∈
        (retainedDeduplicatedGaugedWrappedDrawingPositionedPeriodicPlanarSATFormula
          source).clauses.zipIdx →
      ∀ sourceLiteral sourceLiteralIndex,
        (sourceLiteral, sourceLiteralIndex) ∈
          sourceClause.literals.zipIdx →
        RetainedRayPolyline
          (retainedDeduplicatedGaugedWrappedDrawingPeriodicPlanarSATIncidenceRoutes
            source sourceClauseIndex sourceLiteralIndex) := by
  let certificate :=
    retainedPlanarSATCertificate source
      sourceLocal sourceWidth sourceOccurrences
      sourceClausesNonempty
  intro sourceClause sourceClauseIndex sourceClauseMember
    sourceLiteral sourceLiteralIndex sourceLiteralMember
  exact
    retainedDeduplicatedGaugedWrappedDrawingPeriodicPlanarSATIncidenceRoutes_retainedRay
      source
      certificate.graphWellFormed
      certificate.graphDegreeAtMostThree
      certificate.graphIsLocal
      (retainedDrawingPlanarSATFormula_clausesNonempty_of_source
        source sourceClausesNonempty)
      (sourceClause, sourceClauseIndex) sourceClauseMember
      (sourceLiteral, sourceLiteralIndex) sourceLiteralMember

/-- Every established source-scaled retained fixed-eight route contains a
genuine final edge. -/
theorem
    retainedDrawingSourceScaledRefinedEightOccurrenceSplitIncidenceRoutes_length_ge_two
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (sourceLocal : source.IsLocal)
    (sourceWidth : source.WidthAtMost 3)
    (sourceOccurrences : source.OccurrencesAtMost 3)
    (sourceClausesNonempty :
      ∀ clause ∈ source.clauses, clause ≠ [])
    {clause :
      PositionedPeriodicClause
        (ThreeOccurrenceVariable
          (WrappedPeriodicPlanarSATVariable Variable))}
    {clauseIndex : Nat}
    (clauseMember :
      (clause, clauseIndex) ∈
        (retainedDrawingSourceScaledRefinedEightOccurrenceSplitPositionedFormula
          source).clauses.zipIdx)
    {literal :
      PeriodicLiteral
        (ThreeOccurrenceVariable
          (WrappedPeriodicPlanarSATVariable Variable))}
    {literalIndex : Nat}
    (literalMember :
      (literal, literalIndex) ∈ clause.literals.zipIdx) :
    2 ≤
      (retainedDrawingSourceScaledRefinedEightOccurrenceSplitIncidenceRoutes
        source clauseIndex literalIndex).length := by
  unfold
    retainedDrawingSourceScaledRefinedEightOccurrenceSplitPositionedFormula
    at clauseMember
  unfold
    retainedDrawingSourceScaledRefinedEightOccurrenceSplitIncidenceRoutes
  exact
    retainedAngularFanSourceScaledSplicedIncidenceRoutes_length_ge_two_of_routes
      retainedAngularFanSourceClearanceFactor_pos
      (retainedDeduplicatedGaugedWrappedDrawingPositionedPeriodicPlanarSATFormula
        source)
      (retainedGaugedWrappedDrawingPeriodicPlanarSATPlacement source)
      (retainedDeduplicatedGaugedWrappedDrawingPeriodicPlanarSATIncidenceRoutes
        source)
      (retainedSourceRoutesForRouteLength_fits
        source sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty)
      (retainedSourceRoutesForRouteLength_certificate
        source sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty)
      (retainedSourceRoutesForRouteLength_endpoints
        source sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty)
      (retainedSourceRoutesForRouteLength_lengths
        source sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty)
      (retainedSourceRoutesForRouteLength_retained
        source sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty)
      clauseMember literalMember

/-- On an explicitly displayed final axis-aligned edge, the total final
direction lookup is genuine. -/
private theorem polylineLastDirection_isGenuine_of_length_and_orthogonal
    {route : List Cell}
    (routeLength : 2 ≤ route.length)
    (routeOrthogonal : OrthogonalPolyline route) :
    (AxisDirection.polylineLastDirection route).IsGenuine := by
  rcases
      AxisDirection.exists_eq_append_pair_of_length_ge_two
        routeLength with
    ⟨leading, before, last, routeEquation⟩
  rw [routeEquation] at routeOrthogonal ⊢
  have finalAligned :
      (GridSegment.mk before last).IsAxisAligned :=
    (List.isChain_append_cons_cons.mp routeOrthogonal).2.1
  unfold AxisDirection.polylineLastDirection
  simp only [List.reverse_append, List.reverse_cons,
    List.reverse_nil, List.nil_append]
  change
    (AxisDirection.between last before).opposite.IsGenuine
  rw [AxisDirection.between_reverse_eq_opposite
    (AxisDirection.between_isGenuine_of_axisAligned finalAligned)]
  simpa using
    AxisDirection.between_isGenuine_of_axisAligned finalAligned

/-- A genuine total final-direction lookup witnesses at least one listed
edge. -/
private theorem two_le_length_of_polylineLastDirection_isGenuine
    {route : List Cell}
    (genuine :
      (AxisDirection.polylineLastDirection route).IsGenuine) :
    2 ≤ route.length := by
  cases route with
  | nil =>
      simp [AxisDirection.polylineLastDirection,
        AxisDirection.polylineFirstDirection,
        AxisDirection.IsGenuine,
        AxisDirection.opposite] at genuine
  | cons first rest =>
      cases rest with
      | nil =>
          simp [AxisDirection.polylineLastDirection,
            AxisDirection.polylineFirstDirection,
            AxisDirection.IsGenuine,
            AxisDirection.opposite] at genuine
      | cons second tail =>
          simp

/-- Every genuine final coordinated fixed-eight route contains a final
edge. -/
theorem
    retainedDrawingSourceScaledCoordinatedEightOccurrenceSplitIncidenceRoutes_length_ge_two
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (sourceLocal : source.IsLocal)
    (sourceWidth : source.WidthAtMost 3)
    (sourceOccurrences : source.OccurrencesAtMost 3)
    (sourceClausesNonempty :
      ∀ clause ∈ source.clauses, clause ≠ [])
    {clause :
      PositionedPeriodicClause
        (ThreeOccurrenceVariable
          (WrappedPeriodicPlanarSATVariable Variable))}
    {clauseIndex : Nat}
    (clauseMember :
      (clause, clauseIndex) ∈
        (retainedDrawingSourceScaledRefinedEightOccurrenceSplitPositionedFormula
          source).clauses.zipIdx)
    {literal :
      PeriodicLiteral
        (ThreeOccurrenceVariable
          (WrappedPeriodicPlanarSATVariable Variable))}
    {literalIndex : Nat}
    (literalMember :
      (literal, literalIndex) ∈ clause.literals.zipIdx) :
    2 ≤
      (retainedDrawingSourceScaledCoordinatedEightOccurrenceSplitIncidenceRoutes
        source clauseIndex literalIndex).length := by
  apply two_le_length_of_polylineLastDirection_isGenuine
  rw [
    retainedDrawingSourceScaledCoordinatedEightOccurrenceSplitIncidenceRoutes_lastDirection_eq_fallback
      source sourceLocal sourceWidth sourceOccurrences
      sourceClausesNonempty clauseMember literalMember]
  exact
    polylineLastDirection_isGenuine_of_length_and_orthogonal
      (retainedDrawingSourceScaledRefinedEightOccurrenceSplitIncidenceRoutes_length_ge_two
        source sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty clauseMember literalMember)
      (retainedDrawingSourceScaledRefinedEightOccurrenceSplitIncidenceRoutes_valid
        source sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty clauseMember literalMember).2.2

end PeriodicOrthocrossing
end LeanTrominoes
