import LeanTrominoes.RetainedAngularFanFinalCoordinatedTerminalDirections
import LeanTrominoes.RetainedAngularFanSourceScaledDrawing
import LeanTrominoes.PeriodicEightOccurrenceSplitVariableRouteOrder

/-!
# Variable route order after source-first retained-fan scaling

The retained boundary prefixes differ from the canonical Figure 7
prefixes, but every copied-source route keeps the same final Figure 7 spoke;
the appended implication-cycle routes are merely scaled.  Consequently the
complete source-scaled retained route family inherits the canonical
clockwise occurrence order.
-/

namespace LeanTrominoes
namespace PeriodicEightOccurrenceSplit

open PeriodicEightOccurrenceSplitPositioned
open PeriodicThreeSATThree

set_option maxHeartbeats 2000000

/-- Replacing canonical copied-source boundary prefixes by retained angular
fan prefixes preserves the clockwise variable-route order after the common
routing refinement. -/
theorem
    retainedAngularFanSplicedIncidenceRoutes_variableRoutesInOccurrenceOrder
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
            (routes clauseIndex literalIndex)) :
    (retainedAngularFanRefinedFormula
        source placement routes).VariableRoutesInOccurrenceOrder
      (retainedAngularFanSplicedIncidenceRoutes
        source placement routes) := by
  let order :=
    angularOccurrenceOrder source.erase routes
  let boundary :=
    canonicalAngularBoundaryRoutes source placement order
  let referenceRoutes :=
    PositionedPeriodicCNF.scaleIncidenceRoutes
      retainedTerminalFanRoutingRefinement
      (angularSplicedIncidenceRoutes
        source placement order boundary)
  have referenceOrder :
      (retainedAngularFanRefinedFormula
          source placement routes).VariableRoutesInOccurrenceOrder
        referenceRoutes := by
    have unscaled :=
      angularSplicedIncidenceRoutes_variableRoutesInOccurrenceOrder
        source placement order fits boundary
    have scaled :=
      PositionedPeriodicCNF.VariableRoutesInOccurrenceOrder.scale
        unscaled retainedTerminalFanRoutingRefinement
        (by simp [retainedTerminalFanRoutingRefinement])
    simpa [retainedAngularFanRefinedFormula,
      order, boundary, referenceRoutes] using scaled
  apply
    PositionedPeriodicCNF.VariableRoutesInOccurrenceOrder.of_memberwise_lastDirection_eq
      referenceOrder
  intro scaledClause clauseIndex scaledClauseMember
    literal literalIndex literalMember
  rw [retainedAngularFanRefinedFormula,
    PositionedPeriodicCNF.scale_clauses,
    List.zipIdx_map] at scaledClauseMember
  rcases List.mem_map.mp scaledClauseMember with
    ⟨taggedClause, taggedClauseMember, taggedClauseEqual⟩
  rcases taggedClause with ⟨baseClause, baseIndex⟩
  have clauseIndexEqual :
      baseIndex = clauseIndex :=
    congrArg Prod.snd taggedClauseEqual
  have scaledClauseEqual :
      baseClause.scale retainedTerminalFanRoutingRefinement =
        scaledClause :=
    congrArg Prod.fst taggedClauseEqual
  subst clauseIndex
  subst scaledClause
  have baseLiteralMember :
      (literal, literalIndex) ∈ baseClause.literals.zipIdx := by
    simpa using literalMember
  by_cases occurrenceIndex :
      baseIndex <
        (PeriodicEightOccurrenceSplitPositioned.occurrenceClauses source
          (occurrencePortsOfAngularOrder
            source.erase order)).length
  · have copiedClauseMember :=
      occurrenceClauseMember_of_formula_member
        source placement order taggedClauseMember occurrenceIndex
    rcases
        occurrenceClauseMetadata_lookup
          source
          (occurrencePortsOfAngularOrder source.erase order)
          copiedClauseMember with
      ⟨metadata, _metadataLookup, metadataClauseEqual,
        sourceClauseMember, metadataIndex,
        metadataClauseDefinition⟩
    have sourceClauseMemberAt :
        (metadata.sourceClause, baseIndex) ∈
          source.clauses.zipIdx := by
      simpa [metadataIndex] using sourceClauseMember
    have copiedClauseEqual :
        baseClause =
          PeriodicEightOccurrenceSplitPositioned.occurrenceClause
            (occurrencePortsOfAngularOrder source.erase order)
            baseIndex metadata.sourceClause := by
      calc
        baseClause = metadata.clause :=
          metadataClauseEqual.symm
        _ =
            PeriodicEightOccurrenceSplitPositioned.occurrenceClause
              (occurrencePortsOfAngularOrder source.erase order)
              metadata.clauseIndex metadata.sourceClause :=
          metadataClauseDefinition
        _ =
            PeriodicEightOccurrenceSplitPositioned.occurrenceClause
              (occurrencePortsOfAngularOrder source.erase order)
              baseIndex metadata.sourceClause := by
          rw [metadataIndex]
    rcases
        occurrenceLiteral_of_members
          (occurrencePortsOfAngularOrder source.erase order)
          copiedClauseEqual baseLiteralMember with
      ⟨sourceLiteral, sourceLiteralMember,
        copiedLiteralEqual⟩
    change
      AxisDirection.polylineLastDirection
          (retainedAngularFanSplicedIncidenceRoutes
            source placement routes baseIndex literalIndex) =
        AxisDirection.polylineLastDirection
          (scalePolyline retainedTerminalFanRoutingRefinement
            (angularSplicedIncidenceRoutes
              source placement order boundary
              baseIndex literalIndex))
    rw [
      retainedAngularFanSplicedIncidenceRoutes_occurrence
        source placement routes baseIndex literalIndex occurrenceIndex,
      retainedAngularFanSplicedOccurrenceRoutes_of_members
        source placement routes
        sourceClauseMemberAt sourceLiteralMember,
      angularSplicedIncidenceRoutes_occurrence
        source placement order boundary
        baseIndex literalIndex occurrenceIndex,
      angularSplicedOccurrenceRoutes_of_members
        boundary sourceClauseMemberAt sourceLiteralMember,
      AxisDirection.polylineLastDirection_scalePolyline
        retainedTerminalFanRoutingRefinement
        (by simp [retainedTerminalFanRoutingRefinement])]
    calc
      AxisDirection.polylineLastDirection
          (retainedAngularFanSplicedOccurrenceRoute
            source placement routes metadata.sourceClause
            sourceLiteral baseIndex literalIndex) =
        AxisDirection.polylineLastDirection
          (angularOccurrenceSuffix placement order
            metadata.sourceClause sourceLiteral
            baseIndex literalIndex) := by
              simpa [order] using
                retainedAngularFanSplicedOccurrenceRoute_lastDirection
                  source placement routes fits certificate
                  endpoints lengths retainedRoutes
                  sourceClauseMemberAt sourceLiteralMember
      _ =
        AxisDirection.polylineLastDirection
          (angularSplicedOccurrenceRoute boundary
            metadata.sourceClause sourceLiteral
            baseIndex literalIndex) := by
              rw [
                angularOccurrenceSuffix_lastDirection
                  placement order metadata.sourceClause
                  sourceLiteral baseIndex literalIndex]
              exact
                (angularSplicedOccurrenceRoute_lastDirection
                  boundary sourceClauseMemberAt
                  sourceLiteralMember).symm
  · let cycleIndex :=
      baseIndex -
        (PeriodicEightOccurrenceSplitPositioned.occurrenceClauses source
          (occurrencePortsOfAngularOrder
            source.erase order)).length
    have clauseIndexDecomposition :
        baseIndex =
          (PeriodicEightOccurrenceSplitPositioned.occurrenceClauses source
            (occurrencePortsOfAngularOrder
              source.erase order)).length +
            cycleIndex := by
      dsimp only [cycleIndex]
      omega
    change
      AxisDirection.polylineLastDirection
          (retainedAngularFanSplicedIncidenceRoutes
            source placement routes baseIndex literalIndex) =
        AxisDirection.polylineLastDirection
          (scalePolyline retainedTerminalFanRoutingRefinement
            (angularSplicedIncidenceRoutes
              source placement order boundary
              baseIndex literalIndex))
    rw [clauseIndexDecomposition,
      retainedAngularFanSplicedIncidenceRoutes_cycle,
      angularSplicedIncidenceRoutes_cycle]

/-- Source-first scaling preserves the hypotheses needed by the retained
route-order theorem. -/
theorem
    retainedAngularFanSourceScaledSplicedIncidenceRoutes_variableRoutesInOccurrenceOrder
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
          2 ≤ (family.routes clauseIndex literalIndex).length) :
    (retainedAngularFanSourceScaledRefinedFormula
        factor source placement family.routes).VariableRoutesInOccurrenceOrder
      (retainedAngularFanSourceScaledSplicedIncidenceRoutes
        factor source placement family.routes) := by
  let scaledFamily :=
    family.scale factorPositive
  have scaledFits :
      FitsEightSlots
        (angularOccurrenceOrder
          (source.scale factor).erase
          (PositionedPeriodicCNF.scaleIncidenceRoutes
            factor family.routes)) := by
    rw [PositionedPeriodicCNF.erase_scale,
      angularOccurrenceOrder_scaleIncidenceRoutes
        source.erase factorPositive family.routes]
    exact fits
  have scaledCertificate :
      RetainedOccurrenceTerminalCertificate
        (source.scale factor).erase
        (PositionedPeriodicCNF.scaleIncidenceRoutes
          factor family.routes) := by
    simpa only [PositionedPeriodicCNF.erase_scale] using
      certificate.scaleIncidenceRoutes factorPositive
  have scaledLengths :
      ∀ clause clauseIndex,
        (clause, clauseIndex) ∈
          (source.scale factor).clauses.zipIdx →
        ∀ literal literalIndex,
          (literal, literalIndex) ∈ clause.literals.zipIdx →
          2 ≤
            (PositionedPeriodicCNF.scaleIncidenceRoutes
              factor family.routes clauseIndex literalIndex).length := by
    intro scaledClause clauseIndex scaledClauseMember
      literal literalIndex literalMember
    rw [PositionedPeriodicCNF.scale_clauses,
      List.zipIdx_map] at scaledClauseMember
    rcases List.mem_map.mp scaledClauseMember with
      ⟨taggedClause, taggedClauseMember, taggedClauseEqual⟩
    have clauseIndexEqual :
        taggedClause.2 = clauseIndex :=
      congrArg Prod.snd taggedClauseEqual
    have scaledClauseEqual :
        taggedClause.1.scale factor = scaledClause :=
      congrArg Prod.fst taggedClauseEqual
    subst clauseIndex
    subst scaledClause
    have sourceLiteralMember :
        (literal, literalIndex) ∈
          taggedClause.1.literals.zipIdx := by
      simpa using literalMember
    simpa [PositionedPeriodicCNF.scaleIncidenceRoutes,
      scalePolyline] using
      lengths taggedClause.1 taggedClause.2 taggedClauseMember
        literal literalIndex sourceLiteralMember
  simpa [retainedAngularFanSourceScaledRefinedFormula,
    retainedAngularFanSourceScaledSplicedIncidenceRoutes,
    scaledFamily] using
    retainedAngularFanSplicedIncidenceRoutes_variableRoutesInOccurrenceOrder
      (source.scale factor)
      (placement.scale factor)
      (PositionedPeriodicCNF.scaleIncidenceRoutes
        factor family.routes)
      scaledFits scaledCertificate
      scaledFamily.endpoints scaledLengths scaledFamily.retained

end PeriodicEightOccurrenceSplit

namespace PeriodicOrthocrossing

open PeriodicEightOccurrenceSplit
open PeriodicThreeSATThree

set_option maxHeartbeats 2000000

/-- The established source-scaled retained fixed-eight routes follow
syntactic occurrence order clockwise at every degree-three split variable. -/
theorem
    retainedDrawingSourceScaledRefinedEightOccurrenceSplitIncidenceRoutes_variableRoutesInOccurrenceOrder
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (sourceLocal : source.IsLocal)
    (sourceWidth : source.WidthAtMost 3)
    (sourceOccurrences : source.OccurrencesAtMost 3)
    (sourceClausesNonempty :
      ∀ clause ∈ source.clauses, clause ≠ []) :
    PositionedPeriodicCNF.VariableRoutesInOccurrenceOrder
      (retainedDrawingSourceScaledRefinedEightOccurrenceSplitPositionedFormula
        source)
      (retainedDrawingSourceScaledRefinedEightOccurrenceSplitIncidenceRoutes
        source) := by
  let sourceCertificate :=
    retainedPlanarSATCertificate source
      sourceLocal sourceWidth sourceOccurrences
      sourceClausesNonempty
  let retainedClausesNonempty :=
    retainedDrawingPlanarSATFormula_clausesNonempty_of_source
      source sourceClausesNonempty
  let family :
      PositionedPeriodicCNF.CanonicalRetainedRayIncidenceRoutes
        (retainedDeduplicatedGaugedWrappedDrawingPositionedPeriodicPlanarSATFormula
          source)
        (retainedGaugedWrappedDrawingPeriodicPlanarSATPlacement source) :=
    { routes :=
        retainedDeduplicatedGaugedWrappedDrawingPeriodicPlanarSATIncidenceRoutes
          source
      endpoints := by
        intro clause clauseIndex clauseMember
          literal literalIndex literalMember
        exact
          retainedDeduplicatedGaugedWrappedDrawingPeriodicPlanarSATIncidenceRoutes_endpoints
            source
            sourceCertificate.graphWellFormed
            sourceCertificate.graphDegreeAtMostThree
            sourceCertificate.graphIsLocal
            clauseMember literalMember
      retained := by
        intro clause clauseIndex clauseMember
          literal literalIndex literalMember
        exact
          retainedDeduplicatedGaugedWrappedDrawingPeriodicPlanarSATIncidenceRoutes_retainedRay
            source
            sourceCertificate.graphWellFormed
            sourceCertificate.graphDegreeAtMostThree
            sourceCertificate.graphIsLocal
            retainedClausesNonempty
            (clause, clauseIndex) clauseMember
            (literal, literalIndex) literalMember }
  have familyFits :
      FitsEightSlots
        (angularOccurrenceOrder
          (retainedDeduplicatedGaugedWrappedDrawingPositionedPeriodicPlanarSATFormula
            source).erase family.routes) := by
    simpa [retainedDrawingAngularOccurrenceOrder,
      retainedPlanarSATFormula, family] using
      retainedDrawingAngularOccurrenceOrder_fitsEightSlots
        sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty
  have familyCertificate :
      RetainedOccurrenceTerminalCertificate
        (retainedDeduplicatedGaugedWrappedDrawingPositionedPeriodicPlanarSATFormula
          source).erase family.routes := by
    simpa only [family] using
      retainedDeduplicatedGaugedWrappedDrawingPeriodicPlanarSATOccurrence_terminalCertificate
        source
        sourceCertificate.graphWellFormed
        sourceCertificate.graphDegreeAtMostThree
        sourceCertificate.graphIsLocal
        retainedClausesNonempty
  have familyLengths :
      ∀ clause clauseIndex,
        (clause, clauseIndex) ∈
          (retainedDeduplicatedGaugedWrappedDrawingPositionedPeriodicPlanarSATFormula
            source).clauses.zipIdx →
        ∀ literal literalIndex,
          (literal, literalIndex) ∈ clause.literals.zipIdx →
          2 ≤ (family.routes clauseIndex literalIndex).length := by
    intro clause clauseIndex clauseMember
      literal literalIndex literalMember
    simpa only [family] using
      retainedDeduplicatedGaugedWrappedDrawingPeriodicPlanarSATIncidenceRoutes_length_ge_two
        source
        sourceCertificate.graphWellFormed
        sourceCertificate.graphDegreeAtMostThree
        sourceCertificate.graphIsLocal
        retainedClausesNonempty
        clauseMember literalMember
  have ordered :=
    retainedAngularFanSourceScaledSplicedIncidenceRoutes_variableRoutesInOccurrenceOrder
      retainedAngularFanSourceClearanceFactor_pos
      (retainedDeduplicatedGaugedWrappedDrawingPositionedPeriodicPlanarSATFormula
        source)
      (retainedGaugedWrappedDrawingPeriodicPlanarSATPlacement source)
      family familyFits familyCertificate familyLengths
  simpa only [
    retainedDrawingSourceScaledRefinedEightOccurrenceSplitPositionedFormula,
    retainedDrawingSourceScaledRefinedEightOccurrenceSplitIncidenceRoutes,
    family] using ordered

end PeriodicOrthocrossing
end LeanTrominoes
