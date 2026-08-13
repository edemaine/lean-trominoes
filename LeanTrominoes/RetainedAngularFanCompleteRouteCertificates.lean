/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.RetainedAngularFanCompleteRoutes
import LeanTrominoes.PeriodicEightOccurrenceSplitAngularSplicedRoutes
import LeanTrominoes.PositionedPeriodicCNFRetainedRayRasterization

/-!
# Endpoint and orthogonality certificates for refined retained fan routes

This file verifies the total route family assembled for the factor-eight
fixed-eight split.  Copied source clauses inherit the retained fan-splice
certificate; appended cycle clauses inherit the existing Figure 7
certificate through positive scaling.
-/

namespace LeanTrominoes
namespace PeriodicEightOccurrenceSplit

open PeriodicEightOccurrenceSplitPositioned
open PeriodicThreeSATThree

set_option maxHeartbeats 800000

/-- The canonical position of a copied source clause is the factor-36
refinement of its original canonical position. -/
theorem canonicalClausePosition_occurrenceClause
    {Variable : Type*}
    (placement : PeriodicVariablePlacement Variable)
    (occurrencePorts : OccurrencePorts)
    (clauseIndex : Nat)
    (clause : PositionedPeriodicClause Variable) :
    PositionedPeriodicCNF.canonicalClausePosition
        (PeriodicEightOccurrenceSplitPositioned.placement placement)
        (PeriodicEightOccurrenceSplitPositioned.occurrenceClause
          occurrencePorts clauseIndex clause) =
      Cell.scale
        PeriodicEightOccurrenceSplitPositioned.refinementScale
        (PositionedPeriodicCNF.canonicalClausePosition
          placement clause) := by
  rcases clause.position with ⟨clauseX, clauseY⟩
  rcases placement.translation
    (PeriodicCNF.clauseAnchor clause.literals) with
    ⟨translationX, translationY⟩
  simp only [PositionedPeriodicCNF.canonicalClausePosition,
    PeriodicEightOccurrenceSplitPositioned.occurrenceClause,
    PeriodicEightOccurrenceSplitPositioned.occurrenceClause_clauseAnchor]
  simp [PeriodicEightOccurrenceSplitPositioned.placement,
    PeriodicVariablePlacement.translation,
    PeriodicEightOccurrenceSplitPositioned.refinementScale,
    Cell.sub, Cell.scale]
  constructor <;> ring

/-- Every genuine route has the scaled canonical endpoints of its unscaled
fixed-eight clause and literal. -/
theorem retainedAngularFanSplicedIncidenceRoutes_endpoints
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
        (PeriodicEightOccurrenceSplitPositioned.formula
          source placement
          (occurrencePortsOfAngularOrder
            source.erase
            (angularOccurrenceOrder
              source.erase routes))).clauses.zipIdx)
    {literal :
      PeriodicLiteral
        (ThreeOccurrenceVariable Variable)}
    {literalIndex : Nat}
    (literalMember :
      (literal, literalIndex) ∈ clause.literals.zipIdx) :
    (retainedAngularFanSplicedIncidenceRoutes
      source placement routes clauseIndex literalIndex).head? =
        some
          (Cell.scale retainedTerminalFanRoutingRefinement
            (PositionedPeriodicCNF.canonicalClausePosition
              (PeriodicEightOccurrenceSplitPositioned.placement
                placement)
              clause)) ∧
      (retainedAngularFanSplicedIncidenceRoutes
        source placement routes clauseIndex literalIndex).getLast? =
          some
            (Cell.scale retainedTerminalFanRoutingRefinement
              (PositionedPeriodicCNF.canonicalLiteralPosition
                (PeriodicEightOccurrenceSplitPositioned.placement
                  placement)
                clause literal)) := by
  let order :=
    angularOccurrenceOrder source.erase routes
  let occurrencePorts :=
    occurrencePortsOfAngularOrder source.erase order
  by_cases occurrenceIndex :
      clauseIndex <
        (PeriodicEightOccurrenceSplitPositioned.occurrenceClauses
          source occurrencePorts).length
  · have copiedClauseMember :=
      occurrenceClauseMember_of_formula_member
        source placement order clauseMember occurrenceIndex
    rcases occurrenceClauseMetadata_lookup
        source occurrencePorts copiedClauseMember with
      ⟨metadata, _metadataLookup, metadataClauseEqual,
        sourceClauseMember, metadataIndex,
        metadataClauseDefinition⟩
    have sourceClauseMemberAt :
        (metadata.sourceClause, clauseIndex) ∈
          source.clauses.zipIdx := by
      simpa [metadataIndex] using sourceClauseMember
    have copiedClauseEqual :
        clause =
          PeriodicEightOccurrenceSplitPositioned.occurrenceClause
            occurrencePorts clauseIndex
            metadata.sourceClause := by
      calc
        clause = metadata.clause :=
          metadataClauseEqual.symm
        _ =
            PeriodicEightOccurrenceSplitPositioned.occurrenceClause
              occurrencePorts metadata.clauseIndex
              metadata.sourceClause :=
          metadataClauseDefinition
        _ =
            PeriodicEightOccurrenceSplitPositioned.occurrenceClause
              occurrencePorts clauseIndex
              metadata.sourceClause := by
          rw [metadataIndex]
    rcases occurrenceLiteral_of_members
        occurrencePorts copiedClauseEqual literalMember with
      ⟨sourceLiteral, sourceLiteralMember,
        copiedLiteralEqual⟩
    have explicitValid :=
      retainedAngularFanSplicedOccurrenceRoute_valid
        source placement routes fits certificate
        endpoints lengths retainedRoutes
        sourceClauseMemberAt sourceLiteralMember
    have copiedClausePosition :
        Cell.scale retainedTerminalFanTotalRefinement
            (PositionedPeriodicCNF.canonicalClausePosition
              placement metadata.sourceClause) =
          Cell.scale retainedTerminalFanRoutingRefinement
            (PositionedPeriodicCNF.canonicalClausePosition
              (PeriodicEightOccurrenceSplitPositioned.placement
                placement)
              (PeriodicEightOccurrenceSplitPositioned.occurrenceClause
                occurrencePorts clauseIndex
                metadata.sourceClause)) := by
      rw [canonicalClausePosition_occurrenceClause,
        Cell.scale_scale]
      simp [retainedTerminalFanTotalRefinement_eq,
        retainedTerminalFanRoutingRefinement,
        PeriodicEightOccurrenceSplitPositioned.refinementScale]
    rw [retainedAngularFanSplicedIncidenceRoutes_occurrence
      source placement routes clauseIndex literalIndex
      (by simpa [occurrencePorts] using occurrenceIndex),
      retainedAngularFanSplicedOccurrenceRoutes_of_members
        source placement routes
        sourceClauseMemberAt sourceLiteralMember]
    constructor
    · rw [explicitValid.1, copiedClausePosition,
        copiedClauseEqual]
    · simpa [order, occurrencePorts,
        copiedClauseEqual, copiedLiteralEqual] using
          explicitValid.2.1
  · have oldEndpoints :=
      cycleSplicedIncidenceRoutes_endpoints
        source placement occurrencePorts
        clauseMember literalMember
    let cycleIndex :=
      clauseIndex -
        (PeriodicEightOccurrenceSplitPositioned.occurrenceClauses
          source occurrencePorts).length
    have clauseIndexDecomposition :
        clauseIndex =
          (PeriodicEightOccurrenceSplitPositioned.occurrenceClauses
            source occurrencePorts).length + cycleIndex := by
      dsimp only [cycleIndex]
      omega
    have oldRouteEq :
        cycleSplicedIncidenceRoutes
            source placement occurrencePorts
            clauseIndex literalIndex =
          allCycleRoutes source placement
            cycleIndex literalIndex := by
      rw [clauseIndexDecomposition]
      exact cycleSplicedIncidenceRoutes_cycle
        source placement occurrencePorts
        cycleIndex literalIndex
    have newRouteEq :
        retainedAngularFanSplicedIncidenceRoutes
            source placement routes
            clauseIndex literalIndex =
          scalePolyline retainedTerminalFanRoutingRefinement
            (allCycleRoutes source placement
              cycleIndex literalIndex) := by
      rw [clauseIndexDecomposition]
      exact retainedAngularFanSplicedIncidenceRoutes_cycle
        source placement routes cycleIndex literalIndex
    rw [oldRouteEq] at oldEndpoints
    rw [newRouteEq]
    constructor
    · simp [oldEndpoints.1]
    · simp [oldEndpoints.2]

/-- Every genuine route in the complete refined family is orthogonal. -/
theorem retainedAngularFanSplicedIncidenceRoutes_orthogonal
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
        (PeriodicEightOccurrenceSplitPositioned.formula
          source placement
          (occurrencePortsOfAngularOrder
            source.erase
            (angularOccurrenceOrder
              source.erase routes))).clauses.zipIdx)
    {literal :
      PeriodicLiteral
        (ThreeOccurrenceVariable Variable)}
    {literalIndex : Nat}
    (literalMember :
      (literal, literalIndex) ∈ clause.literals.zipIdx) :
    PeriodicOrthocrossing.OrthogonalPolyline
      (retainedAngularFanSplicedIncidenceRoutes
        source placement routes clauseIndex literalIndex) := by
  let order :=
    angularOccurrenceOrder source.erase routes
  let occurrencePorts :=
    occurrencePortsOfAngularOrder source.erase order
  by_cases occurrenceIndex :
      clauseIndex <
        (PeriodicEightOccurrenceSplitPositioned.occurrenceClauses
          source occurrencePorts).length
  · have copiedClauseMember :=
      occurrenceClauseMember_of_formula_member
        source placement order clauseMember occurrenceIndex
    rcases occurrenceClauseMetadata_lookup
        source occurrencePorts copiedClauseMember with
      ⟨metadata, _metadataLookup, metadataClauseEqual,
        sourceClauseMember, metadataIndex,
        metadataClauseDefinition⟩
    have sourceClauseMemberAt :
        (metadata.sourceClause, clauseIndex) ∈
          source.clauses.zipIdx := by
      simpa [metadataIndex] using sourceClauseMember
    have copiedClauseEqual :
        clause =
          PeriodicEightOccurrenceSplitPositioned.occurrenceClause
            occurrencePorts clauseIndex
            metadata.sourceClause := by
      calc
        clause = metadata.clause :=
          metadataClauseEqual.symm
        _ =
            PeriodicEightOccurrenceSplitPositioned.occurrenceClause
              occurrencePorts metadata.clauseIndex
              metadata.sourceClause :=
          metadataClauseDefinition
        _ =
            PeriodicEightOccurrenceSplitPositioned.occurrenceClause
              occurrencePorts clauseIndex
              metadata.sourceClause := by
          rw [metadataIndex]
    rcases occurrenceLiteral_of_members
        occurrencePorts copiedClauseEqual literalMember with
      ⟨sourceLiteral, sourceLiteralMember,
        _copiedLiteralEqual⟩
    rw [retainedAngularFanSplicedIncidenceRoutes_occurrence
      source placement routes clauseIndex literalIndex
      (by simpa [occurrencePorts] using occurrenceIndex),
      retainedAngularFanSplicedOccurrenceRoutes_of_members
        source placement routes
        sourceClauseMemberAt sourceLiteralMember]
    exact
      (retainedAngularFanSplicedOccurrenceRoute_valid
        source placement routes fits certificate
        endpoints lengths retainedRoutes
        sourceClauseMemberAt sourceLiteralMember).2.2
  · have oldOrthogonal :=
      cycleSplicedIncidenceRoutes_orthogonal
        source placement occurrencePorts
        clauseMember literalMember
    let cycleIndex :=
      clauseIndex -
        (PeriodicEightOccurrenceSplitPositioned.occurrenceClauses
          source occurrencePorts).length
    have clauseIndexDecomposition :
        clauseIndex =
          (PeriodicEightOccurrenceSplitPositioned.occurrenceClauses
            source occurrencePorts).length + cycleIndex := by
      dsimp only [cycleIndex]
      omega
    have oldRouteEq :
        cycleSplicedIncidenceRoutes
            source placement occurrencePorts
            clauseIndex literalIndex =
          allCycleRoutes source placement
            cycleIndex literalIndex := by
      rw [clauseIndexDecomposition]
      exact cycleSplicedIncidenceRoutes_cycle
        source placement occurrencePorts
        cycleIndex literalIndex
    have newRouteEq :
        retainedAngularFanSplicedIncidenceRoutes
            source placement routes
            clauseIndex literalIndex =
          scalePolyline retainedTerminalFanRoutingRefinement
            (allCycleRoutes source placement
              cycleIndex literalIndex) := by
      rw [clauseIndexDecomposition]
      exact retainedAngularFanSplicedIncidenceRoutes_cycle
        source placement routes cycleIndex literalIndex
    rw [oldRouteEq] at oldOrthogonal
    rw [newRouteEq]
    exact oldOrthogonal.scalePolyline
      (by simp [retainedTerminalFanRoutingRefinement])

/-- Re-express the endpoint theorem directly in the scaled positioned
formula and placement used by the assembled drawing. -/
theorem retainedAngularFanRefinedIncidenceRoutes_endpoints
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
    (retainedAngularFanSplicedIncidenceRoutes
      source placement routes clauseIndex literalIndex).head? =
        some
          (PositionedPeriodicCNF.canonicalClausePosition
            (retainedAngularFanRefinedPlacement placement)
            clause) ∧
      (retainedAngularFanSplicedIncidenceRoutes
        source placement routes clauseIndex literalIndex).getLast? =
          some
            (PositionedPeriodicCNF.canonicalLiteralPosition
              (retainedAngularFanRefinedPlacement placement)
              clause literal) := by
  rw [retainedAngularFanRefinedFormula,
    PositionedPeriodicCNF.scale_clauses,
    List.zipIdx_map] at clauseMember
  rcases List.mem_map.mp clauseMember with
    ⟨taggedClause, taggedClauseMember,
      taggedClauseEqual⟩
  have clauseIndexEqual :
      taggedClause.2 = clauseIndex :=
    congrArg Prod.snd taggedClauseEqual
  have scaledClauseEqual :
      taggedClause.1.scale
          retainedTerminalFanRoutingRefinement =
        clause :=
    congrArg Prod.fst taggedClauseEqual
  subst clauseIndex
  subst clause
  have sourceLiteralMember :
      (literal, literalIndex) ∈
        taggedClause.1.literals.zipIdx := by
    simpa using literalMember
  have baseEndpoints :=
    retainedAngularFanSplicedIncidenceRoutes_endpoints
      source placement routes fits certificate
      endpoints lengths retainedRoutes
      taggedClauseMember sourceLiteralMember
  constructor
  · simpa [retainedAngularFanRefinedPlacement] using
      baseEndpoints.1
  · simpa [retainedAngularFanRefinedPlacement] using
      baseEndpoints.2

/-- The orthogonality theorem likewise applies directly to genuine
incidences of the scaled positioned formula. -/
theorem retainedAngularFanRefinedIncidenceRoutes_orthogonal
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
    PeriodicOrthocrossing.OrthogonalPolyline
      (retainedAngularFanSplicedIncidenceRoutes
        source placement routes clauseIndex literalIndex) := by
  rw [retainedAngularFanRefinedFormula,
    PositionedPeriodicCNF.scale_clauses,
    List.zipIdx_map] at clauseMember
  rcases List.mem_map.mp clauseMember with
    ⟨taggedClause, taggedClauseMember,
      taggedClauseEqual⟩
  have clauseIndexEqual :
      taggedClause.2 = clauseIndex :=
    congrArg Prod.snd taggedClauseEqual
  have scaledClauseEqual :
      taggedClause.1.scale
          retainedTerminalFanRoutingRefinement =
        clause :=
    congrArg Prod.fst taggedClauseEqual
  subst clauseIndex
  subst clause
  have sourceLiteralMember :
      (literal, literalIndex) ∈
        taggedClause.1.literals.zipIdx := by
    simpa using literalMember
  exact retainedAngularFanSplicedIncidenceRoutes_orthogonal
    source placement routes fits certificate
    endpoints lengths retainedRoutes
    taggedClauseMember sourceLiteralMember

end PeriodicEightOccurrenceSplit
end LeanTrominoes
