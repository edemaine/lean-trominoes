import LeanTrominoes.RetainedAngularFanDrawing
import LeanTrominoes.RetainedAngularFanSourceScaling

/-!
# Canonical retained angular-fan drawing after source-first scaling

The global retained source is refined by the fixed clearance factor before
the finite angular fans are inserted.  This module transports the canonical
endpoint, retained-ray, length, and terminal certificates through that scale,
then packages the resulting complete fixed-eight route family as canonical
orthogonal incidence routes.
-/

namespace LeanTrominoes
namespace PeriodicEightOccurrenceSplit

open PeriodicThreeSATThree

set_option maxHeartbeats 2000000

/-- Scaling a canonical retained source first and then inserting angular fans
produces canonical orthogonal routes for the source-scaled refined formula. -/
def retainedAngularFanSourceScaledCanonicalOrthogonalRoutes
    {Variable : Type*} [DecidableEq Variable]
    {factor : Nat} (factorPositive : 0 < factor)
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
    PositionedPeriodicCNF.CanonicalOrthogonalIncidenceRoutes
      (retainedAngularFanSourceScaledRefinedFormula
        factor source placement family.routes)
      (retainedAngularFanSourceScaledRefinedPlacement
        factor placement) := by
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
              factor family.routes
              clauseIndex literalIndex).length := by
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
      lengths
        taggedClause.1 taggedClause.2 taggedClauseMember
        literal literalIndex sourceLiteralMember
  simpa [retainedAngularFanSourceScaledRefinedFormula,
    retainedAngularFanSourceScaledRefinedPlacement,
    scaledFamily] using
    retainedAngularFanRefinedCanonicalOrthogonalRoutes
      (source.scale factor)
      (placement.scale factor)
      (PositionedPeriodicCNF.scaleIncidenceRoutes
        factor family.routes)
      scaledFits scaledCertificate
      scaledFamily.endpoints scaledLengths scaledFamily.retained

/-- Certificate-by-certificate form of
`retainedAngularFanSourceScaledCanonicalOrthogonalRoutes`.  This avoids
forcing clients to construct the retained-route package while elaborating a
large concrete positioned formula. -/
def retainedAngularFanSourceScaledCanonicalOrthogonalRoutesOfCertificates
    {Variable : Type*} [DecidableEq Variable]
    {factor : Nat} (factorPositive : 0 < factor)
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
    (retained :
      ∀ clause clauseIndex,
        (clause, clauseIndex) ∈ source.clauses.zipIdx →
        ∀ literal literalIndex,
          (literal, literalIndex) ∈ clause.literals.zipIdx →
          RetainedRayPolyline
            (routes clauseIndex literalIndex)) :
    PositionedPeriodicCNF.CanonicalOrthogonalIncidenceRoutes
      (retainedAngularFanSourceScaledRefinedFormula
        factor source placement routes)
      (retainedAngularFanSourceScaledRefinedPlacement
        factor placement) :=
  retainedAngularFanSourceScaledCanonicalOrthogonalRoutes
    factorPositive source placement
    { routes := routes
      endpoints := endpoints
      retained := retained }
    fits certificate lengths

end PeriodicEightOccurrenceSplit

namespace PeriodicOrthocrossing

open PeriodicEightOccurrenceSplit
open PeriodicThreeSATThree

set_option maxHeartbeats 2000000

/-- The final retained planar-SAT source, refined by the fixed source
clearance factor before inserting its angular fans. -/
def retainedDrawingSourceScaledRefinedEightOccurrenceSplitPositionedFormula
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable) :
    PositionedPeriodicCNF
      (ThreeOccurrenceVariable
        (WrappedPeriodicPlanarSATVariable Variable)) :=
  retainedAngularFanSourceScaledRefinedFormula
    retainedAngularFanSourceClearanceFactor
    (retainedDeduplicatedGaugedWrappedDrawingPositionedPeriodicPlanarSATFormula
      source)
    (retainedGaugedWrappedDrawingPeriodicPlanarSATPlacement source)
    (retainedDeduplicatedGaugedWrappedDrawingPeriodicPlanarSATIncidenceRoutes
      source)

/-- Placement paired with the source-scaled retained fixed-eight formula. -/
def retainedDrawingSourceScaledRefinedEightOccurrenceSplitPlacement
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable) :
    PeriodicVariablePlacement
      (ThreeOccurrenceVariable
        (WrappedPeriodicPlanarSATVariable Variable)) :=
  retainedAngularFanSourceScaledRefinedPlacement
    retainedAngularFanSourceClearanceFactor
    (retainedGaugedWrappedDrawingPeriodicPlanarSATPlacement source)

/-- Complete route family obtained by scaling the final retained source
before inserting its unchanged fixed-size angular fans. -/
def retainedDrawingSourceScaledRefinedEightOccurrenceSplitIncidenceRoutes
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable) :
    PositionedPeriodicCNF.IncidenceRoutes :=
  retainedAngularFanSourceScaledSplicedIncidenceRoutes
    retainedAngularFanSourceClearanceFactor
    (retainedDeduplicatedGaugedWrappedDrawingPositionedPeriodicPlanarSATFormula
      source)
    (retainedGaugedWrappedDrawingPeriodicPlanarSATPlacement source)
    (retainedDeduplicatedGaugedWrappedDrawingPeriodicPlanarSATIncidenceRoutes
      source)

/-- Source-first clearance scaling changes coordinates but leaves the
established retained fixed-eight logical formula unchanged. -/
@[simp]
theorem
    retainedDrawingSourceScaledRefinedEightOccurrenceSplitPositionedFormula_erase
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable) :
    (retainedDrawingSourceScaledRefinedEightOccurrenceSplitPositionedFormula
      source).erase =
      retainedDrawingEightOccurrenceSplitFormula source := by
  rw [retainedDrawingSourceScaledRefinedEightOccurrenceSplitPositionedFormula,
    retainedAngularFanSourceScaledRefinedFormula_erase
      retainedAngularFanSourceClearanceFactor_pos]
  simp [retainedDrawingEightOccurrenceSplitFormula,
    retainedDrawingAngularOccurrencePorts,
    retainedDrawingAngularOccurrenceOrder,
    retainedPlanarSATFormula]

/-- The source-scaled retained fixed-eight placement has positive period. -/
theorem
    retainedDrawingSourceScaledRefinedEightOccurrenceSplitPlacement_period_pos
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable) :
    0 <
      (retainedDrawingSourceScaledRefinedEightOccurrenceSplitPlacement
        source).period := by
  apply retainedAngularFanSourceScaledRefinedPlacement_period_pos
    retainedAngularFanSourceClearanceFactor_pos
  simpa [retainedGaugedWrappedDrawingPeriodicPlanarSATPlacement,
    wrappedDrawingPeriodicPlanarSATPlacement] using
    drawingPeriodicPlanarSATPlacement_period_pos source

/-- The concrete source-scaled retained fan construction, packaged with
canonical endpoints and pointwise orthogonality. -/
def
    retainedDrawingSourceScaledRefinedEightOccurrenceSplitCanonicalOrthogonalRoutes
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (sourceLocal : source.IsLocal)
    (sourceWidth : source.WidthAtMost 3)
    (sourceOccurrences : source.OccurrencesAtMost 3)
    (sourceClausesNonempty :
      ∀ clause ∈ source.clauses, clause ≠ []) :
    PositionedPeriodicCNF.CanonicalOrthogonalIncidenceRoutes
      (retainedDrawingSourceScaledRefinedEightOccurrenceSplitPositionedFormula
        source)
      (retainedDrawingSourceScaledRefinedEightOccurrenceSplitPlacement
        source) := by
  let sourceCertificate :=
    retainedPlanarSATCertificate source
      sourceLocal sourceWidth sourceOccurrences
      sourceClausesNonempty
  let retainedClausesNonempty :=
    retainedDrawingPlanarSATFormula_clausesNonempty_of_source
      source sourceClausesNonempty
  apply retainedAngularFanSourceScaledCanonicalOrthogonalRoutesOfCertificates
    retainedAngularFanSourceClearanceFactor_pos
    (retainedDeduplicatedGaugedWrappedDrawingPositionedPeriodicPlanarSATFormula
      source)
    (retainedGaugedWrappedDrawingPeriodicPlanarSATPlacement source)
    (retainedDeduplicatedGaugedWrappedDrawingPeriodicPlanarSATIncidenceRoutes
      source)
  · simpa [retainedDrawingAngularOccurrenceOrder,
      retainedPlanarSATFormula] using
      retainedDrawingAngularOccurrenceOrder_fitsEightSlots
        sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty
  · exact
      retainedDeduplicatedGaugedWrappedDrawingPeriodicPlanarSATOccurrence_terminalCertificate
        source
        sourceCertificate.graphWellFormed
        sourceCertificate.graphDegreeAtMostThree
        sourceCertificate.graphIsLocal
        retainedClausesNonempty
  · intro clause clauseIndex clauseMember
      literal literalIndex literalMember
    exact
      retainedDeduplicatedGaugedWrappedDrawingPeriodicPlanarSATIncidenceRoutes_endpoints
        source
        sourceCertificate.graphWellFormed
        sourceCertificate.graphDegreeAtMostThree
        sourceCertificate.graphIsLocal
        clauseMember literalMember
  · intro clause clauseIndex clauseMember
      literal literalIndex literalMember
    exact
      retainedDeduplicatedGaugedWrappedDrawingPeriodicPlanarSATIncidenceRoutes_length_ge_two
        source
        sourceCertificate.graphWellFormed
        sourceCertificate.graphDegreeAtMostThree
        sourceCertificate.graphIsLocal
        retainedClausesNonempty
        clauseMember literalMember
  · intro clause clauseIndex clauseMember
      literal literalIndex literalMember
    exact
      retainedDeduplicatedGaugedWrappedDrawingPeriodicPlanarSATIncidenceRoutes_retainedRay
        source
        sourceCertificate.graphWellFormed
        sourceCertificate.graphDegreeAtMostThree
        sourceCertificate.graphIsLocal
        retainedClausesNonempty
        (clause, clauseIndex) clauseMember
        (literal, literalIndex) literalMember

end PeriodicOrthocrossing
end LeanTrominoes
