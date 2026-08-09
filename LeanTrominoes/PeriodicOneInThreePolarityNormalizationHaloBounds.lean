import LeanTrominoes.PeriodicOneInThreePolarityNormalizationContinuousPlanarPresentation
import LeanTrominoes.PeriodicOneInThreePolarityNormalizationRawRouteBounds
import LeanTrominoes.PositionedPeriodicCNFRebasedRouteTransport

/-!
# Halo bounds after polarity-normalization gauging

The final fresh-variable gauge has two geometric behaviors.  Routes ending
at embedded original variables have zero gauge and retain the raw rebased
halo certificate.  Routes ending at fresh variables acquire the inverse
source-occurrence shift; this cancels the raw canonical shift and leaves a
two-point fragment among refined route points zero, one, and two, all inside
the final fundamental square.
-/

namespace LeanTrominoes
namespace PeriodicOneInThreePolarityNormalizationRouteSubdivision

open PeriodicOneInThreePolarityNormalization

/-- The raw and final gauged drawings have the same grid size, so raw halo
membership can be read directly in the final drawing. -/
theorem finalPositionInExpandedSquare_of_raw
    {Variable : Type*} [DecidableEq Variable]
    {source : PositionedPeriodicCNF Variable}
    {sourcePlacement : PeriodicVariablePlacement Variable}
    (presentation :
      PositionedPeriodicCNF.ContinuousPlanarIncidencePresentation
        source sourcePlacement)
    {point : Cell}
    (inside :
      (rawIncidenceDrawing presentation).PositionInExpandedSquare point) :
    (PositionedPeriodicCNF.incidenceDrawing
      (formula source sourcePlacement presentation.routes)
      (placement sourcePlacement presentation.routes)
      (incidenceRoutes source sourcePlacement presentation.routes))
        |>.PositionInExpandedSquare point := by
  have rawGridSize :
      (rawIncidenceDrawing presentation).gridSize =
        (refinedPlacement sourcePlacement).period := by
    rw [show
      (rawIncidenceDrawing presentation).gridSize =
          (rawPlacement sourcePlacement presentation.routes).period by
        simpa [rawIncidenceDrawing] using
          PositionedPeriodicCNF.incidenceDrawing_gridSize
            (rawFormula source sourcePlacement presentation.routes)
            (rawPlacement sourcePlacement presentation.routes)
            (rawIncidenceRoutes source sourcePlacement presentation.routes)
            (rawPlacement_periodPositive presentation)]
    exact rawPlacement_period sourcePlacement presentation.routes
  have finalGridSize := incidenceDrawing_gridSize_eq_refinedPlacement_period
    presentation
  unfold PeriodicGridDrawing.PositionInExpandedSquare at inside ⊢
  rw [rawGridSize] at inside
  rw [finalGridSize]
  exact inside

/-- The final gauged polarity-normalized presentation inherits the ordinary
open rebased-route halo bound. -/
theorem continuousPlanarPresentation_rebasedRoutePointsInExpandedSquare
    {Variable : Type*} [DecidableEq Variable]
    {source : PositionedPeriodicCNF Variable}
    {sourcePlacement : PeriodicVariablePlacement Variable}
    (presentation :
      PositionedPeriodicCNF.HaloBoundedContinuousPlanarIncidencePresentation
        source sourcePlacement) :
    (continuousPlanarPresentation
      presentation.toContinuousPlanarIncidencePresentation)
      |>.toPlanarIncidencePresentation
      |>.RebasedRoutePointsInExpandedSquare := by
  intro gaugedTagged gaugedTaggedMember point pointMember
  let continuous := presentation.toContinuousPlanarIncidencePresentation
  have gaugedTaggedMember' := gaugedTaggedMember
  change gaugedTagged ∈
    (PeriodicCNF.incidencesWithMetadata
      ((rawFormula source sourcePlacement presentation.routes)
        |>.variableGauge freshGauge).erase).zipIdx at gaugedTaggedMember'
  rw [PositionedPeriodicCNF.erase_variableGauge,
    PeriodicCNF.incidencesWithMetadata_variableGauge,
    List.zipIdx_map] at gaugedTaggedMember'
  rcases List.mem_map.mp gaugedTaggedMember' with
    ⟨rawTagged, rawTaggedMember, gaugedTaggedEq⟩
  subst gaugedTagged
  let descriptor :=
    (exists_rawRouteDescriptor continuous rawTaggedMember).some
  rcases PositionedPeriodicCNF.incidenceMetadata_of_tagged
      (rawFormula source sourcePlacement presentation.routes)
      rawTaggedMember with
    ⟨rawClause, rawLiteral, rawClauseMember,
      rawLiteralMember, rawIncidenceEq⟩
  have rawTaggedClauseEq : rawTagged.1.clause = rawClause.literals :=
    congrArg CNFIncidence.clause rawIncidenceEq
  have rawTaggedLiteralEq : rawTagged.1.literal = rawLiteral :=
    congrArg CNFIncidence.literal rawIncidenceEq
  change point ∈ PeriodicOrthocrossing.translatePolyline
      ((placement sourcePlacement presentation.routes).translation
        (Cell.sub
          (PeriodicCNF.clauseAnchor
            (rawTagged.1.clause.variableGauge freshGauge))
          (rawTagged.1.literal.variableGauge freshGauge).offset))
      (incidenceRoutes source sourcePlacement presentation.routes
        rawTagged.1.clauseIndex rawTagged.1.literalIndex).reverse at pointMember
  rw [rawIncidenceEq] at pointMember
  have pointMember' :
      point ∈ PeriodicOrthocrossing.translatePolyline
        (((rawPlacement sourcePlacement presentation.routes)
            |>.variableGauge freshGauge).translation
          (Cell.sub
            (PeriodicCNF.clauseAnchor
              (rawClause.literals.variableGauge freshGauge))
            (rawLiteral.variableGauge freshGauge).offset))
        (PositionedPeriodicCNF.variableGaugeCanonicalIncidenceRoutes
          (rawFormula source sourcePlacement presentation.routes)
          (rawPlacement sourcePlacement presentation.routes)
          freshGauge
          (rawIncidenceRoutes source sourcePlacement presentation.routes)
          rawTagged.1.clauseIndex rawTagged.1.literalIndex).reverse := by
    simpa only [placement, incidenceRoutes] using pointMember
  rw [PositionedPeriodicCNF.variableGaugeCanonicalIncidenceRoutes_rebasedRoute_eq
    (rawFormula source sourcePlacement presentation.routes)
    (rawPlacement sourcePlacement presentation.routes)
    freshGauge
    (rawIncidenceRoutes source sourcePlacement presentation.routes)
    rawClauseMember] at pointMember'
  have literalCases := descriptor.outputLiteral_classify rawTaggedMember
  rw [rawIncidenceEq] at literalCases
  rcases literalCases with wholeCase | prefixCase | middleCase | suffixCase
  · rcases wholeCase with ⟨_fragmentEq, rawLiteralEq⟩
    change rawLiteral = liftLiteral descriptor.sourceLiteral at rawLiteralEq
    have rawGaugeEq : freshGauge rawLiteral.atom = (0, 0) := by
      rw [rawLiteralEq]
      rfl
    have rawPointMember :
        point ∈ PeriodicOrthocrossing.translatePolyline
          ((rawPlacement sourcePlacement presentation.routes).translation
            (Cell.sub
              (PeriodicCNF.clauseAnchor rawClause.literals)
              rawLiteral.offset))
          (rawIncidenceRoutes source sourcePlacement presentation.routes
            rawTagged.1.clauseIndex rawTagged.1.literalIndex).reverse := by
      simpa [rawGaugeEq,
        PeriodicOrthocrossing.translatePolyline,
        PeriodicVariablePlacement.translation, Cell.add, Cell.sub,
        Cell.scale] using pointMember'
    exact finalPositionInExpandedSquare_of_raw continuous
      (rawIncidenceRoutes_rebasedRoutePointsInExpandedSquare presentation
        rawTagged rawTaggedMember point (by
          rw [rawTaggedClauseEq, rawTaggedLiteralEq]
          exact rawPointMember))
  · rcases prefixCase with ⟨fragmentEq, rawLiteralEq⟩
    change rawLiteral =
      complementLiteral descriptor.metadata.sourceClauseIndex
        descriptor.sourceLiteralIndex descriptor.sourceLiteral at rawLiteralEq
    have descriptorRouteEq := descriptor.rebasedRouteEq rawTaggedMember
    rw [rawIncidenceEq] at descriptorRouteEq
    rw [descriptorRouteEq] at pointMember'
    have sourceAnchor := refinedSource_clauseAnchor_eq_zero
      source sourcePlacement descriptor.sourceClauseMember
    have rawGaugeEq :
        freshGauge rawLiteral.atom =
          Cell.sub (0, 0) descriptor.sourceLiteral.offset := by
      rw [rawLiteralEq]
      rfl
    have shiftsCancel :
        Cell.add
            ((refinedPlacement sourcePlacement).translation
              (Cell.sub
                (PeriodicCNF.clauseAnchor
                  descriptor.metadata.sourceClause.literals)
                descriptor.sourceLiteral.offset))
            ((rawPlacement sourcePlacement presentation.routes).translation
              (Cell.sub (0, 0) (freshGauge rawLiteral.atom))) =
          (0, 0) := by
      rw [rawGaugeEq, sourceAnchor]
      rcases descriptor.sourceLiteral.offset with ⟨sourceX, sourceY⟩
      apply Prod.ext <;>
        simp [PeriodicVariablePlacement.translation,
          Cell.add, Cell.sub, Cell.scale]
    rw [PeriodicOrthocrossing.translatePolyline_add, shiftsCancel,
      PeriodicOrthocrossing.translatePolyline_zero] at pointMember'
    have fragmentPointMember :
        point ∈ descriptor.fragment.select
          (refinedRoute presentation.routes
            descriptor.metadata.sourceClauseIndex
            descriptor.sourceLiteralIndex) := by
      simpa using pointMember'
    exact descriptor.nearClauseFragment_pointInsideFinalExpandedSquare
      (Or.inl fragmentEq) fragmentPointMember
  · rcases middleCase with ⟨fragmentEq, rawLiteralEq⟩
    change rawLiteral =
      complementFalseLiteral descriptor.metadata.sourceClauseIndex
        descriptor.sourceLiteralIndex descriptor.sourceLiteral at rawLiteralEq
    have descriptorRouteEq := descriptor.rebasedRouteEq rawTaggedMember
    rw [rawIncidenceEq] at descriptorRouteEq
    rw [descriptorRouteEq] at pointMember'
    have sourceAnchor := refinedSource_clauseAnchor_eq_zero
      source sourcePlacement descriptor.sourceClauseMember
    have rawGaugeEq :
        freshGauge rawLiteral.atom =
          Cell.sub (0, 0) descriptor.sourceLiteral.offset := by
      rw [rawLiteralEq]
      rfl
    have shiftsCancel :
        Cell.add
            ((refinedPlacement sourcePlacement).translation
              (Cell.sub
                (PeriodicCNF.clauseAnchor
                  descriptor.metadata.sourceClause.literals)
                descriptor.sourceLiteral.offset))
            ((rawPlacement sourcePlacement presentation.routes).translation
              (Cell.sub (0, 0) (freshGauge rawLiteral.atom))) =
          (0, 0) := by
      rw [rawGaugeEq, sourceAnchor]
      rcases descriptor.sourceLiteral.offset with ⟨sourceX, sourceY⟩
      apply Prod.ext <;>
        simp [PeriodicVariablePlacement.translation,
          Cell.add, Cell.sub, Cell.scale]
    rw [PeriodicOrthocrossing.translatePolyline_add, shiftsCancel,
      PeriodicOrthocrossing.translatePolyline_zero] at pointMember'
    have fragmentPointMember :
        point ∈ descriptor.fragment.select
          (refinedRoute presentation.routes
            descriptor.metadata.sourceClauseIndex
            descriptor.sourceLiteralIndex) := by
      simpa using pointMember'
    exact descriptor.nearClauseFragment_pointInsideFinalExpandedSquare
      (Or.inr fragmentEq) fragmentPointMember
  · rcases suffixCase with ⟨_fragmentEq, rawLiteralEq⟩
    change rawLiteral = originalFalseLiteral descriptor.sourceLiteral at rawLiteralEq
    have rawGaugeEq : freshGauge rawLiteral.atom = (0, 0) := by
      rw [rawLiteralEq]
      rfl
    have rawPointMember :
        point ∈ PeriodicOrthocrossing.translatePolyline
          ((rawPlacement sourcePlacement presentation.routes).translation
            (Cell.sub
              (PeriodicCNF.clauseAnchor rawClause.literals)
              rawLiteral.offset))
          (rawIncidenceRoutes source sourcePlacement presentation.routes
            rawTagged.1.clauseIndex rawTagged.1.literalIndex).reverse := by
      simpa [rawGaugeEq,
        PeriodicOrthocrossing.translatePolyline,
        PeriodicVariablePlacement.translation, Cell.add, Cell.sub,
        Cell.scale] using pointMember'
    exact finalPositionInExpandedSquare_of_raw continuous
      (rawIncidenceRoutes_rebasedRoutePointsInExpandedSquare presentation
        rawTagged rawTaggedMember point (by
          rw [rawTaggedClauseEq, rawTaggedLiteralEq]
          exact rawPointMember))

/-- Package polarity normalization as a continuously planar presentation
with the rebased-route halo bound required by ribbon assembly. -/
def haloBoundedContinuousPlanarPresentation
    {Variable : Type*} [DecidableEq Variable]
    {source : PositionedPeriodicCNF Variable}
    {sourcePlacement : PeriodicVariablePlacement Variable}
    (presentation :
      PositionedPeriodicCNF.HaloBoundedContinuousPlanarIncidencePresentation
        source sourcePlacement) :
    PositionedPeriodicCNF.HaloBoundedContinuousPlanarIncidencePresentation
      (formula source sourcePlacement presentation.routes)
      (placement sourcePlacement presentation.routes) where
  toContinuousPlanarIncidencePresentation :=
    continuousPlanarPresentation
      presentation.toContinuousPlanarIncidencePresentation
  rebasedRoutePointsInside :=
    continuousPlanarPresentation_rebasedRoutePointsInExpandedSquare presentation

end PeriodicOneInThreePolarityNormalizationRouteSubdivision
end LeanTrominoes
