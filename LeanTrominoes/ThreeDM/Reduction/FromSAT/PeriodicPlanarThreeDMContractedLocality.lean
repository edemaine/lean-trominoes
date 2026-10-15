/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.ThreeDM.Reduction.FromSAT.PeriodicPlanarThreeDMIncidenceOffsets
import LeanTrominoes.ThreeDM.Reduction.FromSAT.PeriodicPlanarThreeDMLocality
import LeanTrominoes.ThreeDM.PeriodicThreeDMContractionLocality

/-! # Locality survives contraction in the planar 3DM assembly -/
namespace LeanTrominoes.PeriodicPlanarOneInThreeToThreeDM

theorem encodedProblem_incidenceOffsetsComparable {V : Type*} [DecidableEq V]
    {source : PeriodicCNF V} (width : source.WidthAtMost 3) :
    (encodedProblem source).IncidenceOffsetsComparable := by
  intro color atom first firstMember second secondMember
  exact encoded_incidence_offsets_comparable width color atom firstMember secondMember

theorem encodedProblem_contractedGraph_isLocal {V : Type*} [DecidableEq V]
    {source : PeriodicCNF V} (width : source.WidthAtMost 3) (bounds : source.HasUnitOffsets) :
    (encodedProblem source).contractedGraph.IsLocal :=
  PeriodicThreeDM.contractedGraph_isLocal (encodedProblem_isLocal bounds)
    (encodedProblem_incidenceOffsetsComparable width)

theorem normalizedProblem_incidenceOffsetsComparable {V : Type*} [DecidableEq V]
    {source : PositionedPeriodicCNF V} (placement : PeriodicVariablePlacement V)
    (arity : PeriodicOneInThreeNoUnits.ArityTwoOrThree source.erase) :
    (normalizedProblem source placement).IncidenceOffsetsComparable := by
  apply encodedProblem_incidenceOffsetsComparable
  intro clause member
  have length := normalizedSource_arityTwoOrThree source placement arity clause member
  change clause.length ≤ 3
  omega

end LeanTrominoes.PeriodicPlanarOneInThreeToThreeDM

namespace LeanTrominoes.PeriodicOneInThreePolarityNormalizationRouteSubdivision

theorem paddedPeriodicThreeDMProblem_incidenceOffsetsComparable {V : Type*} [DecidableEq V]
    (source : PositionedPeriodicCNF V) (placement : PeriodicVariablePlacement V)
    (routes : PositionedPeriodicCNF.IncidenceRoutes)
    (arity : PeriodicOneInThreeNoUnits.ArityTwoOrThree source.erase) :
    (paddedPeriodicThreeDMProblem source placement routes).IncidenceOffsetsComparable := by
  apply PeriodicPlanarOneInThreeToThreeDM.normalizedProblem_incidenceOffsetsComparable
  simpa only [PositionedPeriodicCNF.erase_scale] using formula_arityTwoOrThree source placement routes arity

end LeanTrominoes.PeriodicOneInThreePolarityNormalizationRouteSubdivision
