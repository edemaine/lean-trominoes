/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.TrichromaticGraphOrientationLocalCoRE
import LeanTrominoes.TrichromaticGraphOrientationPlanarHardness
import LeanTrominoes.PeriodicPlanarThreeDMContractedLocality
import LeanTrominoes.PeriodicThreeDMLocalPlaneCompleteness

/-! # Local graph orientation is co-r.e. complete, with planar hard instances

The numeric graph reduction preserves locality after suppressing the
degree-two elements: a clause terminal determines every nonzero offset at
that element. Its ordinary graph output has an orthogonal planar drawing.
-/
namespace LeanTrominoes.PeriodicWangPlanarThreeDMReduction
open PeriodicOrthocrossing
set_option synthInstance.maxSize 2048
local instance {V : Type*} [DecidableEq V] :
    DecidableEq (RetainedOrderedFixedEightOneInThreeVariable V) :=
  PlanarOneInThreeNoUnitsFigureNine.nestedVariableDecidableEq

theorem problem_incidenceOffsetsComparable (tiles : LeanWang.TileSet) :
    (problem tiles).IncidenceOffsetsComparable := by
  unfold problem retainedOrderedFixedEightPolarityNormalizedPaddedPeriodicThreeDMProblem
  apply PeriodicOneInThreePolarityNormalizationRouteSubdivision.paddedPeriodicThreeDMProblem_incidenceOffsetsComparable
  exact retainedOrderedFixedEightPositionedPeriodicPlanarOneInThreeNoUnitsFinalGaugedFormula_arityTwoOrThree
    (sourceFormula tiles) (sourceFormula_isLocal tiles) (sourceFormula_widthAtMostThree tiles)
    (sourceFormula_occurrencesAtMostThree_canonicalBEq tiles) (sourceFormula_clausesNonempty tiles)

theorem problem_contractedGraph_isLocal (tiles : LeanWang.TileSet) :
    (problem tiles).contractedGraph.IsLocal :=
  PeriodicThreeDM.contractedGraph_isLocal (problem_isLocal tiles) (problem_incidenceOffsetsComparable tiles)

end LeanTrominoes.PeriodicWangPlanarThreeDMReduction

namespace LeanTrominoes.PeriodicThreeDM.GraphOrientationEncoding

theorem input_isLocal {problem : PeriodicThreeDM} (locality : problem.contractedGraph.IsLocal) :
    TrichromaticGraphOrientation.IsLocal (input problem) := by
  intro record member
  obtain ⟨edge,edgeMember,rfl⟩ := List.mem_map.mp member
  exact locality edge.toPeriodicEdge (List.mem_map.mpr ⟨edge,edgeMember,rfl⟩)

end LeanTrominoes.PeriodicThreeDM.GraphOrientationEncoding

namespace LeanTrominoes.TrichromaticGraphOrientation

theorem wangReduction_isLocal (tiles : LeanWang.TileSet) : IsLocal (wangReduction tiles) :=
  PeriodicThreeDM.GraphOrientationEncoding.input_isLocal
    (PeriodicWangPlanarThreeDMReduction.problem_contractedGraph_isLocal tiles)

theorem wangReduction_local_correct (tiles : LeanWang.TileSet) :
    LocalProblem (wangReduction tiles) ↔ LeanWang.TilesPlane tiles := by
  rw [LocalProblem,and_iff_right (wangReduction_isLocal tiles)]
  exact wangReduction_correct tiles

theorem localProblem_coREHard : LeanWang.CoREHard LocalProblem := by
  intro A _ source hs
  obtain ⟨f,hf,correct⟩ := LeanWang.domino_problem_coRE_hard source hs
  refine ⟨wangReduction ∘ f,wangReduction_computable.comp hf,?_⟩
  intro a
  exact (correct a).trans (wangReduction_local_correct (f a)).symm

theorem localProblem_coREComplete : LeanWang.CoREComplete LocalProblem :=
  ⟨localProblem_coRE,localProblem_coREHard⟩

def LocalPlanarProblem (input : Input) : Prop := IsLocal input ∧ PlanarProblem input

theorem wangReduction_localPlanar_correct (tiles : LeanWang.TileSet) :
    LocalPlanarProblem (wangReduction tiles) ↔ LeanWang.TilesPlane tiles := by
  rw [LocalPlanarProblem,and_iff_right (wangReduction_isLocal tiles)]
  exact wangReduction_planar_correct tiles

theorem localPlanarProblem_coREHard : LeanWang.CoREHard LocalPlanarProblem := by
  intro A _ source hs
  obtain ⟨f,hf,correct⟩ := LeanWang.domino_problem_coRE_hard source hs
  refine ⟨wangReduction ∘ f,wangReduction_computable.comp hf,?_⟩
  intro a
  exact (correct a).trans (wangReduction_localPlanar_correct (f a)).symm

end LeanTrominoes.TrichromaticGraphOrientation
