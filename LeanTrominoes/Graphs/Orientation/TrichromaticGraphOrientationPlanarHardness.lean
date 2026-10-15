/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.Graphs.Orientation.TrichromaticGraphOrientationCompleteness
import LeanTrominoes.Graphs.Drawings.Grid.PeriodicGridDrawingIndexing
import LeanTrominoes.ThreeDM.PeriodicThreeDMContractionContinuousPlanarity
import LeanTrominoes.ThreeDM.PeriodicThreeDMContractionEndpointContacts

/-! # Ordinary colored graph orientation has planar hard instances

The computable reduction still emits only vertex kinds and colored edges.
Its drawing is an existence certificate, not part of the reduction output.
-/
namespace LeanTrominoes.TrichromaticGraphOrientation

def underlyingGraph (input : Input) : PeriodicGraph Nat :=
  ⟨List.range input.1.length,input.2.map Prod.fst⟩

def HasPlanarPresentation (input : Input) : Prop :=
  ∃ drawing : PeriodicGridDrawing,
    drawing.IsCompatible (underlyingGraph input) ∧ drawing.IsOrthogonal ∧
      drawing.IsContinuouslyPlanar ∧ drawing.LiftedRoutesAvoidEachOther ∧
      (∀ route ∈ drawing.edgeRoutes, LocalIncidenceDrawing.RouteIsSimple route)

def PlanarProblem (input : Input) : Prop := Problem input ∧ HasPlanarPresentation input

theorem underlyingGraph_contracted (problem : PeriodicThreeDM) :
    underlyingGraph (PeriodicThreeDM.GraphOrientationEncoding.input problem) =
      problem.contractedGraph.indexed := by
  simp only [underlyingGraph,PeriodicThreeDM.GraphOrientationEncoding.input,
    List.length_map,List.map_map,PeriodicGraph.indexed,
    PeriodicThreeDM.contractedGraph]
  rfl

theorem wangReduction_hasPlanarPresentation (tiles : LeanWang.TileSet) :
    HasPlanarPresentation (wangReduction tiles) := by
  let presentation := PeriodicWangPlanarThreeDMReduction.presentation tiles
  let degree := PeriodicWangPlanarThreeDMReduction.problem_degreeTwoOrThree tiles
  refine ⟨presentation.contractedDrawing, ?_, ?_, ?_, ?_, ?_⟩
  · rw [wangReduction,underlyingGraph_contracted]
    exact PeriodicGridDrawing.isCompatible_indexed
      presentation.toPlanarPresentation.contractedDrawing_isCompatible
  · exact presentation.toPlanarPresentation.contractedDrawing_isOrthogonal
  · exact presentation.contractedDrawing_isContinuouslyPlanar degree
  · exact presentation.toPlanarPresentation.contractedDrawing_liftedRoutesAvoidEachOther degree
      (PeriodicWangPlanarThreeDMReduction.presentation_separated tiles)
  · exact presentation.toPlanarPresentation.contractedDrawing_routesSimple degree
      (PeriodicWangPlanarThreeDMReduction.presentation_separated tiles)
      (PeriodicWangPlanarThreeDMReduction.presentation_routesSimple tiles)

theorem wangReduction_planar_correct (tiles : LeanWang.TileSet) :
    PlanarProblem (wangReduction tiles) ↔ LeanWang.TilesPlane tiles := by
  rw [PlanarProblem,and_iff_left (wangReduction_hasPlanarPresentation tiles)]
  exact wangReduction_correct tiles

theorem planarProblem_coREHard : LeanWang.CoREHard PlanarProblem := by
  intro A _ source hs
  obtain ⟨f,hf,correct⟩ := LeanWang.domino_problem_coRE_hard source hs
  refine ⟨wangReduction ∘ f,wangReduction_computable.comp hf,?_⟩
  intro a
  exact (correct a).trans (wangReduction_planar_correct (f a)).symm

end LeanTrominoes.TrichromaticGraphOrientation
