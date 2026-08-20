/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicThreeDMNormalizationTripleCellTypeIncidenceData
import LeanTrominoes.PeriodicThreeDMNormalizationEndpointTriplePermutation
import LeanTrominoes.PeriodicThreeDMContractedVertexFans

/-! # Triple cell types from RGB incidence-route data -/

noncomputable section

namespace LeanTrominoes

open Gadget DegreeThreeVertexNormalization

namespace PeriodicThreeDM
namespace NormalizationCompiler

/-- Original-incidence side/color datum for one named color at one indexed
triple. -/
def incidenceSideColorAt
    (input : Input) (tripleIndex : Nat)
    (color : WireColor) : EndpointSideColor :=
  (VertexSide.ofDirection
    (AxisDirection.polylineFirstDirection
      (incidenceRoute input ⟨tripleIndex, color⟩)), color)

/-- Canonical RGB ordering of the three original-incidence records. -/
def incidenceColorTripleData
    (input : Input) (tripleIndex : Nat) : EndpointTripleData :=
  (incidenceSideColorAt input tripleIndex .red,
    incidenceSideColorAt input tripleIndex .green,
    incidenceSideColorAt input tripleIndex .blue)

/-- Forgetting presentation proofs commutes definitionally with compression
of one contracted endpoint's side and color. -/
@[simp] theorem endpointSideColor_inputOfPresentation
    {problem : PeriodicThreeDM}
    (presentation : problem.PlanarPresentation)
    (endpoint : ContractedEndpoint) :
    endpointSideColor (inputOfPresentation presentation, endpoint) =
      (endpoint.outwardSide presentation, endpoint.color) := by
  cases endpoint with
  | source edge => cases edge <;> rfl
  | target edge => cases edge <;> rfl

/-- A triple fan's executable endpoint colors are a permutation of RGB. -/
theorem contractedVertexFan_colors_perm_incidenceColors
    {problem : PeriodicThreeDM}
    {presentation : problem.ContinuousPlanarPresentation}
    (degree : problem.DegreeTwoOrThree)
    (tripleIndex : Nat)
    (fan : ContractedVertexFan presentation (.triple tripleIndex)) :
    List.Perm [fan.first.color, fan.second.color, fan.third.color]
      incidenceColors := by
  have colorsNodup :
      [fan.first.color, fan.second.color, fan.third.color].Nodup := by
    simpa [ContractedVertexFan.coloredFan] using
      fan.colors_nodup_of_triple degree tripleIndex
  generalize firstEq : fan.first.color = firstColor at colorsNodup ⊢
  generalize secondEq : fan.second.color = secondColor at colorsNodup ⊢
  generalize thirdEq : fan.third.color = thirdColor at colorsNodup ⊢
  cases firstColor <;> cases secondColor <;> cases thirdColor <;>
    simp_all [incidenceColors] <;> decide

/-- At every genuine triple of a continuous planar presentation, the final
cell type is determined by the first directions of the red, green, and blue
original incidence routes in that fixed color order. -/
theorem finalVertexCellType_eq_incidenceColorTripleData
    {problem : PeriodicThreeDM}
    (presentation : problem.ContinuousPlanarPresentation)
    (wellFormed : problem.IsWellFormed)
    (degree : problem.DegreeTwoOrThree)
    (tripleIndex : Nat)
    (indexLt : tripleIndex < problem.triples.length) :
    finalVertexCellType
        (inputOfPresentation presentation.toPlanarPresentation)
        (.triple tripleIndex) =
      finalVertexCellTypeFromData
        (.inr (), some (incidenceColorTripleData
          (inputOfPresentation presentation.toPlanarPresentation)
          tripleIndex)) := by
  obtain ⟨fan⟩ := exists_contractVertexFan_at_triple
    presentation wellFormed degree tripleIndex indexLt
  let input := inputOfPresentation presentation.toPlanarPresentation
  let endpoints : EndpointTriple :=
    (fan.first, fan.second, fan.third)
  let actual := incidenceEndpointTripleData input endpoints
  let canonical := incidenceColorTripleData input tripleIndex
  have compressedEq :
      endpointTripleData (input, endpoints) = actual := by
    exact compilerEndpointTripleData_eq_incidenceTags
      presentation.toPlanarPresentation tripleIndex
      fan.first fan.second fan.third fan.endpoints_eq
  have dataAtEq :
      endpointTripleDataAt (input, .triple tripleIndex) =
        some actual := by
    unfold endpointTripleDataAt endpointTripleAt
    dsimp [input]
    simp only [inputOfPresentation]
    rw [fan.endpoints_eq]
    simpa [input, endpoints, inputOfPresentation] using
      congrArg some compressedEq
  have firstTag :=
    fan.first.incidenceTag_eq_of_vertex_triple
      tripleIndex fan.first_data.2
  have secondTag :=
    fan.second.incidenceTag_eq_of_vertex_triple
      tripleIndex fan.second_data.2
  have thirdTag :=
    fan.third.incidenceTag_eq_of_vertex_triple
      tripleIndex fan.third_data.2
  have colorsPerm :=
    contractedVertexFan_colors_perm_incidenceColors
      degree tripleIndex fan
  have dataPerm :
      List.Perm (endpointTripleDataList actual)
        (endpointTripleDataList canonical) := by
    have mapped := colorsPerm.map
      (incidenceSideColorAt input tripleIndex)
    simpa [actual, canonical, endpoints,
      endpointTripleDataList, incidenceEndpointTripleData,
      incidenceEndpointSideColor, incidenceColorTripleData,
      incidenceSideColorAt, incidenceColors,
      firstTag, secondTag, thirdTag] using mapped
  have sidesNodup :
      (endpointTripleDataList actual).map Prod.fst |>.Nodup := by
    rw [← compressedEq]
    dsimp [input, endpoints]
    simpa [endpointTripleDataList, endpointTripleData] using
      fan.sidesNodup
  have orderEq :
      trichromaticOrderFromData (some actual) =
        trichromaticOrderFromData (some canonical) :=
    trichromaticOrderFromData_eq_of_perm
      actual canonical dataPerm.symm sidesNodup
  have cellEq :
      finalVertexCellType input (.triple tripleIndex) =
        finalVertexCellTypeFromData (.inr (), some actual) := by
    simp only [finalVertexCellType, finalVertexCellTypeFromData]
    rw [← trichromaticOrderFromData_at
      (input, .triple tripleIndex)]
    rw [dataAtEq]
  simpa [input, canonical, finalVertexCellTypeFromData] using
    cellEq.trans
      (congrArg OrthogonalCellType.trichromaticVertex orderEq)

end NormalizationCompiler
end PeriodicThreeDM
end LeanTrominoes
