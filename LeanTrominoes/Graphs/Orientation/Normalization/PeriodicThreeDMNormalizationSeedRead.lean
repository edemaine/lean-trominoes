/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.Graphs.Orientation.NormalizedOrientationCNFSeedComputability
import LeanTrominoes.SAT.CNF.PeriodicCNFReflection
import LeanTrominoes.Graphs.Orientation.Normalization.PeriodicThreeDMNormalizationOrientationEquivalence
import LeanTrominoes.ThreeDM.PeriodicThreeDMCNF
import LeanTrominoes.Graphs.Orientation.Normalization.PeriodicThreeDMGraphOrientationEncodingCorrect

/-! # A signed one-port decoder for each normalized 3DM triple -/
noncomputable section
namespace LeanTrominoes.PeriodicThreeDM
open Gadget PeriodicCNF.SignedDecoder
namespace SeedNormalization
open Gadget.NormalizedOrientation
variable {problem : PeriodicThreeDM}

abbrev drawing (presentation : problem.PlanarPresentation) := presentation.normalizedOrthogonalDrawing

def selectedEndpoint (index : Nat) : ContractedEndpoint :=
  problem.contractedTripleEndpointForTag ⟨index,.red⟩

def read (presentation : problem.PlanarPresentation) (index : Nat) :
    PeriodicLiteral Gadget.NormalizedOrientation.AsCNF.Variable :=
  let endpoint := selectedEndpoint (problem := problem) index
  let location := presentation.endpointDrawingLocation endpoint (0,0)
  ⟨(Gadget.NormalizedOrientation.AsCNF.address (drawing presentation) location,(endpoint.finalNormalizedPort presentation).side),
    PeriodicCNF.Reflection.cell (Gadget.NormalizedOrientation.AsCNF.quotient (drawing presentation) location),false⟩

theorem endpoint_location_lift (presentation : problem.PlanarPresentation)
    (endpoint : ContractedEndpoint) (translate : Cell) :
    presentation.endpointDrawingLocation endpoint translate =
      Gadget.NormalizedOrientation.AsCNF.lift (drawing presentation)
        (presentation.endpointDrawingLocation endpoint (0,0)) (PeriodicCNF.Reflection.cell translate) := by
  have periods := presentation.normalizedOrthogonalDrawing_periods
  have hp : (drawing presentation).horizontalPeriod = presentation.finalNormalizationPeriod := periods.1
  have vp : (drawing presentation).verticalPeriod = presentation.finalNormalizationPeriod := periods.2
  simp only [Gadget.NormalizedOrientation.AsCNF.lift,hp,vp,PlanarPresentation.endpointDrawingLocation,
    PeriodicCNF.Reflection.cell,reflectedLocation,Cell.add,Cell.scale]
  ext <;> simp <;> ring

theorem read_decode (presentation : problem.PlanarPresentation)
    (a : Gadget.NormalizedOrientation.AsCNF.Variable → Cell → Bool) :
    decode (read presentation) a = fun index translate =>
      presentation.reverseGraphOrientation
        (Gadget.NormalizedOrientation.AsCNF.orientation (drawing presentation) (PeriodicCNF.Reflection.assignment a)) ⟨index,.red⟩ translate := by
  funext index translate
  simp only [PlanarPresentation.reverseGraphOrientation,PlanarPresentation.drawingEndpointInward,
    decode,read,selectedEndpoint,Bool.false_eq_true,ite_false]
  rw [endpoint_location_lift presentation _ translate]
  simp only [Gadget.NormalizedOrientation.AsCNF.orientation,
    Gadget.NormalizedOrientation.AsCNF.address_lift,Gadget.NormalizedOrientation.AsCNF.quotient_lift,
    PeriodicCNF.Reflection.assignment,PeriodicCNF.Reflection.cell_add,PeriodicCNF.Reflection.cell_cell]
  congr 2
  ext <;> simp [Cell.add,add_comm]

theorem forward_inverse (presentation : problem.ContinuousPlanarPresentation)
    (wellFormed : problem.IsWellFormed) (degree : problem.DegreeTwoOrThree)
    (collisionFree : presentation.toPlanarPresentation.FinalAssignmentsCollisionFree)
    (values : problem.GraphOrientation) (index : Nat) (bound : index < problem.triples.length)
    (translate : Cell) :
    presentation.toPlanarPresentation.reverseGraphOrientation
      (presentation.forwardDrawingOrientation values) ⟨index,.red⟩ translate = values ⟨index,.red⟩ translate := by
  let planar := presentation.toPlanarPresentation
  let endpoint := selectedEndpoint (problem := problem) index
  have tagMember := tripleIncidenceTag_mem_incidenceTags problem index bound .red
  have endpointMember := contractedTripleEndpoint_mem_contractedEndpoints problem
    (problem.contractedTripleEndpointForTag_mem wellFormed degree tagMember)
  have vertex : endpoint.vertex = .triple index :=
    contractedTripleEndpointForTag_vertex problem wellFormed degree tagMember
  have vertexMember : (.triple index : PeriodicThreeDMVertex) ∈ problem.contractedGraph.vertices :=
    (GraphOrientationEncoding.triple_mem problem index).2 bound
  have siteMember :
      (rasterLocation planar.finalNormalizationPeriod (planar.finalNormalizationPosition (.triple index)),
        FinalOrientationSite.vertex (.triple index)) ∈ planar.finalOrientationSites :=
    List.mem_append_left _ (List.mem_map.mpr ⟨_,vertexMember,rfl⟩)
  have value := presentation.forwardDrawingOrientation_periodOccurrence collisionFree values siteMember
    translate (endpoint.finalNormalizedPort planar).side
  change presentation.forwardDrawingOrientation values
      (reflectedLocation (Cell.add (planar.finalNormalizationPosition (.triple index))
        (Cell.scale (planar.finalNormalizationPeriod : Int) translate))) _ =
    planar.vertexPortInward values (.triple index) translate _ at value
  rw [← vertex] at value
  have portValue := PlanarPresentation.vertexPortInward_endpoint presentation wellFormed degree
    values (endpoint := endpoint) endpointMember translate
  change planar.vertexPortInward values endpoint.vertex translate
    (endpoint.finalNormalizedPort planar).side = endpoint.inwardAtVertexTranslate values translate at portValue
  rw [portValue] at value
  have inward := ContractedEndpoint.inwardAtVertexTranslate_eq_not_value_of_triple
    values endpoint index vertex translate
  change (!(presentation.forwardDrawingOrientation values (planar.endpointDrawingLocation endpoint translate)
    (endpoint.finalNormalizedPort planar).side) : Bool) = values ⟨index,.red⟩ translate
  rw [show planar.endpointDrawingLocation endpoint translate =
    reflectedLocation (Cell.add (planar.finalNormalizationPosition endpoint.vertex)
      (Cell.scale (planar.finalNormalizationPeriod : Int) translate)) from rfl,value]
  rw [inward]
  simp only [Bool.not_not]
  have color : endpoint.color = .red := by
    have same : endpoint.incidenceTag.color = endpoint.color := by
      cases endpoint with
      | source edge => cases edge <;> rfl
      | target edge => cases edge <;> rfl
    exact same.symm.trans (congrArg IncidenceTag.color
      (problem.contractedTripleEndpointForTag_incidenceTag wellFormed degree tagMember))
  rw [color]

end SeedNormalization
end LeanTrominoes.PeriodicThreeDM
