/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.Graphs.Orientation.Normalization.PeriodicThreeDMNormalizationBoundedSeedFactor
import LeanTrominoes.Tiling.Tromino.Gadgets.GadgetITrichromaticPins

/-! # Matching-bit prescriptions occur at trichromatic drawing vertices -/
noncomputable section
namespace LeanTrominoes.PeriodicThreeDM.SeedNormalization
open Gadget DegreeThreeVertexNormalization
variable {problem : PeriodicThreeDM}

def vertexOrder (presentation : problem.PlanarPresentation) (index : Nat) : TrichromaticOrder :=
  trichromaticOrder (canonicalColoringAt presentation (.triple index))

theorem vertex_type (presentation : problem.ContinuousPlanarPresentation)
    (degree : problem.DegreeTwoOrThree)
    (collisionFree : presentation.toPlanarPresentation.FinalAssignmentsCollisionFree)
    (index : Nat) (bound : index < problem.triples.length) (translate : Cell) :
    (drawing presentation.toPlanarPresentation).getAt
      (presentation.toPlanarPresentation.endpointDrawingLocation
        (selectedEndpoint (problem := problem) index) translate) =
      .trichromaticVertex (vertexOrder presentation.toPlanarPresentation index) := by
  let planar := presentation.toPlanarPresentation
  have vertex : (selectedEndpoint (problem := problem) index).vertex = .triple index :=
    contractedTripleEndpointForTag_vertex problem presentation.problemWellFormed degree
      (tripleIncidenceTag_mem_incidenceTags problem index bound .red)
  have siteMember := planar.finalOrientationSite_vertex_mem
    ((GraphOrientationEncoding.triple_mem problem index).2 bound)
  have lookup := planar.finalOrientationSiteAt_reflected_periodOccurrence collisionFree siteMember
    (translate := translate)
  have cellType := planar.normalizedOrthogonalDrawing_getAt_eq_of_site_lookup collisionFree lookup
  simpa only [drawing,PlanarPresentation.endpointDrawingLocation,vertex,
    FinalOrientationSite.cellType,FinalOrientationSite.point,PlanarPresentation.finalVertexCellType,
    vertexOrder] using cellType

theorem trichromaticPattern_port_readout (order : TrichromaticOrder) (bit : Bool)
    (port : CanonicalVertexPort) :
    iConfigurationInward (.trichromaticVertex order)
      (portConfiguration .I (orthogonalCellGadget .I (.trichromaticVertex order))
        (CanonicalISelection.trichromaticPattern order bit)) port.side = bit := by
  rw [CanonicalISelection.trichromaticPattern,CanonicalISelection.pattern_ports]
  have active : ((OrthogonalCellType.trichromaticVertex order).portColor port.side).isSome := by
    cases order <;> cases port <;> rfl
  simpa only [PreferredISelection.profile,if_pos active] using
    (PreferredISelection.pattern_spec (.trichromaticVertex order) (fun _ => bit) ⟨rfl,rfl⟩).2.2 port.side active

end LeanTrominoes.PeriodicThreeDM.SeedNormalization
