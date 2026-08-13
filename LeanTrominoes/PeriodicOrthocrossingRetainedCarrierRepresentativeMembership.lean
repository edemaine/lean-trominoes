/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingRetainedPlanarSATGaugedCarrierClauseOrbits

/-!
# Membership of retained carrier representatives

Every raw retained carrier link whose physical segment occurrence lies in the
neighboring source window has a selected zero-owner representative.  This is
the semantic counterpart of the representative geometry: it lets a periodic
assignment use the finite selected carrier formula to recover every equality
along a neighboring physical carrier chain.
-/

namespace LeanTrominoes
namespace PeriodicOrthocrossing

open PlanarThreeSAT

/-- Correcting a raw retained link to its zero owner puts the first endpoint
on a neighboring segment occurrence. -/
theorem
    carrierLinkRepresentativeCorrection_first_translate_neighbor
    {Vertex : Type*} [DecidableEq Vertex]
    {graph : PeriodicGraph Vertex}
    (wellFormed : graph.IsWellFormed)
    (degree : graph.DegreeAtMost 3)
    (isLocal : graph.IsLocal)
    {link : EqualityLink CarrierNode}
    (linkMem :
      link ∈ retainedDrawingCompleteCarrierLinksRaw graph) :
    let corrected :=
      carrierLinkPeriodTranslate graph link
        (carrierLinkRepresentativeCorrection graph link)
    IsNeighborTranslation corrected.first.translate := by
  let correction :=
    carrierLinkRepresentativeCorrection graph link
  let corrected :=
    carrierLinkPeriodTranslate graph link correction
  have rawEndpoints :=
    retainedDrawingCompleteCarrierLinkRaw_endpoints_mem graph linkMem
  have correctedEndpoints :=
    carrierLinkRepresentativeCorrection_endpoints_mem
      wellFormed degree isLocal linkMem
  have rawCommon :=
    retainedDrawingCompleteCarrierLinksRaw_common_key graph linkMem
  have correctedCommon :
      corrected.first.carrierKey =
        corrected.second.carrierKey :=
    carrierLinkPeriodTranslate_common_key
      graph link correction rawCommon
  cases firstEq : link.first with
  | boundary firstBoundary =>
      have firstBoundaryMem :
          firstBoundary ∈ retainedCrossingBoundaries graph := by
        rw [firstEq] at rawEndpoints
        unfold retainedDrawingCarrierNodes at rawEndpoints
        simpa using rawEndpoints.1
      have canonicalFirstMem :
          firstBoundary.periodNormalize graph ∈
            drawingCrossingBoundaries graph :=
        retainedCrossingBoundary_periodNormalize_mem
          graph firstBoundaryMem
      have correctedFirstEq :
          corrected.first =
            .boundary (firstBoundary.periodNormalize graph) :=
        carrierLinkRepresentativeCorrection_first_boundary
          graph firstEq
      change IsNeighborTranslation corrected.first.translate
      rw [correctedFirstEq]
      exact
        (drawingCrossingBoundary_indexed_mem_and_translate_neighbor
          graph canonicalFirstMem).2
  | terminal firstTerminal =>
      cases secondEq : link.second with
      | boundary secondBoundary =>
          have secondBoundaryMem :
              secondBoundary ∈ retainedCrossingBoundaries graph := by
            rw [secondEq] at rawEndpoints
            unfold retainedDrawingCarrierNodes at rawEndpoints
            simpa using rawEndpoints.2
          have canonicalSecondMem :
              secondBoundary.periodNormalize graph ∈
                drawingCrossingBoundaries graph :=
            retainedCrossingBoundary_periodNormalize_mem
              graph secondBoundaryMem
          have correctedSecondEq :
              corrected.second =
                .boundary
                  (secondBoundary.periodNormalize graph) :=
            carrierLinkRepresentativeCorrection_terminal_boundary
              graph firstEq secondEq
          have fields :=
            carrierNode_indexed_translate_eq_of_carrierKey_eq_of_indexed_mem
              graph
              (retainedCarrierNode_indexed_mem
                graph correctedEndpoints.1)
              (retainedCarrierNode_indexed_mem
                graph correctedEndpoints.2)
              correctedCommon
          change IsNeighborTranslation corrected.first.translate
          rw [fields.2, correctedSecondEq]
          exact
            (drawingCrossingBoundary_indexed_mem_and_translate_neighbor
              graph canonicalSecondMem).2
      | terminal secondTerminal =>
          have correctedFirstEq :
              corrected.first =
                .terminal
                  ⟨firstTerminal.indexed, (0, 0),
                    firstTerminal.endpoint⟩ :=
            carrierLinkRepresentativeCorrection_terminal_terminal
              graph firstEq secondEq
          change IsNeighborTranslation corrected.first.translate
          rw [correctedFirstEq]
          simp [CarrierNode.translate, IsNeighborTranslation]

/-- Every raw link on a neighboring physical carrier has a selected
zero-owner representative in its periodic orbit. -/
theorem
    retainedDrawingCompleteCarrierLink_representativeCorrection_mem
    {Vertex : Type*} [DecidableEq Vertex]
    {graph : PeriodicGraph Vertex}
    (wellFormed : graph.IsWellFormed)
    (degree : graph.DegreeAtMost 3)
    (isLocal : graph.IsLocal)
    {link : EqualityLink CarrierNode}
    (linkMem :
      link ∈ retainedDrawingCompleteCarrierLinksRaw graph)
    (sourceNeighbor :
      IsNeighborTranslation link.first.translate) :
    carrierLinkPeriodTranslate graph link
        (carrierLinkRepresentativeCorrection graph link) ∈
      retainedDrawingCompleteCarrierLinks graph := by
  apply
    (mem_retainedDrawingCompleteCarrierLinks_iff graph _).mpr
  constructor
  · exact
      retainedDrawingCompleteCarrierLinkRaw_periodTranslate_mem
        wellFormed degree isLocal linkMem
        (carrierLinkRepresentativeCorrection graph link)
        sourceNeighbor
        (carrierLinkRepresentativeCorrection_first_translate_neighbor
          wellFormed degree isLocal linkMem)
  · exact
      carrierLinkPeriodTranslate_correction_isRepresentative
        graph link

end PeriodicOrthocrossing
end LeanTrominoes
