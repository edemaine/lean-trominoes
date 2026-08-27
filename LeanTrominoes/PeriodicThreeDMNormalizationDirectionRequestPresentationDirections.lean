/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicThreeDMNormalizationDirectionRequestContractedDirections
import LeanTrominoes.PeriodicThreeDMNormalizationIncidenceEndpointDirections

/-! # Presentation-level incidence words for contracted requests -/

namespace LeanTrominoes
namespace PeriodicThreeDM
namespace NormalizationDirectionRequest

open Gadget NormalizationCompiler

/-- In any compatible presentation, a suppressed degree-two edge request is
exactly the first incidence word followed by the reversed second incidence
word.  The required length and common-boundary facts come from presentation
compatibility rather than becoming source-emitter inputs. -/
theorem PlanarPresentation.ofEdge_through_directions
    {problem : PeriodicThreeDM}
    (presentation : problem.PlanarPresentation)
    (color : WireColor) (atom : Nat) (first second : Incidence)
    (firstMember : first ∈ problem.incidences color atom)
    (secondMember : second ∈ problem.incidences color atom) :
    (ofEdge (inputOfPresentation presentation)
        (.through color atom first second)).directions =
      unitSubdivisionDirections
          (presentation.incidenceRoute
            ⟨first.tripleIndex, color⟩) ++
        unitSubdivisionDirections
          (presentation.incidenceRoute
            ⟨second.tripleIndex, color⟩).reverse := by
  have firstTagMember :
      ⟨first.tripleIndex, color⟩ ∈ problem.incidenceTags :=
    incidenceTag_mem_of_incidence_mem
      problem color atom firstMember
  apply NormalizationDirectionRequest.ofEdge_through_directions
  · simpa [inputOfPresentation, incidenceRoute,
      PlanarPresentation.incidenceRoute] using
      presentation.incidenceRoute_length_ge_two firstTagMember
  · simpa [inputOfPresentation, incidenceRoute,
      reversedIncidenceRouteAt,
      PlanarPresentation.incidenceRoute,
      PlanarPresentation.reversedIncidenceRouteAt] using
      presentation.throughIncidenceRoutes_boundary
        color atom firstMember secondMember

end NormalizationDirectionRequest
end PeriodicThreeDM
end LeanTrominoes
