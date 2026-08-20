/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicThreeDMNormalizationTripleIncidenceData
import LeanTrominoes.PeriodicThreeDMNormalizationCellTypeComputability

/-! # Triple cell types from original incidence directions -/

noncomputable section

namespace LeanTrominoes

namespace PeriodicThreeDM
namespace NormalizationCompiler

/-- For every genuine triple, the final trichromatic cell type can be
computed from three original-incidence first directions; no contracted route
needs to be constructed or scanned. -/
theorem exists_finalVertexCellType_eq_incidenceTags
    {problem : PeriodicThreeDM}
    (presentation : problem.PlanarPresentation)
    (wellFormed : problem.IsWellFormed)
    (degree : problem.DegreeTwoOrThree)
    (tripleIndex : Nat)
    (indexLt : tripleIndex < problem.triples.length) :
    ∃ endpoints : EndpointTriple,
      finalVertexCellType (inputOfPresentation presentation)
          (.triple tripleIndex) =
        finalVertexCellTypeFromData
          (.inr (), some (incidenceEndpointTripleData
            (inputOfPresentation presentation) endpoints)) := by
  rcases exists_endpointTripleDataAt_eq_incidenceTags
      presentation wellFormed degree tripleIndex indexLt with
    ⟨endpoints, dataEq⟩
  refine ⟨endpoints, ?_⟩
  simp only [finalVertexCellType, finalVertexCellTypeFromData]
  rw [← trichromaticOrderFromData_at
    (inputOfPresentation presentation, .triple tripleIndex)]
  rw [dataEq]

end NormalizationCompiler
end PeriodicThreeDM
end LeanTrominoes
