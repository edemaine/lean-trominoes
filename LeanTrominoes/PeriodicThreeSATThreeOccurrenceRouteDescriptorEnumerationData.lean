/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFIncidenceMetadataSize
import LeanTrominoes.PeriodicThreeSATThreeOccurrenceRouteDescriptorData

/-! # Copied occurrence route-descriptor enumeration -/

namespace LeanTrominoes
namespace PeriodicThreeSATThree

/-- Explicit copied-source route records in exact global edge order. -/
def occurrenceRouteDescriptors
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable) :
    List PeriodicOrthocrossing.RouteDescriptor :=
  (PeriodicCNF.incidencesWithMetadata source).zipIdx.map fun tagged =>
    occurrenceRouteDescriptor source tagged.1 tagged.2

@[simp] theorem occurrenceRouteDescriptors_length
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable) :
    (occurrenceRouteDescriptors source).length =
      PeriodicCNF.presentationLiteralCount source := by
  simp [occurrenceRouteDescriptors]

end PeriodicThreeSATThree
end LeanTrominoes
