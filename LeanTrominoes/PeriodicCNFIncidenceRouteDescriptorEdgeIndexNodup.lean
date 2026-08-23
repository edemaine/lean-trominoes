/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFIncidenceRouteDescriptorEnumerationData

/-! # Duplicate-free stored indices of numeric route descriptors -/

namespace LeanTrominoes
namespace PeriodicCNF

open PeriodicOrthocrossing

/-- Stored edge indices of numeric incidence descriptors are duplicate-free. -/
theorem numericRouteDescriptor_edgeIndices_nodup
    {Variable : Type} [DecidableEq Variable]
    (formula : PeriodicCNF Variable) :
    ((numericRouteDescriptors formula).map
      RouteDescriptor.edgeIndex).Nodup := by
  unfold numericRouteDescriptors
  rw [List.map_map]
  change
    (formula.incidencesWithMetadata.zipIdx.map Prod.snd).Nodup
  exact List.nodup_zipIdx_map_snd formula.incidencesWithMetadata

end PeriodicCNF
end LeanTrominoes
