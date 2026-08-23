/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFIncidenceRouteDescriptorEdgeIndexNodup
import LeanTrominoes.PeriodicThreeSATThreeSplitRouteDescriptorEnumerationSemantics

/-! # Duplicate-free explicit split route descriptors -/

namespace LeanTrominoes
namespace PeriodicThreeSATThree

open PeriodicOrthocrossing

/-- Stored global edge indices in the explicit occurrence-plus-cycle
descriptor stream are duplicate-free. -/
theorem splitRouteDescriptors_edgeIndices_nodup
    {Variable : Type} [DecidableEq Variable]
    (source : PeriodicCNF Variable) :
    ((splitRouteDescriptors source).map
      RouteDescriptor.edgeIndex).Nodup := by
  rw [← numericRouteDescriptors_formula_eq_splitRouteDescriptors source]
  exact PeriodicCNF.numericRouteDescriptor_edgeIndices_nodup (formula source)

/-- In particular, the explicit split descriptor stream itself has no
duplicates. -/
theorem splitRouteDescriptors_nodup
    {Variable : Type} [DecidableEq Variable]
    (source : PeriodicCNF Variable) :
    (splitRouteDescriptors source).Nodup :=
  (splitRouteDescriptors_edgeIndices_nodup source).of_map
    RouteDescriptor.edgeIndex

end PeriodicThreeSATThree
end LeanTrominoes
