/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFIncidenceRouteDescriptorEnumerationData
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorPairCrossingData
import Mathlib.Data.List.Enum

/-! # Stored presentation indices of numeric CNF route descriptors -/

namespace LeanTrominoes
namespace PeriodicCNF

open PeriodicOrthocrossing

/-- The edge index stored in every numeric descriptor is exactly its position
in the descriptor stream. -/
theorem numericRouteDescriptors_selfIndexed
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable) :
    RouteDescriptorList.SelfIndexed
      (numericRouteDescriptors formula) := by
  rw [RouteDescriptorList.SelfIndexed, List.forall_mem_zipIdx']
  intro index indexLt
  simp only [numericRouteDescriptors, List.length_map,
    List.length_zipIdx] at indexLt ⊢
  simp [CNFIncidence.numericRouteDescriptor]

end PeriodicCNF
end LeanTrominoes
