/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PlanarThreeSATOcurrences

/-! # Endpoint occurrences in equality-link families -/

namespace LeanTrominoes.PlanarThreeSAT

/-- The first endpoint of every listed equality link occurs in its two-clause
encoding. -/
theorem EqualityLink.first_mem_embeddedVariableOccurrences_equalityFamily
    {Variable : Type*} {links : List (EqualityLink Variable)}
    {link : EqualityLink Variable} (linkMem : link ∈ links) :
    link.first ∈ embeddedVariableOccurrences (equalityFamily links) := by
  unfold equalityFamily
  rw [embeddedVariableOccurrences_flatMap]
  apply List.mem_flatMap.mpr
  refine ⟨link, linkMem, ?_⟩
  simp [embeddedVariableOccurrences, equalityInstance]

/-- The second endpoint of every listed equality link occurs in its two-clause
encoding. -/
theorem EqualityLink.second_mem_embeddedVariableOccurrences_equalityFamily
    {Variable : Type*} {links : List (EqualityLink Variable)}
    {link : EqualityLink Variable} (linkMem : link ∈ links) :
    link.second ∈ embeddedVariableOccurrences (equalityFamily links) := by
  unfold equalityFamily
  rw [embeddedVariableOccurrences_flatMap]
  apply List.mem_flatMap.mpr
  refine ⟨link, linkMem, ?_⟩
  simp [embeddedVariableOccurrences, equalityInstance]

end LeanTrominoes.PlanarThreeSAT
