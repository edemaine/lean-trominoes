/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.PeriodicCNFDimensions
import Lean.Util.CollectAxioms

/-! # Higher-dimensional locality boundary checks

Locality uses every coordinate and allows arbitrary common offsets.
-/

namespace LeanTrominoes.PeriodicCNFDimensions.Examples

private def shifted : Lattice 3 := ![100, -200, 300]
private def neighbor : Lattice 3 := ![100, -200, 301]
private def diagonal : Lattice 3 := ![101, -200, 301]

example : IsLocal ([[((0, shifted), true), ((1, neighbor), false)]] : Formula 3) := by
  decide +kernel

example : ¬ IsLocal ([[((0, shifted), true), ((1, diagonal), false)]] : Formula 3) := by
  decide +kernel

example : PeriodicConstraints.Satisfiable (Lattice 3)
    ([[((0, shifted), true)]] : Formula 3) := by
  refine ⟨fun _ _ => true, ?_⟩
  simp [PeriodicConstraints.Holds]

example : ¬ PeriodicConstraints.Satisfiable (Lattice 3)
    ([[((0, shifted), true)], [((0, shifted), false)]] : Formula 3) := by
  rintro ⟨a, satisfied⟩
  have positive := satisfied 0 [((0, shifted), true)] (by simp)
  have negative := satisfied 0 [((0, shifted), false)] (by simp)
  simp only [List.mem_singleton, exists_eq_left, zero_add] at positive negative
  exact Bool.noConfusion (positive.symm.trans negative)

open Lean Elab Command in
run_cmd do
  for name in [``PeriodicCNFDimensions.liftPlane_satisfiable_iff,
      ``PeriodicCNFDimensions.liftPlane_local_iff,
      ``PeriodicCNFDimensions.satisfiable_coREComplete,
      ``PeriodicCNFDimensions.localProblem_coREComplete] do
    let axioms ← Lean.collectAxioms name
    let extra := axioms.filter fun ax =>
      ax != ``propext && ax != ``Classical.choice && ax != ``Quot.sound
    unless extra.isEmpty do
      throwError "{name} depends on unexpected axioms: {extra}"

end LeanTrominoes.PeriodicCNFDimensions.Examples
