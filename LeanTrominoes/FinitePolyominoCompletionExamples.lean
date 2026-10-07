/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.FinitePolyominoCompletionCoRE
import Lean.Util.CollectAxioms

/-! # Finite seeds outside the inspected box

Both prescribed monominoes cover (5, 0), with distinct tile-kind tags.
The radius-zero search can pass, but radius five and plane completion fail.
This checks that the seed is retained even before its overlap is inspected.
-/

namespace LeanTrominoes.FinitePolyominoCompletion.Examples

private def first : Placement Bool := ⟨false, .identity, (5, 0)⟩
private def second : Placement Bool := ⟨true, .identity, (5, 0)⟩
private def origin : Placement Bool := ⟨false, .identity, (0, 0)⟩
private def input : Input := (([(0, 0)], [(0, 0)]), [first, second])

example : FiniteSearch input 0 := by
  let selected := (pool input 0).filter fun p =>
    decide (p = origin ∨ p = first ∨ p = second)
  refine ⟨selected, PlaneTilingSearch.filter_mem_subsets _ _, ?_⟩
  constructor <;> decide +kernel

example : ¬ FiniteSearch input 5 := by
  rintro ⟨selected, _, valid, retained⟩
  obtain ⟨p, _, _, unique⟩ := valid (5, 0) (by decide +kernel)
  have one := unique first (retained (by decide +kernel)) (by decide +kernel)
  have two := unique second (retained (by decide +kernel)) (by decide +kernel)
  exact (by decide +kernel : first ≠ second) (one.trans two.symm)

example : ¬ Completable input := by
  intro completed
  have disjoint := seed_cells_disjoint completed
    (by decide +kernel : first ∈ input.2) (by decide +kernel : second ∈ input.2)
    (by decide +kernel : first ≠ second)
  exact Finset.disjoint_left.mp disjoint
    (by decide +kernel : (5, 0) ∈ first.cells (PlaneTilingSearch.tiles input.1))
    (by decide +kernel : (5, 0) ∈ second.cells (PlaneTilingSearch.tiles input.1))

open Lean Elab Command in
run_cmd do
  for name in [``FinitePolyominoCompletion.completable_iff,
      ``FinitePolyominoCompletion.coRE, ``FinitePolyominoCompletion.fixedProblem_coRE] do
    let axioms ← Lean.collectAxioms name
    let extra := axioms.filter fun ax =>
      ax != ``propext && ax != ``Classical.choice && ax != ``Quot.sound
    unless extra.isEmpty do
      throwError "{name} depends on unexpected axioms: {extra}"

end LeanTrominoes.FinitePolyominoCompletion.Examples
