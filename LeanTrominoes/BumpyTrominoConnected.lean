/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.PlusRefinement
import LeanTrominoes.PolyominoConnectivity

/-! # The fixed 15-omino is connected -/

namespace LeanTrominoes.PlusRefinement

private def predecessor (c : Cell) : Cell :=
  if c.2 ≠ 0 then (c.1, 0) else if c.1 > 0 then (c.1 - 1, 0) else (c.1 + 1, 0)

private def rank (c : Cell) : Nat := c.1.natAbs + c.2.natAbs

/-- An explicit spanning tree, certified by a strictly decreasing rank. -/
private theorem predecessor_certificate :
    ∀ c ∈ bumpy, c ≠ (0, 0) →
      predecessor c ∈ bumpy ∧ Cell.SideAdjacent c (predecessor c) ∧
        rank (predecessor c) < rank c := by decide

theorem bumpy_connected : Polyomino.IsConnected bumpy := by
  let root : {c // c ∈ bumpy} := ⟨(0, 0), origin_mem_bumpy⟩
  have reach (c : {c // c ∈ bumpy}) : bumpy.sideGraph.Reachable c root := by
    generalize hr : rank c.val = n
    induction n using Nat.strong_induction_on generalizing c with
    | h n ih =>
      by_cases hc : c.val = (0, 0)
      · have eq : c = root := Subtype.ext hc
        rw [eq]
      · obtain ⟨hp, ha, lt⟩ := predecessor_certificate c.val c.property hc
        let previous : {c // c ∈ bumpy} := ⟨predecessor c.val, hp⟩
        have edge : bumpy.sideGraph.Adj c previous := ha
        exact edge.reachable.trans (ih _ (hr ▸ lt) previous rfl)
  letI : Nonempty {c // c ∈ bumpy} := ⟨root⟩
  exact ⟨fun a b => (reach a).trans (reach b).symm⟩

end LeanTrominoes.PlusRefinement
