/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.CompletionPrefillSearch

/-! # Primitive-recursive checks for finite collections of preplacements -/

namespace LeanTrominoes.PeriodicTrominoPrefill
open Computability TrominoAssignment

set_option maxHeartbeats 2000000

theorem repeatOffset_primrec : Primrec₂ repeatOffset := by
  unfold repeatOffset
  exact cell_add_primrec.comp₂
    (cell_scale_primrec.comp₂ (Primrec.fst.comp₂ Primrec₂.right) (period₁_primrec.comp₂ Primrec₂.left))
    (cell_scale_primrec.comp₂ (Primrec.snd.comp₂ Primrec₂.right) (period₂_primrec.comp₂ Primrec₂.left))

theorem repeatedCells_primrec (t : Tromino) :
    Primrec₂ fun (input : PeriodicTrominoPrefill × Cell) (p : Placement Unit) =>
      repeatedCells t input.1 input.2 p := by
  unfold repeatedCells
  exact Primrec.list_map ((placementCells_primrec t).comp Primrec.snd)
    (cell_add_primrec.comp₂ (repeatOffset_primrec.comp₂
      ((Primrec.fst.comp Primrec.fst).comp₂ Primrec₂.left)
      ((Primrec.snd.comp Primrec.fst).comp₂ Primrec₂.left)) Primrec₂.right)

theorem boundedFootprints_primrec (t : Tromino) : Primrec₂ (boundedFootprints t) := by
  have atIndex : Primrec₂ fun (input : PeriodicTrominoPrefill × Nat) (index : Cell) =>
      input.1.motif.map (repeatedCells t input.1 index) := by
    exact Primrec.list_map (motif_primrec.comp (Primrec.fst.comp Primrec.fst))
      ((repeatedCells_primrec t).comp₂
        (Primrec₂.pair.comp₂ ((Primrec.fst.comp Primrec.fst).comp₂ Primrec₂.left)
          (Primrec.snd.comp₂ Primrec₂.left)) Primrec₂.right)
  exact Primrec.list_flatMap (boxCellList_primrec.comp Primrec.snd) atIndex

private theorem cell_mem_primrec : PrimrecRel fun (c : Cell) (xs : List Cell) => c ∈ xs :=
  (Primrec.eq.exists_mem_list.swap).of_eq fun _ _ => by simp

theorem compatible_primrec : PrimrecRel Compatible :=
  cell_mem_primrec.not.forall_mem_list.or
    (cell_mem_primrec.forall_mem_list.and cell_mem_primrec.forall_mem_list.swap)

theorem boundedValid_primrec (t : Tromino) : PrimrecPred fun input : PeriodicTrominoPrefill × Nat =>
    BoundedValid t input.1 input.2 := by
  exact compatible_primrec.swap.forall_mem_list.swap.forall_mem_list.comp
    (boundedFootprints_primrec t) (boundedFootprints_primrec t)

end LeanTrominoes.PeriodicTrominoPrefill
