/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.PolyominoConnectivitySearch
import LeanTrominoes.PlaneTilingSearchComputability

/-! # Computability of finite polyomino cut certificates -/

namespace LeanTrominoes.PolyominoConnectivitySearch

open Computability

theorem mem_list_primrec : PrimrecRel (fun (c : Cell) (xs : List Cell) => c ∈ xs) := by
  apply (Primrec.eq.exists_mem_list.comp₂ Primrec₂.right Primrec₂.left).of_eq
  intro c xs
  simp

theorem adjacent_primrec : PrimrecRel Cell.SideAdjacent := by
  have ax : Primrec (fun a : Cell × Cell => a.1.1) := Primrec.fst.comp Primrec.fst
  have ay : Primrec (fun a : Cell × Cell => a.1.2) := Primrec.snd.comp Primrec.fst
  have bx : Primrec (fun a : Cell × Cell => a.2.1) := Primrec.fst.comp Primrec.snd
  have byPR : Primrec (fun a : Cell × Cell => a.2.2) := Primrec.snd.comp Primrec.snd
  exact ((Primrec.eq.comp ax bx).and
    ((Primrec.eq.comp (int_add_primrec.comp ay (Primrec.const 1)) byPR).or
      (Primrec.eq.comp (int_add_primrec.comp byPR (Primrec.const 1)) ay))).or
    ((Primrec.eq.comp ay byPR).and
      ((Primrec.eq.comp (int_add_primrec.comp ax (Primrec.const 1)) bx).or
        (Primrec.eq.comp (int_add_primrec.comp bx (Primrec.const 1)) ax)))

theorem cut_primrec : PrimrecRel Cut := by
  have inside : PrimrecRel (fun (c : Cell) (a : List Cell × List Cell) => c ∈ a.2) :=
    mem_list_primrec.comp₂ Primrec₂.left (Primrec.snd.comp₂ Primrec₂.right)
  have row : PrimrecRel (fun (b : Cell) (a : (List Cell × List Cell) × Cell) =>
      Cell.SideAdjacent a.2 b → b ∈ a.1.2) := by
    apply ((adjacent_primrec.comp₂ (Primrec.snd.comp₂ Primrec₂.right) Primrec₂.left).not.or
      (mem_list_primrec.comp₂ Primrec₂.left
        (Primrec.snd.comp₂ (Primrec.fst.comp₂ Primrec₂.right)))).of_eq
    intro a
    tauto
  have rows : PrimrecRel (fun (c : Cell) (a : List Cell × List Cell) =>
      ∀ b ∈ a.1, Cell.SideAdjacent c b → b ∈ a.2) :=
    row.forall_mem_list.comp (Primrec.fst.comp Primrec.snd) (Primrec.pair Primrec.snd Primrec.fst)
  exact (inside.exists_mem_list.comp Primrec.fst Primrec.id).and
    ((inside.not.exists_mem_list.comp Primrec.fst Primrec.id).and
      (rows.forall_mem_list.comp Primrec.snd Primrec.id))

theorem disconnected_primrec : PrimrecPred Disconnected :=
  cut_primrec.swap.exists_mem_list.comp PlaneTilingSearch.subsets_primrec Primrec.id

end LeanTrominoes.PolyominoConnectivitySearch
