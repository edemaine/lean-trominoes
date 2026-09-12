/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.Theorem55Compiler
import LeanTrominoes.Computability

/-! # Computability of the explicit two-polyomino reduction -/

namespace LeanTrominoes

open Computability

theorem Computability.int_emodNat_primrec :
    Primrec₂ (fun z : Int => fun n : Nat => z % (n : Int)) := by
  apply (int_subtract_primrec.comp₂ Primrec₂.left
    (int_multiply_primrec.comp₂ (int_ofNat_primrec.comp₂ Primrec₂.right)
      int_edivNat_primrec)).of_eq
  intro z n
  change z - (n : Int) * (z / (n : Int)) = z % (n : Int)
  have := Int.emod_add_mul_ediv z n
  omega

theorem Computability.constant_polyomino_membership_primrec (shape : Polyomino) :
    PrimrecPred (fun c : Cell => c ∈ shape) := by
  classical
  exact (Primrec.eq.exists_mem_list.comp (Primrec.const shape.toList) Primrec.id).of_eq
    (fun c => by simp)

namespace Theorem55Compiler

theorem padding_membership_primrec :
    PrimrecRel (fun (n : Nat) (c : Cell) => c ∈ PeriodicTrominoPadding.region n) := by
  have x : Primrec (fun a : Nat × Cell => a.2.1 % (a.1 : Int)) :=
    int_emodNat_primrec.comp (Primrec.fst.comp Primrec.snd) Primrec.fst
  have y : Primrec (fun a : Nat × Cell => a.2.2 % (a.1 : Int)) :=
    int_emodNat_primrec.comp (Primrec.snd.comp Primrec.snd) Primrec.fst
  exact (((Primrec.eq.comp x (Primrec.const 14)).or
    (Primrec.eq.comp x (Primrec.const 15))).and
      ((int_le_primrec.comp (Primrec.const 4) y).and
        (int_le_primrec.comp y (Primrec.const 6)))).primrecRel

theorem preparedContains_primrec : Primrec₂ preparedContains := by
  have source : Primrec (fun a : Input × Cell =>
      a.1.2.validContains (Cell.add (54, 18) a.2)) :=
    periodicRegion_validContains_primrec.comp (Primrec.snd.comp Primrec.fst)
      (cell_add_primrec.comp (Primrec.const (54, 18)) Primrec.snd)
  have padding : Primrec (fun a : Input × Cell =>
      decide (a.2 ∈ PeriodicTrominoPadding.region a.1.1)) :=
    padding_membership_primrec.decide.comp (Primrec.fst.comp Primrec.fst) Primrec.snd
  exact Primrec.cond source (Primrec.const true) padding

theorem parent_primrec : Primrec PlusRefinement.parent := by
  exact Primrec.pair
    (int_edivNat_primrec.comp (int_add_primrec.comp Primrec.fst (Primrec.const 1)) (Primrec.const 3))
    (int_edivNat_primrec.comp (int_add_primrec.comp Primrec.snd (Primrec.const 1)) (Primrec.const 3))

theorem subcell_primrec : Primrec PlusRefinement.subcell :=
  cell_sub_primrec.comp Primrec.id (cell_scale_primrec.comp (Primrec.const 3) parent_primrec)

theorem refinedContains_primrec : Primrec₂ refinedContains := by
  have source : Primrec (fun a : Input × Cell => preparedContains a.1 (PlusRefinement.parent a.2)) :=
    preparedContains_primrec.comp Primrec.fst (parent_primrec.comp Primrec.snd)
  have cross : Primrec (fun a : Input × Cell =>
      decide (PlusRefinement.subcell a.2 ∈ PlusRefinement.cross)) :=
    (constant_polyomino_membership_primrec PlusRefinement.cross).decide.comp
      (subcell_primrec.comp Primrec.snd)
  exact Primrec.and.comp source cross

theorem squareList_primrec : Primrec squareList := by
  have rows : Primrec₂ (fun (n : Nat) (x : Nat) =>
      (List.range n).map (fun y : Nat => ((x : Int), (y : Int)))) := by
    change Primrec (fun a : Nat × Nat =>
      (List.range a.1).map (fun y : Nat => ((a.2 : Int), (y : Int))))
    apply Primrec.list_map (Primrec.list_range.comp Primrec.fst)
    change Primrec (fun a : (Nat × Nat) × Nat => ((a.1.2 : Int), (a.2 : Int)))
    exact Primrec.pair (int_ofNat_primrec.comp (Primrec.snd.comp Primrec.fst))
      (int_ofNat_primrec.comp Primrec.snd)
  apply (Primrec.list_flatMap Primrec.list_range rows).of_eq
  intro n
  simp [squareList, List.product, List.map_flatMap, List.map_map, Function.comp_def]

theorem horizontal_lock_membership_primrec :
    PrimrecRel (fun (n : Nat) (c : Cell) => c ∈ KeyedPeriodicComplement.horizontalLock n) := by
  let shifted : Nat × Cell → Cell := fun a => Cell.sub a.2 ((a.1 : Int), 0)
  have shiftedPR : Primrec shifted := cell_sub_primrec.comp Primrec.snd
    (Primrec.pair (int_ofNat_primrec.comp Primrec.fst) (Primrec.const 0))
  have finitePR := constant_polyomino_membership_primrec
    ({(-4, 2), (-4, 3), (-3, 3), (-2, 3), (-1, 3)} : Polyomino)
  apply ((finitePR.comp shiftedPR).primrecRel).of_eq
  intro n c
  simp only [shifted, KeyedPeriodicComplement.horizontalLock, Finset.mem_insert,
    Finset.mem_singleton, Prod.ext_iff, Cell.sub]
  omega

theorem repack_primrec : Primrec₂ KeyedPeriodicComplement.repack := by
  have vertical : PrimrecPred (fun a : Nat × Cell => a.2 ∈ KeyedPeriodicComplement.verticalLock) :=
    (constant_polyomino_membership_primrec _).comp Primrec.snd
  exact Primrec.ite vertical
    (cell_add_primrec.comp Primrec.snd
      (Primrec.pair (Primrec.const 0) (int_ofNat_primrec.comp Primrec.fst)))
    (Primrec.ite horizontal_lock_membership_primrec
      (cell_add_primrec.comp Primrec.snd
        (Primrec.pair (int_negate_primrec.comp (int_ofNat_primrec.comp Primrec.fst)) (Primrec.const 0)))
      Primrec.snd)

theorem compile_primrec : Primrec compile := by
  have size : Primrec (fun a : Input => 3 * a.1) :=
    Primrec.nat_mul.comp (Primrec.const 3) Primrec.fst
  have keep : PrimrecRel (fun (c : Cell) (a : Input) => (!refinedContains a c) = true) := by
    apply (Primrec.eq.comp₂ refinedContains_primrec.swap (Primrec₂.const true)).not.of_eq
    intro c a
    change (¬ refinedContains a c = true) ↔ (!refinedContains a c) = true
    cases refinedContains a c <;> decide
  have filtered : Primrec (fun a : Input => (squareList (3 * a.1)).filter
      (fun c => !refinedContains a c)) := by
    apply (keep.listFilter.comp (squareList_primrec.comp size) Primrec.id).of_eq
    intro a
    simp only [Bool.decide_coe, id_eq]
  exact Primrec.list_map filtered (repack_primrec.comp₂ (size.comp₂ Primrec₂.left) Primrec₂.right)

end Theorem55Compiler
end LeanTrominoes
