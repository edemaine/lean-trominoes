/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.CompletionPeriodicCertificate

/-! # Enumerable finite certificates for periodic completion -/
namespace LeanTrominoes.CompletionPeriodic
open Computability PeriodicTrominoPrefill TrominoAssignment
set_option maxHeartbeats 2000000

private theorem all_primrec {α β : Type} [Primcodable α] [Primcodable β]
    {xs : α → List β} {p : α → β → Prop} (hx : Primrec xs) (hp : PrimrecRel p) :
    PrimrecPred fun a => ∀ b ∈ xs a, p a b :=
  hp.swap.forall_mem_list.comp hx Primrec.id

private theorem mem_primrec : PrimrecRel fun (c : Cell) (xs : List Cell) => c ∈ xs :=
  (Primrec.eq.exists_mem_list.swap).of_eq fun _ _ => by simp

private theorem sameCells_primrec : PrimrecRel SameCells :=
  mem_primrec.forall_mem_list.and mem_primrec.forall_mem_list.swap

private theorem mod_primrec : Primrec₂ fun (x : Int) (n : Nat) => x % (n:Int) := by
  exact (int_subtract_primrec.comp₂ Primrec₂.left
    (int_multiply_primrec.comp₂ (int_ofNat_primrec.comp₂ Primrec₂.right) int_edivNat_primrec)).of_eq
    (fun x n => (Int.emod_def x n).symm)

theorem key_primrec : Primrec₂ key := by
  unfold key residue
  exact Primrec.nat_add.comp₂
    (Primrec.nat_mul.comp₂
      (int_toNat_primrec.comp₂ (mod_primrec.comp₂ (Primrec.fst.comp₂ Primrec₂.right) Primrec₂.left)) Primrec₂.left)
    (int_toNat_primrec.comp₂ (mod_primrec.comp₂ (Primrec.snd.comp₂ Primrec₂.right) Primrec₂.left))

theorem entry_primrec : Primrec₂ entry :=
  (Primrec.list_getD (⟨(),.identity,(0,0)⟩ : Placement Unit)).comp₂ (Primrec.snd.comp₂ Primrec₂.left)
    (key_primrec.comp₂ (Primrec.fst.comp₂ Primrec₂.left) Primrec₂.right)

theorem tileList_primrec (t : Tromino) : Primrec₂ (tileList t) := by
  unfold tileList
  exact Primrec.list_map ((placementCells_primrec t).comp entry_primrec)
    (cell_add_primrec.comp₂ (Primrec.snd.comp₂ Primrec₂.left) Primrec₂.right)

private theorem local_primrec (t : Tromino) : PrimrecPred fun q : Certificate × Cell =>
    q.2 ∈ tileList t q.1 q.2 ∧ ∀ d ∈ tileList t q.1 q.2,
      SameCells (tileList t q.1 d) (tileList t q.1 q.2) := by
  apply (mem_primrec.comp Primrec.snd (tileList_primrec t)).and
  apply all_primrec (tileList_primrec t)
  exact sameCells_primrec.comp
    ((tileList_primrec t).comp (Primrec.fst.comp Primrec.fst) Primrec.snd)
    ((tileList_primrec t).comp (Primrec.fst.comp Primrec.fst) (Primrec.snd.comp Primrec.fst))

private theorem retained_primrec (t : Tromino) :
    PrimrecRel fun q : (PeriodicTrominoPrefill × Certificate) × Cell => fun p : Placement Unit =>
      SameCells (repeatedCells t q.1.1 q.2 p)
        (tileList t q.1.2 (Cell.add (repeatOffset q.1.1 q.2) p.offset)) := by
  let ci : ((PeriodicTrominoPrefill × Certificate) × Cell) × Placement Unit → PeriodicTrominoPrefill := fun q => q.1.1.1
  have hi : Primrec ci := Primrec.fst.comp (Primrec.fst.comp Primrec.fst)
  have hw : Primrec fun q : ((PeriodicTrominoPrefill × Certificate) × Cell) × Placement Unit => q.1.1.2 :=
    Primrec.snd.comp (Primrec.fst.comp Primrec.fst)
  have hk : Primrec fun q : ((PeriodicTrominoPrefill × Certificate) × Cell) × Placement Unit => q.1.2 :=
    Primrec.snd.comp Primrec.fst
  exact sameCells_primrec.comp
    ((repeatedCells_primrec t).comp (hi.pair hk) Primrec.snd)
    ((tileList_primrec t).comp hw (cell_add_primrec.comp
      (repeatOffset_primrec.comp hi hk) (placement_offset_primrec.comp Primrec.snd)))

theorem check_primrec (t : Tromino) : PrimrecPred fun q : PeriodicTrominoPrefill × Certificate => Check t q.1 q.2 := by
  apply (Primrec.nat_lt.comp (Primrec.const 0) (Primrec.fst.comp Primrec.snd)).and
  apply PrimrecPred.and
  · exact (all_primrec (boxCellList_primrec.comp Primrec.fst) (p := fun w c => c ∈ tileList t w c ∧ ∀ d ∈ tileList t w c, SameCells (tileList t w d) (tileList t w c)) (local_primrec t)).comp Primrec.snd
  · apply all_primrec (boxCellList_primrec.comp (Primrec.fst.comp Primrec.snd))
    exact all_primrec (motif_primrec.comp (Primrec.fst.comp Primrec.fst)) (retained_primrec t)

/-- Including the input's full-rank requirement keeps the certificate language
inside the original plane-completion problem. -/
def Certified (t : Tromino) (input : PeriodicTrominoPrefill) : Prop :=
  (input.occupiedRegion t).IsFullRank ∧ ∃ w, Check t input w

theorem certified_re (t : Tromino) : REPred (Certified t) := by
  let decode : Nat → Certificate := fun n => (Encodable.decode (α := Certificate) n).getD (0,[])
  have hd : Primrec decode := Primrec.option_getD.comp Primrec.decode (Primrec.const (0,[]))
  have hp : PrimrecPred fun q : PeriodicTrominoPrefill × Nat =>
      (q.1.occupiedRegion t).IsFullRank ∧ Check t q.1 (decode q.2) :=
    (periodicRegion_isFullRank_primrec.comp ((occupiedRegion_primrec t).comp Primrec.fst)).and
      ((check_primrec t).comp (Primrec.fst.pair (hd.comp Primrec.snd)))
  apply (LeanWang.REPred.exists_nat (p := fun input n => (input.occupiedRegion t).IsFullRank ∧ Check t input (decode n)) hp.computablePred).of_eq
  intro input
  constructor
  · rintro ⟨n,rank,checked⟩; exact ⟨rank,decode n,checked⟩
  · rintro ⟨rank,w,checked⟩
    refine ⟨Encodable.encode w,rank,?_⟩
    simpa only [decode,Encodable.encodek,Option.getD_some] using checked
end LeanTrominoes.CompletionPeriodic
