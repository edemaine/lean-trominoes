/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.CompletionStripRawGeometry
import LeanTrominoes.CompletionStripValidity

/-! # Finite natural-arithmetic form of the strip prefill validity test -/
namespace LeanTrominoes.PeriodicStripTrominoPrefill.Raw

def point (t : Tromino) (p : Placement Unit) (k : Fin 3) : Cell :=
  Cell.add p.offset (p.symmetry.act (sourceCell t k))

theorem mem_cells_iff_point (t : Tromino) (p : Placement Unit) (c : Cell) :
    c ∈ p.cells (fun _ => t.cells) ↔ ∃ k : Fin 3, point t p k = c := by
  simp only [Placement.mem_cells_iff,cells_eq_source,Finset.mem_image,Finset.mem_univ,true_and]
  constructor
  · rintro ⟨d,⟨k,rfl⟩,eq⟩
    exact ⟨k,eq⟩
  · rintro ⟨k,eq⟩
    exact ⟨sourceCell t k,⟨k,rfl⟩,eq⟩

theorem forall_cells_iff (t : Tromino) (p : Placement Unit) (P : Cell → Prop) :
    (∀ c ∈ p.cells (fun _ => t.cells), P c) ↔ ∀ k : Fin 3, P (point t p k) := by
  simp only [mem_cells_iff_point]
  constructor
  · intro h k
    exact h _ ⟨k,rfl⟩
  · rintro h c ⟨k,rfl⟩
    exact h k

theorem mod_eq_iff (a b period : Nat) :
    a % period = b % period ↔ (period : Int) ∣ (a : Int) - b := by
  rw [Int.dvd_iff_emod_eq_zero,← Int.emod_eq_emod_iff_emod_sub_eq_zero]
  exact Int.ofNat_inj.symm

def SamePlace (t : Tromino) (input : PeriodicStripTrominoPrefill)
    (p q : Placement Unit) (a b : Fin 3) : Prop :=
  (biasedCell t (bound input) p a).2 = (biasedCell t (bound input) q b).2 ∧
    (biasedCell t (bound input) p a).1 % input.period = (biasedCell t (bound input) q b).1 % input.period

def Aligned (t : Tromino) (input : PeriodicStripTrominoPrefill)
    (p q : Placement Unit) (a b c d : Fin 3) : Prop :=
  (biasedCell t (bound input) p c).1 + (biasedCell t (bound input) q b).1 =
    (biasedCell t (bound input) q d).1 + (biasedCell t (bound input) p a).1 ∧
  (biasedCell t (bound input) p c).2 + (biasedCell t (bound input) q b).2 =
    (biasedCell t (bound input) q d).2 + (biasedCell t (bound input) p a).2

theorem samePlace_iff (t : Tromino) (input : PeriodicStripTrominoPrefill)
    (p q : Placement Unit) (hp : p ∈ input.motif) (hq : q ∈ input.motif) (a b : Fin 3) :
    SamePlace t input p q a b ↔ (point t p a).2 = (point t q b).2 ∧
      (input.period : Int) ∣ (point t p a).1 - (point t q b).1 := by
  have ha := biasedCell_eq t input p hp a
  have hb := biasedCell_eq t input q hq b
  change ((biasedCell t (bound input) p a).1 : Int) = (bound input : Int)+(point t p a).1 ∧
    ((biasedCell t (bound input) p a).2 : Int) = (bound input : Int)+(point t p a).2 at ha
  change ((biasedCell t (bound input) q b).1 : Int) = (bound input : Int)+(point t q b).1 ∧
    ((biasedCell t (bound input) q b).2 : Int) = (bound input : Int)+(point t q b).2 at hb
  rw [SamePlace,mod_eq_iff,ha.1,hb.1]
  have diff : ((bound input : Int)+(point t p a).1) - ((bound input : Int)+(point t q b).1) =
      (point t p a).1-(point t q b).1 := by ring
  rw [diff]
  exact and_congr (by omega) Iff.rfl

theorem aligned_iff (t : Tromino) (input : PeriodicStripTrominoPrefill)
    (p q : Placement Unit) (hp : p ∈ input.motif) (hq : q ∈ input.motif) (a b c d : Fin 3) :
    Aligned t input p q a b c d ↔
      point t p c = Cell.add (Cell.sub (point t p a) (point t q b)) (point t q d) := by
  have ha := biasedCell_eq t input p hp a
  have hb := biasedCell_eq t input q hq b
  have hc := biasedCell_eq t input p hp c
  have hd := biasedCell_eq t input q hq d
  simp only [Aligned,point,Cell.add,Cell.sub,Prod.mk.injEq]
  omega

theorem footprints_aligned_iff (t : Tromino) (input : PeriodicStripTrominoPrefill)
    (p q : Placement Unit) (hp : p ∈ input.motif) (hq : q ∈ input.motif) (a b : Fin 3) :
    p.cells (fun _ => t.cells) = (q.cells (fun _ => t.cells)).image (Cell.add (Cell.sub (point t p a) (point t q b))) ↔
      (∀ c, ∃ d, Aligned t input p q a b c d) ∧ (∀ d, ∃ c, Aligned t input p q a b c d) := by
  simp only [aligned_iff t input p q hp hq]
  constructor
  · intro eq
    constructor
    · intro c
      have member := (mem_cells_iff_point t p _).mpr ⟨c,rfl⟩
      rw [eq] at member
      obtain ⟨e,he,heq⟩ := Finset.mem_image.mp member
      obtain ⟨d,rfl⟩ := (mem_cells_iff_point t q e).mp he
      exact ⟨d,heq.symm⟩
    · intro d
      have member : Cell.add (Cell.sub (point t p a) (point t q b)) (point t q d) ∈ p.cells (fun _ => t.cells) := by
        rw [eq]
        exact Finset.mem_image.mpr ⟨_,(mem_cells_iff_point t q _).mpr ⟨d,rfl⟩,rfl⟩
      exact (mem_cells_iff_point t p _).mp member
  · rintro ⟨forward,backward⟩
    ext e
    constructor
    · intro he
      obtain ⟨c,rfl⟩ := (mem_cells_iff_point t p e).mp he
      obtain ⟨d,eq⟩ := forward c
      exact Finset.mem_image.mpr ⟨_,(mem_cells_iff_point t q _).mpr ⟨d,rfl⟩,eq.symm⟩
    · intro he
      obtain ⟨f,hf,rfl⟩ := Finset.mem_image.mp he
      obtain ⟨d,rfl⟩ := (mem_cells_iff_point t q f).mp hf
      obtain ⟨c,eq⟩ := backward d
      exact (mem_cells_iff_point t p _).mpr ⟨c,eq⟩

/-- Validity uses bounded quantifiers and natural arithmetic only. -/
def Valid (t : Tromino) (input : PeriodicStripTrominoPrefill) : Prop :=
  (∀ p ∈ input.motif, ∀ k : Fin 3,
    bound input ≤ (biasedCell t (bound input) p k).2 ∧
      (biasedCell t (bound input) p k).2 < bound input + input.height) ∧
  ∀ p ∈ input.motif, ∀ q ∈ input.motif, ∀ a b : Fin 3,
    SamePlace t input p q a b →
      (∀ c, ∃ d, Aligned t input p q a b c d) ∧ (∀ d, ∃ c, Aligned t input p q a b c d)

theorem valid_iff (t : Tromino) (input : PeriodicStripTrominoPrefill) :
    Valid t input ↔ PeriodicStripTrominoPrefill.Valid t input := by
  unfold Valid PeriodicStripTrominoPrefill.Valid
  simp only [forall_cells_iff]
  apply and_congr
  · apply forall_congr'; intro p
    apply forall_congr'; intro hp
    apply forall_congr'; intro k
    have h := biasedCell_eq t input p hp k
    dsimp [point,Cell.add]
    omega
  · apply forall_congr'; intro p
    apply forall_congr'; intro hp
    apply forall_congr'; intro q
    apply forall_congr'; intro hq
    apply forall_congr'; intro a
    apply forall_congr'; intro b
    rw [samePlace_iff t input p q hp hq,← footprints_aligned_iff t input p q hp hq]
    exact and_imp

end LeanTrominoes.PeriodicStripTrominoPrefill.Raw
