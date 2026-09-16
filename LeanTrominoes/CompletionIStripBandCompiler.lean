/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.CompletionIStripCapped
import LeanTrominoes.CompletionHorizontalPrefill

/-! # A finite horizontal motif for a band of I-bricks -/
noncomputable section
namespace LeanTrominoes.CompletionPattern.IBricks

set_option maxHeartbeats 2000000

theorem band_prescribed_motif (palette : Cell → Fin 24) (count : Int) (f : Finset Cell) :
    f ∈ bandPrescribed palette count ↔ ∃ location : Cell, InBand count location ∧
      ∃ p ∈ motif (palette location), f = (p.shift (origin location)).cells (fun _ => Tromino.I.cells) := by
  constructor
  · rintro ⟨o,hb,p,hp,eq⟩
    refine ⟨o.location,hb,p.shift o.entry.2,List.mem_flatMap.mpr
      ⟨o.entry,o.member,List.mem_map.mpr ⟨p,hp,rfl⟩⟩,?_⟩
    rw [eq]
    congr 1
    simp [Placement.shift,atomOffset,Cell.add,Int.add_assoc]
  · rintro ⟨location,hb,q,hq,rfl⟩
    obtain ⟨entry,he,hq⟩ := List.mem_flatMap.mp hq
    change q ∈ entry.1.motif.map (fun p => p.shift entry.2) at hq
    obtain ⟨p,hp,eq⟩ := List.mem_map.mp hq
    subst q
    refine ⟨⟨location,entry,he⟩,hb,p,hp,?_⟩
    congr 1
    simp [Placement.shift,atomOffset,Cell.add,Int.add_assoc]

def bandSites (period count : Nat) : List Cell :=
  (List.range period).flatMap fun (x : Nat) => (List.range count).map fun (y : Nat) => ((x:Int),(y:Int))

theorem mem_bandSites (period count : Nat) (c : Cell) :
    c ∈ bandSites period count ↔ 0 ≤ c.1 ∧ c.1 < period ∧ 0 ≤ c.2 ∧ c.2 < count := by
  unfold bandSites
  constructor
  · intro hc
    obtain ⟨x,hx,hc⟩ := List.mem_flatMap.mp hc
    obtain ⟨y,hy,rfl⟩ := List.mem_map.mp hc
    have bx := List.mem_range.mp hx
    have by' := List.mem_range.mp hy
    omega
  · rintro ⟨hx0,hx,hy0,hy⟩
    exact List.mem_flatMap.mpr ⟨c.1.toNat,List.mem_range.mpr (by omega),
      List.mem_map.mpr ⟨c.2.toNat,List.mem_range.mpr (by omega),by
        apply Prod.ext <;> simp <;> omega⟩⟩

def bandMotif (period count : Nat) (palette : Cell → Fin 24) : List (Placement Unit) :=
  (bandSites period count).flatMap fun c => (motif (palette c)).map fun p => p.shift (origin c)

theorem origin_horizontal_repeat (c : Cell) (period i : Int) :
    origin (c.1+i*period,c.2) = Cell.add (i*(36*period),0) (origin c) := by
  apply Prod.ext <;> simp [origin,Cell.add] <;> ring

theorem bandMotif_prescribed (period count : Nat) (periodPositive : 0 < period) (palette : Cell → Fin 24)
    (periodic : ∀ c (i : Int), palette (c.1+i*period,c.2) = palette c) :
    HorizontalPrefill.prescribed .I (36*period) (bandMotif period count palette) =
      bandPrescribed palette count := by
  ext f
  rw [band_prescribed_motif]
  constructor
  · rintro ⟨_,hq,i,rfl⟩
    obtain ⟨c,hc,hq⟩ := List.mem_flatMap.mp hq
    obtain ⟨p,hp,rfl⟩ := List.mem_map.mp hq
    have bounds := (mem_bandSites period count c).mp hc
    refine ⟨(c.1+i*period,c.2),⟨bounds.2.2.1,bounds.2.2.2⟩,p,?_,?_⟩
    · simpa only [periodic] using hp
    · rw [origin_horizontal_repeat]
      congr 1
      simp [Placement.shift,Cell.add,Int.add_assoc]
  · rintro ⟨location,hb,p,hp,rfl⟩
    have positive : (0:Int) < period := by exact_mod_cast periodPositive
    have low := Int.emod_nonneg location.1 (ne_of_gt positive)
    have high := Int.emod_lt_of_pos location.1 positive
    let c : Cell := (location.1%period,location.2)
    have hc : c ∈ bandSites period count := by
      rw [mem_bandSites]
      unfold InBand at hb
      dsimp [c]
      omega
    have rep : (c.1+(location.1/period)*period,c.2) = location := by
      apply Prod.ext
      · change location.1%period+(location.1/period)*period = location.1
        rw [Int.mul_comm (location.1/period)]
        exact Int.emod_add_mul_ediv location.1 period
      · rfl
    have labels : palette c = palette location := by rw [← rep,periodic]
    refine ⟨p.shift (origin c),List.mem_flatMap.mpr
      ⟨c,hc,List.mem_map.mpr ⟨p,by rwa [labels],rfl⟩⟩,location.1/period,?_⟩
    have origins := origin_horizontal_repeat c period (location.1/period)
    rw [rep] at origins
    rw [origins]
    congr 1
    simp [Placement.shift,Cell.add,Int.add_assoc]

end LeanTrominoes.CompletionPattern.IBricks
