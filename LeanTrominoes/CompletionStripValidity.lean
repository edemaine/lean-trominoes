/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.PeriodicTrominoCompletion

/-! # Finite validity checks for periodic strip prefills

Only pairs of motif cells that coincide modulo the horizontal period can
witness an overlap. Coincident descriptions of the same tile are permitted.
-/

namespace LeanTrominoes.PeriodicStripTrominoPrefill

set_option maxHeartbeats 2000000

def translate (input : PeriodicStripTrominoPrefill) (i : Int) (f : Finset Cell) : Finset Cell :=
  f.image (Cell.add (i * input.period,0))

theorem prescribed_iff (t : Tromino) (input : PeriodicStripTrominoPrefill) (f : Finset Cell) :
    f ∈ input.periodic.prescribed t ↔
      ∃ p ∈ input.motif, ∃ i : Int, f = input.translate i (p.cells (fun _ => t.cells)) := by
  simp [PeriodicTrominoPrefill.prescribed,periodic,translate,Cell.scale,Cell.add]

def Valid (t : Tromino) (input : PeriodicStripTrominoPrefill) : Prop :=
  (∀ p ∈ input.motif, ∀ c ∈ p.cells (fun _ => t.cells), 0 ≤ c.2 ∧ c.2 < (input.height : Int)) ∧
  ∀ p ∈ input.motif, ∀ q ∈ input.motif,
    ∀ a ∈ p.cells (fun _ => t.cells), ∀ b ∈ q.cells (fun _ => t.cells),
      a.2 = b.2 → (input.period : Int) ∣ a.1 - b.1 →
      p.cells (fun _ => t.cells) = (q.cells (fun _ => t.cells)).image (Cell.add (Cell.sub a b))

instance (t : Tromino) (input : PeriodicStripTrominoPrefill) : Decidable (Valid t input) := by
  unfold Valid
  infer_instance

theorem valid_iff_partial (t : Tromino) (input : PeriodicStripTrominoPrefill) :
    Valid t input ↔ t.IsPartialTiling input.region (input.periodic.prescribed t) := by
  constructor
  · rintro ⟨inside,compatible⟩
    constructor
    · intro f hf
      refine ⟨input.periodic.prescribed_legal t hf,?_⟩
      obtain ⟨p,hp,i,rfl⟩ := (prescribed_iff t input f).mp hf
      intro c hc
      obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp hc
      simpa [region,Cell.add] using inside p hp a ha
    · intro f hf g hg c hc hd
      obtain ⟨p,hp,i,rfl⟩ := (prescribed_iff t input f).mp hf
      obtain ⟨q,hq,j,rfl⟩ := (prescribed_iff t input g).mp hg
      obtain ⟨a,ha,ea⟩ := Finset.mem_image.mp hc
      obtain ⟨b,hb,eb⟩ := Finset.mem_image.mp hd
      have ey : a.2 = b.2 := by
        have := congrArg Prod.snd (ea.trans eb.symm)
        simpa [Cell.add] using this
      have ex : a.1 - b.1 = (input.period : Int) * (j-i) := by
        have := congrArg Prod.fst (ea.trans eb.symm)
        dsimp [Cell.add] at this
        calc
          a.1 - b.1 = j * input.period - i * input.period := by omega
          _ = (input.period : Int) * (j-i) := by ring
      have eq := compatible p hp q hq a ha b hb ey ⟨j-i,ex⟩
      unfold translate
      rw [eq,Finset.image_image]
      apply Finset.image_congr
      intro d hd
      apply Prod.ext
      · dsimp [Function.comp_def,Cell.add,Cell.sub]
        have := congrArg Prod.fst (ea.trans eb.symm)
        dsimp [Cell.add] at this
        omega
      · dsimp [Function.comp_def,Cell.add,Cell.sub]
        omega
  · intro valid
    have base (p : Placement Unit) (hp : p ∈ input.motif) :
        p.cells (fun _ => t.cells) ∈ input.periodic.prescribed t := by
      apply (prescribed_iff t input _).mpr
      exact ⟨p,hp,0,by
        simp [translate,show Cell.add (0,0) = id by funext c; simp [Cell.add]]⟩
    refine ⟨fun p hp c hc => (valid.tilesInside _ (base p hp)).2 c hc,?_⟩
    intro p hp q hq a ha b hb ey ⟨k,ek⟩
    have shifted : (q.cells (fun _ => t.cells)).image (Cell.add (Cell.sub a b)) ∈
        input.periodic.prescribed t := by
      apply (prescribed_iff t input _).mpr
      refine ⟨q,hq,k,?_⟩
      have eq : Cell.sub a b = (k * input.period,0) := by
        apply Prod.ext <;> dsimp [Cell.sub]
        · rw [ek]; ring
        · omega
      simp only [translate,eq]
    apply valid.nonoverlap _ (base p hp) _ shifted a ha
    exact Finset.mem_image.mpr ⟨b,hb,by apply Prod.ext <;> dsimp [Cell.add,Cell.sub] <;> omega⟩

end LeanTrominoes.PeriodicStripTrominoPrefill
