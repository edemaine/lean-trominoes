/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.Tiling.Domino.DominoWordRAMSourceBlocks

/-! # Loading a basis and two original representatives for a decoder circuit -/
namespace LeanTrominoes.Domino.WordRAM.Binary.SourceLoad
open ComplexityAbstract.RAM
abbrev Data := SourceBlocks.Data
abbrev Code := SourceBlocks.Code

def header : Fin 3 → Fin 64 | 0 => SourceBlocks.basisBase | 1 => SourceBlocks.firstOrigin | 2 => SourceBlocks.secondOrigin
def count (d : ℕ) : Fin 3 → ℕ | 0 => d*d | _ => d
def start (d : ℕ) : Fin 3 → ℕ | 0 => 0 | 1 => d*d | _ => d*d+d

def program (d : ℕ) : Code :=
  .seq (SourceBlocks.program (header 0) (count d 0) (start d 0)) <|
  .seq (SourceBlocks.program (header 1) (count d 1) (start d 1))
       (SourceBlocks.program (header 2) (count d 2) (start d 2))

structure Layout where
  dimension : ℕ
  length : ℕ
  base : ℕ
  source : Fin 3 → ℕ

structure Controls (p : Layout) (data : Data) : Prop where
  length : data.1 SourceBlocks.precision=p.length
  base : data.1 SourceBlocks.circuitBase=p.base
  source : ∀ block, data.1 (header block)=p.source block

structure Result (p : Layout) (source : ℕ → ℕ) (data : Data) : Prop where
  controls : Controls p data
  copied : ∀ block : Fin 3, ∀ slot< count p.dimension block, ∀ i< p.length,
    data.2 (p.base+(start p.dimension block+slot)*p.length+i)=source (p.source block+slot*p.length+i)
  frame : ∀ address, (address< p.base ∨ p.base+(p.dimension*p.dimension+2*p.dimension)*p.length≤ address) →
    data.2 address=source address

theorem Controls.after {p : Layout} {before after : Data} (h : Controls p before)
    (registers : ∀ i : Fin 64, 59≤ i.val → after.1 i=before.1 i) : Controls p after := by
  constructor
  · rw [registers _ (by decide)]; exact h.length
  · rw [registers _ (by decide)]; exact h.base
  · intro block
    rw [registers _ (by fin_cases block <;> decide)]
    exact h.source block

private theorem point_outside {p : Layout} {address : ℕ}
    (outside : address< p.base ∨ p.base+(p.dimension*p.dimension+2*p.dimension)*p.length≤ address)
    (block : Fin 3) : address< p.base+start p.dimension block*p.length ∨
      p.base+(start p.dimension block+count p.dimension block)*p.length≤ address := by
  fin_cases block <;> norm_num [start,count] <;> rcases outside with before | after
  all_goals first | exact Or.inl (by nlinarith) | exact Or.inr (by nlinarith)

theorem program_exec {w : ℕ} (p : Layout) (data : Data) (controls : Controls p data)
    (outside : ∀ block : Fin 3, ∀ slot< count p.dimension block, ∀ i< p.length,
      p.source block+slot*p.length+i< p.base ∨
        p.base+(p.dimension*p.dimension+2*p.dimension)*p.length≤ p.source block+slot*p.length+i)
    (bits : ∀ block : Fin 3, ∀ slot< count p.dimension block, ∀ i< p.length,
      data.2 (p.source block+slot*p.length+i)≤1)
    (fits : ∀ block : Fin 3, Fits w (BatchCopy.bound (p.source block) p.base p.length 0
      (start p.dimension block) (count p.dimension block))) :
    ∃ result, NaturalData.Exec w (program p.dimension) data result
        ((7*p.length+11)*(p.dimension*p.dimension+2*p.dimension)+15) ∧ Result p data.2 result := by
  have call (block : Fin 3) (before : Data) (h : Controls p before)
      (same : ∀ b : Fin 3, ∀ slot< count p.dimension b, ∀ i< p.length,
        before.2 (p.source b+slot*p.length+i)=data.2 (p.source b+slot*p.length+i)) :
      ∃ after, NaturalData.Exec w (SourceBlocks.program (header block) (count p.dimension block) (start p.dimension block)) before after
          (4+((7*p.length+11)*count p.dimension block+1)) ∧
        BatchCopy.Result (p.source block) p.base p.length 0 (start p.dimension block) (count p.dimension block) before.2 after ∧
        Controls p after ∧
        (∀ b : Fin 3, ∀ slot< count p.dimension b, ∀ i< p.length,
          after.2 (p.source b+slot*p.length+i)=data.2 (p.source b+slot*p.length+i)) := by
    obtain ⟨after,run,correct,registers⟩ := SourceBlocks.program_exec before (header block)
      (by fin_cases block <;> decide) (count p.dimension block) (start p.dimension block)
      (by
        rw [h.length,h.base,h.source]
        intro a ha b hb x hx y hy equal
        have bounds := point_outside (outside block a ha x hx) block
        rcases bounds with before | after <;> nlinarith)
      (by rw [h.length,h.source]; intro j hj i hi; rw [same block j hj i hi]; exact bits block j hj i hi)
      (by simpa only [h.length,h.base,h.source] using fits block)
    refine ⟨after,by simpa only [h.length] using run,?_,h.after registers,?_⟩
    · simpa only [h.length,h.base,h.source] using correct
    · intro b slot hs i hi
      rw [correct.frame _ (by simpa only [h.length,h.base,h.source] using point_outside (outside b slot hs i hi) block)]
      exact same b slot hs i hi
  obtain ⟨first,firstRun,firstResult,firstControls,firstSources⟩ := call 0 data controls (fun _ _ _ _ _ => rfl)
  obtain ⟨second,secondRun,secondResult,secondControls,secondSources⟩ := call 1 first firstControls firstSources
  obtain ⟨third,thirdRun,thirdResult,thirdControls,thirdSources⟩ := call 2 second secondControls secondSources
  refine ⟨third,?_,thirdControls,?_,?_⟩
  · have run := firstRun.seq (secondRun.seq thirdRun)
    convert run using 1 <;> simp only [program,start,count] <;> ring
  · intro block slot hs i hi
    fin_cases block
    · change slot<count p.dimension 0 at hs
      change third.2 (p.base+(start p.dimension 0+slot)*p.length+i)=data.2 (p.source 0+slot*p.length+i)
      have secondOutside : p.base+(start p.dimension 0+slot)*p.length+i< p.base+start p.dimension 1*p.length := by
        apply Circuit.digit_before
        · simpa [start,count] using hs
        · exact hi
      have thirdOutside : p.base+(start p.dimension 0+slot)*p.length+i< p.base+start p.dimension 2*p.length := by
        apply Circuit.digit_before
        · norm_num [start,count] at hs ⊢; omega
        · exact hi
      rw [thirdResult.frame _ (Or.inl thirdOutside),secondResult.frame _ (Or.inl secondOutside)]
      simpa only [Nat.zero_add] using firstResult.copied slot hs i hi
    · change slot<count p.dimension 1 at hs
      change third.2 (p.base+(start p.dimension 1+slot)*p.length+i)=data.2 (p.source 1+slot*p.length+i)
      have thirdOutside : p.base+(start p.dimension 1+slot)*p.length+i< p.base+start p.dimension 2*p.length := by
        apply Circuit.digit_before
        · norm_num [start,count] at hs ⊢; omega
        · exact hi
      rw [thirdResult.frame _ (Or.inl thirdOutside)]
      have copied := secondResult.copied slot hs i hi
      simp only [Nat.zero_add] at copied
      exact copied.trans (firstSources 1 slot hs i hi)
    · change slot<count p.dimension 2 at hs
      change third.2 (p.base+(start p.dimension 2+slot)*p.length+i)=data.2 (p.source 2+slot*p.length+i)
      have copied := thirdResult.copied slot hs i hi
      simp only [Nat.zero_add] at copied
      exact copied.trans (secondSources 2 slot hs i hi)
  · intro address h
    rw [thirdResult.frame address (point_outside h 2),secondResult.frame address (point_outside h 1),
      firstResult.frame address (point_outside h 0)]

end LeanTrominoes.Domino.WordRAM.Binary.SourceLoad
