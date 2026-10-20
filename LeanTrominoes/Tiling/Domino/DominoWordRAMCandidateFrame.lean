/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.Tiling.Domino.DominoWordRAMCandidateBounds

/-! # Persistent global data while constructing all candidate edges -/
namespace LeanTrominoes.Domino.WordRAM.Binary.Candidate
open ComplexityAbstract.RAM
abbrev Data := NaturalData 128
variable {n d : ℕ}

def inputEnd (B : BasisData n d) : ℕ := (words B).length+1

structure Frame (B : BasisData n d) (u v : Fin n) (data : Data) : Prop where
  precision : data.1 Reserve.precision=WordRAM.precision B
  zero : data.1 ProbeHeaders.zero=inputEnd B
  determinant : data.1 ProbeHeaders.determinant=inputEnd B+WordRAM.precision B
  twice : data.1 ProbeHeaders.twice=inputEnd B+2*WordRAM.precision B
  parities : data.1 Collect.parities=inputEnd B+3*WordRAM.precision B
  first : data.1 ProbeHeaders.firstOrigin=4+(d*d+u.val*d)*WordRAM.precision B
  second : data.1 ProbeHeaders.secondOrigin=4+(d*d+v.val*d)*WordRAM.precision B
  frontier : inputEnd B+(3+d)*WordRAM.precision B≤ data.1 Reserve.frontier
  original : ∀ address< inputEnd B, data.2 address=inputMemory B address
  zero_digits : ∀ i< WordRAM.precision B, data.2 (inputEnd B+i)=0
  determinant_bits : ∀ i< WordRAM.precision B, data.2 (inputEnd B+WordRAM.precision B+i)≤1
  twice_bits : ∀ i< WordRAM.precision B, data.2 (inputEnd B+2*WordRAM.precision B+i)≤1
  determinant_value : value data.2 (inputEnd B+WordRAM.precision B) (WordRAM.precision B)=B.basis.det.natAbs
  twice_value : value data.2 (inputEnd B+2*WordRAM.precision B) (WordRAM.precision B)=2*B.basis.det.natAbs
  nonzero : B.basis.det≠0

noncomputable def layout (B : BasisData n d) (direction coordinate : Fin d) (data : Data)
    (frontier : inputEnd B+(3+d)*WordRAM.precision B≤ data.1 Reserve.frontier) : FreshProbe.Layout where
  base := data.1 Reserve.frontier
  length := WordRAM.precision B
  outputSlot := ((Circuit.rawNumeratorCircuit d direction coordinate).compile (d*d+2*d)).output
  circuitSlots := slots direction coordinate
  output_before := (Circuit.rawNumeratorCircuit d direction coordinate).output_lt (d*d+2*d) (le_refl _)
  global := fun i => inputEnd B+i.val*WordRAM.precision B
  global_disjoint := by
    intro i j different
    have ne : i.val≠j.val := fun equal => different (Fin.ext equal)
    by_cases less : i.val< j.val
    · have mul := Nat.mul_le_mul_right (WordRAM.precision B) (Nat.succ_le_of_lt less)
      left; nlinarith
    · have mul := Nat.mul_le_mul_right (WordRAM.precision B) (show j.val+1≤ i.val by omega)
      right; nlinarith
  global_before := by
    intro i
    have hi := i.isLt
    have mul := Nat.mul_le_mul_right (WordRAM.precision B) (show i.val+1≤3+d by omega)
    nlinarith

theorem Frame.environment {B : BasisData n d} {u v : Fin n} {data : Data} (h : Frame B u v data)
    (direction coordinate : Fin d) : FreshProbe.GlobalEnvironment (layout B direction coordinate data h.frontier) data.2 B.basis.det := by
  constructor
  · simpa [layout] using h.determinant_bits
  · simpa [layout] using h.twice_bits
  · simpa [layout] using h.zero_digits
  · simpa [layout] using h.determinant_value
  · simpa [layout] using h.twice_value
  · exact h.nonzero
  · change 4*B.basis.det.natAbs≤2^WordRAM.precision B
    have guard := determinant_guard B
    nlinarith only [guard]

theorem inputEnd_four (B : BasisData n d) : 4≤ inputEnd B := by
  unfold inputEnd
  rw [words_length]
  omega

theorem Frame.length_le {B : BasisData n d} {u v : Fin n} {data : Data} (h : Frame B u v data) :
    WordRAM.precision B≤ data.1 Reserve.frontier := by have front := h.frontier; nlinarith

theorem Frame.source_bound {B : BasisData n d} {u v : Fin n} {data : Data} (h : Frame B u v data)
    (direction : Fin d) (block : Fin 3) : (sourceLayout B u v (data.1 Reserve.frontier)).source block≤ data.1 Reserve.frontier := by
  have inputBefore : inputEnd B≤ data.1 Reserve.frontier := by have front := h.frontier; nlinarith
  fin_cases block
  · change 4+sourceRank d u.val v.val 0*WordRAM.precision B≤_
    norm_num [sourceRank]
    exact (inputEnd_four B).trans inputBefore
  · have before := original_source_before B u v (data.1 Reserve.frontier) 1 0
      (by have := direction.isLt; norm_num [SourceLoad.count]; omega) 0 (by unfold WordRAM.precision; omega)
    simpa [inputEnd] using (Nat.le_of_lt before).trans inputBefore
  · have before := original_source_before B u v (data.1 Reserve.frontier) 2 0
      (by have := direction.isLt; norm_num [SourceLoad.count]; omega) 0 (by unfold WordRAM.precision; omega)
    simpa [inputEnd] using (Nat.le_of_lt before).trans inputBefore

theorem Frame.headers_bound {B : BasisData n d} {u v : Fin n} {data : Data} (h : Frame B u v data)
    (direction : Fin d) (highWater : ℕ) (frontier : data.1 Reserve.frontier≤ highWater) :
    ∀ i∈FreshProbe.headerRegisters, data.1 i≤ highWater := by
  intro i member
  simp only [FreshProbe.headerRegisters,List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · rw [h.precision]; exact h.length_le.trans frontier
  · exact frontier
  · rw [h.zero]; have front := h.frontier; nlinarith
  · rw [h.determinant]; have front := h.frontier; nlinarith
  · rw [h.twice]; have front := h.frontier; nlinarith
  · rw [h.first]
    have bound := h.source_bound direction 1
    simpa [sourceLayout,sourceRank] using bound.trans frontier
  · rw [h.second]
    have bound := h.source_bound direction 2
    simpa [sourceLayout,sourceRank] using bound.trans frontier

def persistentHeaders : List (Fin 128) := [Reserve.precision,ProbeHeaders.zero,ProbeHeaders.determinant,
  ProbeHeaders.twice,Collect.parities,ProbeHeaders.firstOrigin,ProbeHeaders.secondOrigin]

theorem Frame.transport {B : BasisData n d} {u v : Fin n} {before after : Data} (h : Frame B u v before)
    (fixed : ∀ i∈persistentHeaders, after.1 i=before.1 i)
    (front : before.1 Reserve.frontier≤ after.1 Reserve.frontier)
    (memory : ∀ address< inputEnd B+3*WordRAM.precision B, after.2 address=before.2 address) : Frame B u v after := by
  constructor
  · rw [fixed _ (by simp [persistentHeaders])]; exact h.precision
  · rw [fixed _ (by simp [persistentHeaders])]; exact h.zero
  · rw [fixed _ (by simp [persistentHeaders])]; exact h.determinant
  · rw [fixed _ (by simp [persistentHeaders])]; exact h.twice
  · rw [fixed _ (by simp [persistentHeaders])]; exact h.parities
  · rw [fixed _ (by simp [persistentHeaders])]; exact h.first
  · rw [fixed _ (by simp [persistentHeaders])]; exact h.second
  · exact h.frontier.trans front
  · intro address within
    rw [memory address (by nlinarith only [within])]
    exact h.original address within
  · intro i hi
    rw [memory _ (by nlinarith only [hi])]
    exact h.zero_digits i hi
  · intro i hi
    rw [memory _ (by nlinarith only [hi])]
    exact h.determinant_bits i hi
  · intro i hi
    rw [memory _ (by nlinarith only [hi])]
    exact h.twice_bits i hi
  · rw [value_congr (fun i hi => memory _ (by nlinarith only [hi]))]
    exact h.determinant_value
  · rw [value_congr (fun i hi => memory _ (by nlinarith only [hi]))]
    exact h.twice_value
  · exact h.nonzero

theorem Frame.change_representatives {B : BasisData n d} {u v u' v' : Fin n} {before after : Data}
    (h : Frame B u v before)
    (fixed : ∀ i∈[Reserve.precision,ProbeHeaders.zero,ProbeHeaders.determinant,ProbeHeaders.twice,Collect.parities],
      after.1 i=before.1 i)
    (first : after.1 ProbeHeaders.firstOrigin=4+(d*d+u'.val*d)*WordRAM.precision B)
    (second : after.1 ProbeHeaders.secondOrigin=4+(d*d+v'.val*d)*WordRAM.precision B)
    (front : before.1 Reserve.frontier≤ after.1 Reserve.frontier)
    (memory : ∀ address< inputEnd B+3*WordRAM.precision B, after.2 address=before.2 address) : Frame B u' v' after := by
  constructor
  · rw [fixed _ (by simp)]; exact h.precision
  · rw [fixed _ (by simp)]; exact h.zero
  · rw [fixed _ (by simp)]; exact h.determinant
  · rw [fixed _ (by simp)]; exact h.twice
  · rw [fixed _ (by simp)]; exact h.parities
  · exact first
  · exact second
  · exact h.frontier.trans front
  · intro address within
    rw [memory address (by nlinarith only [within])]
    exact h.original address within
  · intro i hi
    rw [memory _ (by nlinarith only [hi])]
    exact h.zero_digits i hi
  · intro i hi
    rw [memory _ (by nlinarith only [hi])]
    exact h.determinant_bits i hi
  · intro i hi
    rw [memory _ (by nlinarith only [hi])]
    exact h.twice_bits i hi
  · rw [value_congr (fun i hi => memory _ (by nlinarith only [hi]))]
    exact h.determinant_value
  · rw [value_congr (fun i hi => memory _ (by nlinarith only [hi]))]
    exact h.twice_value
  · exact h.nonzero

end LeanTrominoes.Domino.WordRAM.Binary.Candidate
