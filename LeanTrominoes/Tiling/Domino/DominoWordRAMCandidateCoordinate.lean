/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.Tiling.Domino.DominoWordRAMCandidateFrame

/-! # One complete coordinate stage of a candidate test -/
namespace LeanTrominoes.Domino.WordRAM.Binary.Candidate
open ComplexityAbstract.RAM
variable {n d : ℕ}

noncomputable def coordinateProgram (direction coordinate : Fin d) : Structured.Code 128 :=
  .seq (FreshProbe.callProgram d direction coordinate) (Collect.program coordinate.val)

theorem coordinate_exec {w : ℕ} (B : BasisData n d) (u v : Fin n) (direction coordinate : Fin d)
    (data : Data) (h : Frame B u v data) (highWater : ℕ) (frontier : data.1 Reserve.frontier≤ highWater)
    (width : Fits w (FreshProbe.scalarBound (slotBound d) highWater)) (activeBit : data.1 Collect.active≤1) :
    ∃ result cost, NaturalData.Exec w (coordinateProgram direction coordinate) data result cost ∧
      cost≤ coordinateCost (slotBound d) (WordRAM.precision B) ∧ Frame B u v result ∧
      result.1 Reserve.frontier=data.1 Reserve.frontier+(slots direction coordinate+3)*WordRAM.precision B ∧
      result.1 Collect.active≤1 ∧
      (0< result.1 Collect.active ↔ 0< data.1 Collect.active ∧
        B.basis.det∣(Circuit.rawNumeratorCircuit d direction coordinate).eval (rawInputs B u v)) ∧
      result.1 Collect.parity≤1 ∧
      (B.basis.det∣(Circuit.rawNumeratorCircuit d direction coordinate).eval (rawInputs B u v) →
        ((Circuit.rawNumeratorCircuit d direction coordinate).eval (rawInputs B u v)/B.basis.det)%2=
          (result.1 Collect.parity : ℤ)) ∧
      result.2 (data.1 Collect.parities+coordinate.val)=result.1 Collect.parity ∧
      (∀ address, address< data.1 Reserve.frontier → address≠data.1 Collect.parities+coordinate.val →
        result.2 address=data.2 address) ∧
      (∀ i : Fin 128, 64≤ i.val → i≠Reserve.frontier → i≠Reserve.base → i≠Collect.active →
        i≠Collect.zero → i≠Collect.index → i≠Collect.address → result.1 i=data.1 i) := by
  let p := layout B direction coordinate data h.frontier
  have small : 4≤ highWater := (inputEnd_four B).trans ((by have front := h.frontier; nlinarith : inputEnd B≤ data.1 Reserve.frontier).trans frontier)
  have headers := h.headers_bound direction highWater frontier
  have resources : FreshProbe.Resources data p w := FreshProbe.resources_of_bound data p (slotBound d) highWater
    (slots_le direction coordinate) small headers width
  have lengthBound : WordRAM.precision B≤ highWater := h.length_le.trans frontier
  have sourceBounds := fun block => (h.source_bound direction block).trans frontier
  have sourceFits := FreshProbe.source_fits_of_bound B u v p.base p.length (slotBound d) highWater (arity_le d)
    sourceBounds frontier lengthBound width
  have circuitFits := FreshProbe.circuit_fits_of_bound p (slotBound d) highWater (slots_le direction coordinate) frontier lengthBound width
  obtain ⟨fresh,freshCost,freshRun,freshBound,valid,bit,parity,newFront,newBase,fixed,frame⟩ := FreshProbe.call_exec B u v direction coordinate data p
    rfl h.precision.symm rfl rfl rfl (by simpa [p,layout] using h.zero.symm) (by simpa [p,layout] using h.determinant.symm)
    (by simpa [p,layout] using h.twice.symm)
    (by simpa [p,layout,sourceLayout,sourceRank] using h.first)
    (by simpa [p,layout,sourceLayout,sourceRank] using h.second)
    (h.environment direction coordinate)
    (by intro block slot hs i hi; exact h.original _ (original_source_before B u v p.base block slot hs i hi))
    (by intro block slot hs i hi; exact (original_source_before B u v p.base block slot hs i hi).trans_le (by have front := h.frontier; change inputEnd B≤ p.base; dsimp [p,layout]; nlinarith))
    sourceFits resources circuitFits
  have freshFrame : Frame B u v fresh := by
    apply h.transport
    · intro i member
      simp only [persistentHeaders,List.mem_cons,List.not_mem_nil,or_false] at member
      rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      all_goals exact fixed _ (by decide) (by decide) (by decide)
    · rw [newFront]; omega
    · intro address within
      apply frame address (Or.inl ?_)
      change address< data.1 Reserve.frontier
      have front := h.frontier
      nlinarith only [within,front]
  have activeEq : fresh.1 Collect.active=data.1 Collect.active := fixed _ (by decide) (by decide) (by decide)
  have paritiesEq : fresh.1 Collect.parities=data.1 Collect.parities := fixed _ (by decide) (by decide) (by decide)
  have coordinateFits : Fits w coordinate.val := by
    apply Allocation.nat_fits_le width
    have bound := arity_le d
    have hi := coordinate.isLt
    unfold FreshProbe.scalarBound
    nlinarith
  have pointerBound : fresh.1 Collect.parities+coordinate.val≤ highWater := by
    rw [paritiesEq,h.parities]
    have hi := coordinate.isLt
    have front := h.frontier
    have positive : 1≤WordRAM.precision B := by unfold WordRAM.precision; omega
    have mul := Nat.mul_le_mul_left coordinate.val positive
    nlinarith only [front,frontier,hi,mul]
  have pointerFits : Fits w (fresh.1 Collect.parities+coordinate.val : ℕ) := by
    apply Allocation.nat_fits_le width
    unfold FreshProbe.scalarBound
    nlinarith only [pointerBound]
  obtain ⟨collectCost,collectRun,collectBound⟩ := Collect.program_exec fresh coordinate.val (by rw [activeEq]; exact activeBit) bit
    resources.unit coordinateFits pointerFits
  let result := Collect.result fresh coordinate.val
  have collectFixed (i : Fin 128) (ha : i≠Collect.active) (hz : i≠Collect.zero) (hi : i≠Collect.index) (hp : i≠Collect.address) :
      result.1 i=fresh.1 i := Collect.result_fixed fresh coordinate.val i ha hz hi hp
  have resultFrame : Frame B u v result := by
    apply freshFrame.transport
    · intro i member
      simp only [persistentHeaders,List.mem_cons,List.not_mem_nil,or_false] at member
      rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      all_goals exact collectFixed _ (by decide) (by decide) (by decide) (by decide)
    · rw [collectFixed Reserve.frontier (by decide) (by decide) (by decide) (by decide)]
    · intro address within
      change (Function.update fresh.2 (fresh.1 Collect.parities+coordinate.val) (fresh.1 Collect.parity)) address=fresh.2 address
      apply Function.update_of_ne
      rw [freshFrame.parities]
      omega
  have full := freshRun.seq collectRun
  refine ⟨result,freshCost+collectCost,full,?_,resultFrame,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · have bound := coordinate_cost direction coordinate (WordRAM.precision B)
    change freshCost≤4*((slots direction coordinate+3)*WordRAM.precision B)+
      (26*(WordRAM.precision B)^2+26*WordRAM.precision B+16)*nodeCount direction coordinate+
      29*(WordRAM.precision B)^2+65*WordRAM.precision B+107+(7*WordRAM.precision B+11)*(d*d+2*d) at freshBound
    omega
  · rw [collectFixed Reserve.frontier (by decide) (by decide) (by decide) (by decide)]
    exact newFront
  · exact Collect.result_bit fresh coordinate.val (by rw [activeEq]; exact activeBit)
  · rw [Collect.result_positive,activeEq]
    exact and_congr_right (fun _ => valid)
  · rw [collectFixed Collect.parity (by decide) (by decide) (by decide) (by decide)]
    exact bit
  · rw [collectFixed Collect.parity (by decide) (by decide) (by decide) (by decide)]
    exact parity
  · change (Function.update fresh.2 (fresh.1 Collect.parities+coordinate.val) (fresh.1 Collect.parity)) (data.1 Collect.parities+coordinate.val)=_
    rw [paritiesEq,Function.update_self,collectFixed Collect.parity (by decide) (by decide) (by decide) (by decide)]
  · intro address before different
    change (Function.update fresh.2 (fresh.1 Collect.parities+coordinate.val) (fresh.1 Collect.parity)) address=data.2 address
    rw [Function.update_of_ne (by rw [paritiesEq]; exact different)]
    exact frame address (Or.inl before)
  · intro i high notFront notBase notActive notZero notIndex notAddress
    rw [collectFixed i notActive notZero notIndex notAddress]
    exact fixed i high notFront notBase

end LeanTrominoes.Domino.WordRAM.Binary.Candidate
