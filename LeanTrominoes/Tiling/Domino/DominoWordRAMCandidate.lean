/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.Tiling.Domino.DominoWordRAMCandidateScan

/-! # A complete candidate test using a fixed bounded-word RAM program -/
namespace LeanTrominoes.Domino.WordRAM.Binary.Candidate
open ComplexityAbstract.RAM
variable {n d : ℕ}

noncomputable def program (direction : Fin d) : Structured.Code 128 :=
  .seq (.atom (.constant Collect.active 1)) (scan direction (List.finRange d))

theorem reserveSpace_finRange (direction : Fin d) : reserveSpace direction (List.finRange d)=space direction := by
  simp [reserveSpace,space,←List.ofFn_eq_map,List.sum_ofFn]

theorem program_exec {w : ℕ} (B : BasisData n d) (u v : Fin n) (direction : Fin d)
    (data : Data) (h : Frame B u v data) (highWater : ℕ)
    (budget : data.1 Reserve.frontier+space direction*WordRAM.precision B≤ highWater)
    (width : Fits w (FreshProbe.scalarBound (slotBound d) highWater)) :
    ∃ result cost, NaturalData.Exec w (program direction) data result cost ∧
      cost≤ d*coordinateCost (slotBound d) (WordRAM.precision B)+2 ∧ Frame B u v result ∧
      result.1 Reserve.frontier=data.1 Reserve.frontier+space direction*WordRAM.precision B ∧
      (result.1 Collect.active≠0 ↔ PaddedGraph.Active B u direction v) ∧
      (∀ i : Fin d, result.2 (result.1 Collect.parities+i.val)≤1) ∧
      (PaddedGraph.Active B u direction v → ∀ i : Fin d,
        result.2 (result.1 Collect.parities+i.val)=(PaddedGraph.coordinates B u direction v i%2).toNat) ∧
      (∀ i : Fin 128, 64≤ i.val → i≠Reserve.frontier → i≠Reserve.base → i≠Collect.active →
        i≠Collect.zero → i≠Collect.index → i≠Collect.address → result.1 i=data.1 i) ∧
      (∀ address, address< data.1 Reserve.frontier →
        (address< data.1 Collect.parities ∨ data.1 Collect.parities+d≤ address) → result.2 address=data.2 address) := by
  have unit : Fits w (1:ℕ) := Allocation.nat_fits_le width (by unfold FreshProbe.scalarBound; nlinarith)
  let initial := data.set Collect.active 1
  have initialFrame : Frame B u v initial := by
    apply h.transport
    · intro i member
      simp only [persistentHeaders,List.mem_cons,List.not_mem_nil,or_false] at member
      rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      all_goals simp [initial,NaturalData.set,Collect.active,Reserve.precision,ProbeHeaders.zero,ProbeHeaders.determinant,
        ProbeHeaders.twice,Collect.parities,ProbeHeaders.firstOrigin,ProbeHeaders.secondOrigin]
    · simp [initial,NaturalData.set,Reserve.frontier,Collect.active]
    · intro address within; rfl
  have progress : Progress B u v direction [] initial := by
    refine ⟨initialFrame,?_,?_,by simp,by simp⟩
    · simp [initial,NaturalData.set]
    · simp [initial,NaturalData.set]
  have initialBudget : initial.1 Reserve.frontier+reserveSpace direction (List.finRange d)*WordRAM.precision B≤ highWater := by
    simpa [initial,NaturalData.set,Reserve.frontier,Collect.active,reserveSpace_finRange] using budget
  obtain ⟨result,scanCost,run,bound,correct,front,fixed,memory⟩ := scan_exec B u v direction highWater width (List.finRange d)
    [] initial (List.nodup_finRange d) (by simp) progress initialBudget
  have complete : ∀ coordinate : Fin d, coordinate∈(List.finRange d).reverse++[] := by simp
  have summary := correct.done complete
  have initRun := NaturalData.constant_exec data Collect.active 1 unit
  refine ⟨result,1+scanCost,initRun.seq run,?_,correct.frame,?_,summary.1,summary.2.1,summary.2.2,?_,?_⟩
  · simp only [List.length_finRange] at bound
    omega
  · simpa [initial,NaturalData.set,Reserve.frontier,Collect.active,reserveSpace_finRange] using front
  · intro i high notFront notBase notActive notZero notIndex notAddress
    rw [fixed i high notFront notBase notActive notZero notIndex notAddress]
    exact Function.update_of_ne notActive _ _
  · intro address below outside
    apply memory address
    · simpa [initial,NaturalData.set,Reserve.frontier,Collect.active] using below
    · simpa [initial,NaturalData.set,Collect.parities,Collect.active] using outside

end LeanTrominoes.Domino.WordRAM.Binary.Candidate
