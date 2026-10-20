/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.Tiling.Domino.DominoWordRAMCandidateProgress

/-! # Actual execution of the fixed sequence of coordinate probes -/
namespace LeanTrominoes.Domino.WordRAM.Binary.Candidate
open ComplexityAbstract.RAM
variable {n d : ℕ}

noncomputable def reserveSpace (direction : Fin d) (remaining : List (Fin d)) : ℕ :=
  (remaining.map (fun coordinate => slots direction coordinate+3)).sum

noncomputable def scan (direction : Fin d) : List (Fin d) → Structured.Code 128
  | [] => .atom (.copy Collect.active Collect.active)
  | coordinate::rest => .seq (coordinateProgram direction coordinate) (scan direction rest)

theorem scan_exec {w : ℕ} (B : BasisData n d) (u v : Fin n) (direction : Fin d) (highWater : ℕ)
    (width : Fits w (FreshProbe.scalarBound (slotBound d) highWater)) (remaining : List (Fin d)) :
    ∀ done data, remaining.Nodup → (∀ coordinate∈remaining, coordinate∉done) →
    Progress B u v direction done data →
    data.1 Reserve.frontier+reserveSpace direction remaining*WordRAM.precision B≤ highWater →
    ∃ result cost, NaturalData.Exec w (scan direction remaining) data result cost ∧
      cost≤ remaining.length*coordinateCost (slotBound d) (WordRAM.precision B)+1 ∧
      Progress B u v direction (remaining.reverse++done) result ∧
      result.1 Reserve.frontier=data.1 Reserve.frontier+reserveSpace direction remaining*WordRAM.precision B ∧
      (∀ i : Fin 128, 64≤ i.val → i≠Reserve.frontier → i≠Reserve.base → i≠Collect.active →
        i≠Collect.zero → i≠Collect.index → i≠Collect.address → result.1 i=data.1 i) ∧
      (∀ address, address< data.1 Reserve.frontier →
        (address< data.1 Collect.parities ∨ data.1 Collect.parities+d≤ address) → result.2 address=data.2 address) := by
  induction remaining with
  | nil =>
    intro done data nodup fresh progress budget
    have unit : Fits w (1:ℕ) := Allocation.nat_fits_le width (by unfold FreshProbe.scalarBound; nlinarith)
    have flagFits : Fits w (data.1 Collect.active) := Allocation.nat_fits_le unit progress.active
    have run := NaturalData.copy_exec data Collect.active Collect.active flagFits
    refine ⟨data,1,?_,by simp,by simpa using progress,by simp [reserveSpace],fun _ _ _ _ _ _ _ _ => rfl,fun _ _ _ => rfl⟩
    simpa [scan,NaturalData.set] using run
  | cons coordinate rest ih =>
    intro done data nodup fresh progress budget
    have nd := List.nodup_cons.mp nodup
    have headFresh := fresh coordinate List.mem_cons_self
    obtain ⟨middle,firstCost,firstRun,firstBound,firstFrame,firstFront,firstActive,firstValid,firstBit,firstParity,firstWritten,firstMemory,firstFixed⟩ :=
      coordinate_exec B u v direction coordinate data progress.frame highWater (by omega) width progress.active
    have next := progress.step headFresh firstFrame firstActive firstValid firstBit firstParity firstWritten firstMemory
    have restFresh : ∀ other∈rest, other∉coordinate::done := by
      intro other member inDone
      rcases List.mem_cons.mp inDone with equal | previous
      · exact nd.1 (equal ▸ member)
      · exact fresh other (List.mem_cons_of_mem _ member) previous
    have restBudget : middle.1 Reserve.frontier+reserveSpace direction rest*WordRAM.precision B≤ highWater := by
      rw [firstFront]
      simpa only [reserveSpace,List.map_cons,List.sum_cons,Nat.add_mul,Nat.add_assoc] using budget
    obtain ⟨result,restCost,restRun,restBound,correct,resultFront,resultFixed,resultMemory⟩ :=
      ih (coordinate::done) middle nd.2 restFresh next restBudget
    refine ⟨result,firstCost+restCost,firstRun.seq restRun,?_,?_,?_,?_,?_⟩
    · simp only [List.length_cons]
      nlinarith only [firstBound,restBound]
    · simpa only [List.reverse_cons,List.append_assoc,List.cons_append,List.nil_append] using correct
    · rw [resultFront,firstFront]
      simp only [reserveSpace,List.map_cons,List.sum_cons,Nat.add_mul]
      omega
    · intro i high notFront notBase notActive notZero notIndex notAddress
      rw [resultFixed i high notFront notBase notActive notZero notIndex notAddress,
        firstFixed i high notFront notBase notActive notZero notIndex notAddress]
    · intro address below outside
      have pointer : middle.1 Collect.parities=data.1 Collect.parities := firstFrame.parities.trans progress.frame.parities.symm
      have middleBelow : address< middle.1 Reserve.frontier := by rw [firstFront]; omega
      rw [resultMemory address middleBelow (by rwa [pointer])]
      apply firstMemory address below
      have hi := coordinate.isLt
      rcases outside with before | after <;> omega

end LeanTrominoes.Domino.WordRAM.Binary.Candidate
