/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.Tiling.Domino.DominoWordRAMGlobalScanCounters
import LeanTrominoes.Tiling.Domino.DominoWordRAMGlobalCandidate

/-! # The dynamic target loop in the original-input graph constructor -/
namespace LeanTrominoes.Domino.WordRAM.Driver
open ComplexityAbstract.RAM
open Binary
local notation "Data" => NaturalData 128

noncomputable def maxSpace (d : ℕ) := d*(Candidate.slotBound d+3)
noncomputable def targetStep (d : ℕ) (direction : Fin d) : Structured.Code 128 :=
  .seq (candidateBody d direction) (.atom (.arithmetic .add 65 65 82))
noncomputable def targetsProgram (d : ℕ) (direction : Fin d) : Structured.Code 128 :=
  .seq (.atom (.constant 65 0)) (.loop (.lt 65 66) (targetStep d direction))

 theorem targetsProgram_exec {n d base total bound H w : ℕ} (B : BasisData n d)
    (u : Fin n) (direction : Fin d) (prefixWords : List (ℕ×ℕ)) (data : Data)
    (state : GraphState B base total prefixWords data) (resources : GraphResources bound n d base total)
    (uInput : data.1 (64 : Fin 128)=u.val)
    (room : prefixWords.length+n*(2*2^d)≤ total)
    (budget : data.1 (74 : Fin 128)+n*maxSpace d*WordRAM.precision B≤ H)
    (word : Fits w bound) (heapWord : Fits w (FreshProbe.scalarBound (Candidate.slotBound d) H)) (heapBound : H≤ bound) :
    ∃ result cost, NaturalData.Exec w (targetsProgram d direction) data result cost ∧
      cost≤ n*(candidateCost d (WordRAM.precision B)+3)+3 ∧
      GraphState B base total (prefixWords++Order.targets B u direction (List.finRange n)) result ∧
      result.1 (64 : Fin 128)=u.val ∧
      result.1 (74 : Fin 128)≤ data.1 (74 : Fin 128)+n*maxSpace d*WordRAM.precision B := by
  have unit : Fits w (1:ℕ) := Allocation.nat_fits_le word (by have := resources.small; omega)
  have zero : Fits w (0:ℕ) := Allocation.nat_fits_le unit (by omega)
  have vertices := resources.vertices
  have positive : 1≤(2:ℕ)^d := Nat.one_le_two_pow
  have nBound : n≤ bound := by nlinarith only [vertices,positive]
  have nWord : Fits w n := Allocation.nat_fits_le word nBound
  let Invariant := fun i current =>
    GraphState B base total (prefixWords++Order.targets B u direction ((List.finRange n).take i)) current ∧
    current.1 (64:Fin 128)=u.val ∧
    current.1 (74:Fin 128)≤ data.1 (74:Fin 128)+i*maxSpace d*WordRAM.precision B
  have step : ∀ i, i< n → ∀ current, Controls (65:Fin 128) 66 current i n → Invariant i current →
      ∃ result cost, NaturalData.Exec w (targetStep d direction) current result cost ∧
        cost≤ candidateCost d (WordRAM.precision B)+1 ∧ Controls (65:Fin 128) 66 result (i+1) n ∧ Invariant (i+1) result := by
    intro i within current controls invariant
    have currentState := invariant.1
    have currentLength : (prefixWords++Order.targets B u direction ((List.finRange n).take i)).length=
        prefixWords.length+i*(2*2^d) := by
      rw [List.length_append,Order.targets_length,List.length_take,List.length_finRange,Nat.min_eq_left (Nat.le_of_lt within)]
    have stepBudget : current.1 (74:Fin 128)+Candidate.space direction*WordRAM.precision B≤ H := by
      have space := Nat.mul_le_mul_right (WordRAM.precision B) (Candidate.space_le direction)
      have grow := Nat.mul_le_mul_right (maxSpace d*WordRAM.precision B) (Nat.succ_le_of_lt within)
      have start := invariant.2.2
      change Candidate.space direction*WordRAM.precision B≤ maxSpace d*WordRAM.precision B at space
      nlinarith only [start,space,grow,budget]
    have stepRoom : (prefixWords++Order.targets B u direction ((List.finRange n).take i)).length+
        2*(PeriodicLatticeGraph.DoubleCover.phases d).length≤ total := by
      rw [currentLength]
      have grow := Nat.mul_le_mul_right (2*2^d) (Nat.succ_le_of_lt within)
      simpa using (show prefixWords.length+i*(2*2^d)+(2*2^d)≤ total by nlinarith only [grow,room])
    obtain ⟨middle,bodyCost,bodyRun,bodyBound,middleState,middleFront,middleFixed⟩ :=
      candidateBody_exec B u direction ⟨i,within⟩ _ current currentState resources invariant.2.1 controls.1 stepRoom stepBudget word heapWord heapBound
    have v : middle.1 (65:Fin 128)=i := (middleFixed _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans controls.1
    have uKeep : middle.1 (64:Fin 128)=u.val := (middleFixed _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans invariant.2.1
    have increment := NaturalData.add_exec middle (65:Fin 128) 65 82
      (by rw [v,middleState.unit]; exact Allocation.nat_fits_le nWord (by omega))
    let result := middle.set (65:Fin 128) (i+1)
    have incrementRun : NaturalData.Exec w (.atom (.arithmetic .add 65 65 82)) middle result 1 := by
      simpa only [result,v,middleState.unit] using increment
    have nextState := middleState.set_counter (65:Fin 128) (Or.inr rfl) (i+1)
    refine ⟨result,bodyCost+1,bodyRun.seq incrementRun,by omega,?_,?_,?_,?_⟩
    · simp [Controls,result,NaturalData.set,middleState.vertices]
    · simpa only [Invariant,Order.take_finRange_step i within,Order.targets_append,Order.targets,
        List.flatMap_append,List.flatMap_cons,List.flatMap_nil,List.append_nil,List.append_assoc,phaseWords,Order.block,result] using nextState
    · simpa [result,NaturalData.set] using uKeep
    · change middle.1 (74:Fin 128)≤_
      rw [middleFront]
      have start := invariant.2.2
      have space := Nat.mul_le_mul_right (WordRAM.precision B) (Candidate.space_le direction)
      change Candidate.space direction*WordRAM.precision B≤ maxSpace d*WordRAM.precision B at space
      nlinarith only [start,space]
  let initial := data.set (65:Fin 128) 0
  have initialState := state.set_counter (65:Fin 128) (Or.inr rfl) 0
  have initialInvariant : Invariant 0 initial := by
    refine ⟨?_,?_,?_⟩
    · simpa [Order.targets] using initialState
    · simpa [initial,NaturalData.set] using uInput
    · simp [initial,NaturalData.set]
  obtain ⟨result,loopCost,loopRun,loopBound,finalControls,final⟩ := loop_exec (65:Fin 128) 66 (targetStep d direction) n
    (candidateCost d (WordRAM.precision B)+1) Invariant step n 0 (by omega) initial
    (by simp [Controls,initial,NaturalData.set,state.vertices]) initialInvariant
  have reset := NaturalData.constant_exec data (65:Fin 128) 0 zero
  refine ⟨result,1+loopCost,reset.seq loopRun,?_,?_,final.2.1,?_⟩
  · nlinarith only [loopBound]
  · simpa only [Order.targets_complete] using final.1
  · simpa only [zero_add] using final.2.2

end LeanTrominoes.Domino.WordRAM.Driver
