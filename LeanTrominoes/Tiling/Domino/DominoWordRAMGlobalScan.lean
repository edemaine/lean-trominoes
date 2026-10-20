/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.Tiling.Domino.DominoWordRAMGlobalScanDirections

/-! # Complete operational source/direction/target graph scan -/
namespace LeanTrominoes.Domino.WordRAM.Driver
open ComplexityAbstract.RAM
open Binary
local notation "Data" => NaturalData 128

noncomputable def sourceStep (d : ℕ) : Structured.Code 128 :=
  .seq (directionsProgram d) (.atom (.arithmetic .add 64 64 82))
noncomputable def scanProgram (d : ℕ) : Structured.Code 128 :=
  .seq (.atom (.constant 64 0)) (.loop (.lt 64 66) (sourceStep d))

 theorem scanProgram_exec {n d base total bound H w : ℕ} (B : BasisData n d)
    (prefixWords : List (ℕ×ℕ)) (data : Data)
    (state : GraphState B base total prefixWords data) (resources : GraphResources bound n d base total)
    (room : prefixWords.length+n*d*n*(2*2^d)≤ total)
    (budget : data.1 (74:Fin 128)+n*n*d*maxSpace d*WordRAM.precision B≤ H)
    (word : Fits w bound) (heapWord : Fits w (FreshProbe.scalarBound (Candidate.slotBound d) H)) (heapBound : H≤ bound) :
    ∃ result cost, NaturalData.Exec w (scanProgram d) data result cost ∧
      cost≤ n*(d*(n*(candidateCost d (WordRAM.precision B)+3)+3)+4)+3 ∧
      GraphState B base total (prefixWords++Order.sources B (List.finRange n)) result ∧
      result.1 (64:Fin 128)=n ∧
      result.1 (74:Fin 128)≤ data.1 (74:Fin 128)+n*n*d*maxSpace d*WordRAM.precision B := by
  have unit : Fits w (1:ℕ) := Allocation.nat_fits_le word (by have := resources.small; omega)
  have zero : Fits w (0:ℕ) := Allocation.nat_fits_le unit (by omega)
  have vertices := resources.vertices
  have positive : 1≤(2:ℕ)^d := Nat.one_le_two_pow
  have nBound : n≤ bound := by nlinarith only [vertices,positive]
  have nWord : Fits w n := Allocation.nat_fits_le word nBound
  let Invariant := fun i current =>
    GraphState B base total (prefixWords++Order.sources B ((List.finRange n).take i)) current ∧
    current.1 (74:Fin 128)≤ data.1 (74:Fin 128)+i*d*n*maxSpace d*WordRAM.precision B
  have step : ∀ i, i< n → ∀ current, Controls (64:Fin 128) 66 current i n → Invariant i current →
      ∃ result cost, NaturalData.Exec w (sourceStep d) current result cost ∧
        cost≤ d*(n*(candidateCost d (WordRAM.precision B)+3)+3)+2 ∧
        Controls (64:Fin 128) 66 result (i+1) n ∧ Invariant (i+1) result := by
    intro i within current controls invariant
    have currentState := invariant.1
    have currentLength : (prefixWords++Order.sources B ((List.finRange n).take i)).length=
        prefixWords.length+i*d*n*(2*2^d) := by
      rw [List.length_append,Order.sources_length,List.length_take,List.length_finRange,Nat.min_eq_left (Nat.le_of_lt within)]
    have stepRoom : (prefixWords++Order.sources B ((List.finRange n).take i)).length+d*n*(2*2^d)≤ total := by
      rw [currentLength]
      have grow := Nat.mul_le_mul_right (d*n*(2*2^d)) (Nat.succ_le_of_lt within)
      nlinarith only [grow,room]
    have stepBudget : current.1 (74:Fin 128)+d*n*maxSpace d*WordRAM.precision B≤ H := by
      have grow := Nat.mul_le_mul_right (d*n*maxSpace d*WordRAM.precision B) (Nat.succ_le_of_lt within)
      have frontier := invariant.2
      nlinarith only [grow,frontier,budget]
    obtain ⟨middle,rowCost,rowRun,rowBound,middleState,uKeep,middleFront⟩ := directionsProgram_exec B ⟨i,within⟩ _ current
      currentState resources controls.1 stepRoom stepBudget word heapWord heapBound
    have increment := NaturalData.add_exec middle (64:Fin 128) 64 82
      (by rw [uKeep,middleState.unit]; exact Allocation.nat_fits_le nWord (by omega))
    let result := middle.set (64:Fin 128) (i+1)
    have incrementRun : NaturalData.Exec w (.atom (.arithmetic .add 64 64 82)) middle result 1 := by
      simpa only [result,uKeep,middleState.unit] using increment
    have nextState := middleState.set_counter (64:Fin 128) (Or.inl rfl) (i+1)
    refine ⟨result,rowCost+1,rowRun.seq incrementRun,by omega,?_,?_,?_⟩
    · simp [Controls,result,NaturalData.set,middleState.vertices]
    · simpa only [Order.take_finRange_step i within,Order.sources_append,Order.sources,List.flatMap_append,
        List.flatMap_cons,List.flatMap_nil,List.append_nil,List.append_assoc,result] using nextState
    · change middle.1 (74:Fin 128)≤_
      have frontier := invariant.2
      nlinarith only [frontier,middleFront]
  let initial := data.set (64:Fin 128) 0
  have initialState := state.set_counter (64:Fin 128) (Or.inl rfl) 0
  have initialInvariant : Invariant 0 initial := by
    refine ⟨?_,?_⟩
    · simpa [Order.sources] using initialState
    · simp [initial,NaturalData.set]
  obtain ⟨result,loopCost,loopRun,loopBound,finalControls,final⟩ := loop_exec (64:Fin 128) 66 (sourceStep d) n
    (d*(n*(candidateCost d (WordRAM.precision B)+3)+3)+2) Invariant step n 0 (by omega) initial
    (by simp [Controls,initial,NaturalData.set,state.vertices]) initialInvariant
  have reset := NaturalData.constant_exec data (64:Fin 128) 0 zero
  refine ⟨result,1+loopCost,reset.seq loopRun,?_,?_,finalControls.1,?_⟩
  · nlinarith only [loopBound]
  · have all : (List.finRange n).take n=List.finRange n := by simpa only [List.length_finRange] using List.take_length (l:=List.finRange n)
    simpa only [all] using final.1
  · have frontier := final.2
    nlinarith only [frontier]

end LeanTrominoes.Domino.WordRAM.Driver
