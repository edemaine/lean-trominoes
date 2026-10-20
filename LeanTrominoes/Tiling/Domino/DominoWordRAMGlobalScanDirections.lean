/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.Tiling.Domino.DominoWordRAMGlobalScanTargets

/-! # The fixed sequence of positive coordinate directions -/
namespace LeanTrominoes.Domino.WordRAM.Driver
open ComplexityAbstract.RAM
open Binary
local notation "Data" => NaturalData 128

noncomputable def directionsProgram (d : ℕ) : Structured.Code 128 :=
  sequence (82:Fin 128) (targetsProgram d) (List.finRange d)

 theorem directionsProgram_exec {n d base total bound H w : ℕ} (B : BasisData n d)
    (u : Fin n) (prefixWords : List (ℕ×ℕ)) (data : Data)
    (state : GraphState B base total prefixWords data) (resources : GraphResources bound n d base total)
    (uInput : data.1 (64:Fin 128)=u.val)
    (room : prefixWords.length+d*n*(2*2^d)≤ total)
    (budget : data.1 (74:Fin 128)+d*n*maxSpace d*WordRAM.precision B≤ H)
    (word : Fits w bound) (heapWord : Fits w (FreshProbe.scalarBound (Candidate.slotBound d) H)) (heapBound : H≤ bound) :
    ∃ result cost, NaturalData.Exec w (directionsProgram d) data result cost ∧
      cost≤ d*(n*(candidateCost d (WordRAM.precision B)+3)+3)+1 ∧
      GraphState B base total (prefixWords++Order.directions B u (List.finRange d)) result ∧
      result.1 (64:Fin 128)=u.val ∧
      result.1 (74:Fin 128)≤ data.1 (74:Fin 128)+d*n*maxSpace d*WordRAM.precision B := by
  have unit : Fits w (1:ℕ) := Allocation.nat_fits_le word (by have := resources.small; omega)
  let Invariant := fun done current =>
    GraphState B base total (prefixWords++Order.directions B u done) current ∧
    current.1 (64:Fin 128)=u.val ∧
    current.1 (74:Fin 128)≤ data.1 (74:Fin 128)+done.length*n*maxSpace d*WordRAM.precision B
  have initial : Invariant [] data := by refine ⟨?_,uInput,by simp⟩; simpa [Order.directions] using state
  have step : ∀ done direction rest, done++direction::rest=List.finRange d → ∀ current, Invariant done current →
      ∃ result cost, NaturalData.Exec w (targetsProgram d direction) current result cost ∧
        cost≤ n*(candidateCost d (WordRAM.precision B)+3)+3 ∧ Invariant (done++[direction]) result := by
    intro done direction rest complete current invariant
    have lengths := congrArg List.length complete
    simp only [List.length_append,List.length_cons,List.length_finRange] at lengths
    have row : done.length+1≤ d := by omega
    have currentLength : (prefixWords++Order.directions B u done).length=prefixWords.length+done.length*n*(2*2^d) := by
      rw [List.length_append,Order.directions_length]
    have roomRow : (prefixWords++Order.directions B u done).length+n*(2*2^d)≤ total := by
      rw [currentLength]
      have scaled := Nat.mul_le_mul_right (n*(2*2^d)) row
      nlinarith only [scaled,room]
    have budgetRow : current.1 (74:Fin 128)+n*maxSpace d*WordRAM.precision B≤ H := by
      have scaled := Nat.mul_le_mul_right (n*maxSpace d*WordRAM.precision B) row
      have frontier := invariant.2.2
      nlinarith only [scaled,frontier,budget]
    obtain ⟨result,cost,run,bound,next,uKeep,frontier⟩ := targetsProgram_exec B u direction _ current invariant.1 resources
      invariant.2.1 roomRow budgetRow word heapWord heapBound
    refine ⟨result,cost,run,bound,?_,uKeep,?_⟩
    · simpa only [Order.directions_append,Order.directions,List.flatMap_append,List.flatMap_cons,List.flatMap_nil,List.append_nil,List.append_assoc] using next
    · have prior := invariant.2.2
      simp only [List.length_append,List.length_singleton]
      nlinarith only [prior,frontier]
  obtain ⟨result,cost,run,bound,final⟩ := sequence_exec (82:Fin 128) (targetsProgram d) (List.finRange d)
    (n*(candidateCost d (WordRAM.precision B)+3)+3) Invariant unit
    (by intro done current invariant; exact invariant.1.unit) step (List.finRange d) [] (by simp) data initial
  refine ⟨result,cost,run,?_,final.1,final.2.1,?_⟩
  · simpa only [List.length_finRange,Nat.mul_comm] using bound
  · simpa only [List.length_finRange] using final.2.2

end LeanTrominoes.Domino.WordRAM.Driver
