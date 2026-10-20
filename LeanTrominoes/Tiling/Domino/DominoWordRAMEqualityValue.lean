/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.Tiling.Domino.DominoWordRAMEquality
import LeanTrominoes.Tiling.Domino.DominoWordRAMValues

/-! # A digit equality scan tests equality of the represented integers -/
namespace LeanTrominoes.Domino.WordRAM.Binary

theorem value_eq_iff (memory : ℕ → ℕ) (first second length : ℕ)
    (firstBits : ∀ j< length, memory (first+j)≤1)
    (secondBits : ∀ j< length, memory (second+j)≤1) :
    value memory first length=value memory second length ↔ ∀ j< length, memory (first+j)=memory (second+j) := by
  constructor
  · intro equal
    induction length generalizing first second with
    | zero => simp
    | succ length ih =>
      rw [value_head memory first length,value_head memory second length] at equal
      have firstBit := firstBits 0 (by omega)
      have secondBit := secondBits 0 (by omega)
      simp only [Nat.add_zero] at firstBit secondBit
      have head : memory first=memory second := by omega
      have tails : value memory (first+1) length=value memory (second+1) length := by omega
      have tailBitsFirst : ∀ j< length, memory (first+1+j)≤1 := by
        intro j hj
        have bit := firstBits (j+1) (by omega)
        simpa only [Nat.add_assoc,Nat.add_comm 1 j] using bit
      have tailBitsSecond : ∀ j< length, memory (second+1+j)≤1 := by
        intro j hj
        have bit := secondBits (j+1) (by omega)
        simpa only [Nat.add_assoc,Nat.add_comm 1 j] using bit
      have rest := ih (first+1) (second+1) tailBitsFirst tailBitsSecond tails
      intro j hj
      cases j with
      | zero => simpa using head
      | succ j =>
        have bit := rest j (by omega)
        simpa only [Nat.add_assoc,Nat.add_comm 1 j] using bit
  · intro same
    unfold value
    apply Finset.sum_congr rfl
    intro j hj
    rw [same j (Finset.mem_range.mp hj)]

namespace Equality
open ComplexityAbstract.RAM

theorem program_value_exec {w : ℕ} (p : Layout) (data : Data)
    (length : data.1 Reg.length=p.length) (first : data.1 Reg.first=p.first) (second : data.1 Reg.second=p.second)
    (first_bits : ∀ j< p.length, data.2 (p.first+j)≤1) (second_bits : ∀ j< p.length, data.2 (p.second+j)≤1)
    (small : Fits w (1:ℕ)) (firstFits : Fits w (p.first+p.length : ℕ))
    (secondFits : Fits w (p.second+p.length : ℕ)) (lengthFits : Fits w p.length) :
    ∃ result cost, NaturalData.Exec w program data result cost ∧ cost≤10*p.length+5 ∧
      Represents p data.2 p.length result ∧
      (result.1 Reg.carry=1 ↔ value data.2 p.first p.length=value data.2 p.second p.length) := by
  obtain ⟨result,cost,run,bound,correct⟩ := program_exec p data length first second first_bits second_bits small firstFits secondFits lengthFits
  refine ⟨result,cost,run,bound,correct,?_⟩
  rw [correct.agreement]
  exact (value_eq_iff data.2 p.first p.second p.length first_bits second_bits).symm

end Equality
end LeanTrominoes.Domino.WordRAM.Binary
