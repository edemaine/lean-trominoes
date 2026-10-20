/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.Graphs.Matching.BipartiteMatchingWordRAMPack
import LeanTrominoes.Graphs.Matching.BipartiteMatchingDenseWordRAMInput

/-! # Packed endpoint records are the literal cold matching input -/
namespace LeanTrominoes.BipartiteMatching.PackWordRAM
open ComplexityAbstract.RAM ImplicationGraph.TwoSATExpression

def headerMemory (memory : ℕ → ℤ) (n edges : ℕ) : ℕ → ℤ :=
  Function.update (Function.update (Function.update (Function.update memory 0 (3+2*edges : ℕ)) 1 (n : ℕ)) 2 (n : ℕ)) 3 (edges : ℕ)

def arraysMemory (memory : ℕ → ℤ) (source count : ℕ) : ℕ → ℤ :=
  prefixMemory (prefixMemory memory 4 (fun i => memory (source+i)) count)
    (4+count) (fun i => memory (source+count+i)) count

private theorem initial_left (input : DenseWordRAM.Input) (i : ℕ) (hi : i < input.2.2.length) :
    (initial (r:=64) (DenseWordRAM.encode input)).data.2 (4+i)=(input.2.2[i]).1.val := by
  simp [initial,State.data,DenseWordRAM.encode,DenseWordRAM.words,List.getElem?_append,
    List.getElem?_map,hi]
  rw [show 3+i=i+1+1+1 by omega]
  simp only [List.getElem?_cons_succ]
  rw [List.getElem?_append_left (by simpa using hi)]
  simp [hi]

private theorem initial_right (input : DenseWordRAM.Input) (i : ℕ) (hi : i < input.2.2.length) :
    (initial (r:=64) (DenseWordRAM.encode input)).data.2 (4+input.2.2.length+i)=(input.2.2[i]).2.val := by
  simp [initial,State.data,DenseWordRAM.encode,DenseWordRAM.words,List.getElem?_append,
    List.getElem?_map,hi]
  rw [show 4+input.2.2.length+i-1=(input.2.2.length+i)+1+1+1 by omega]
  simp only [List.getElem?_cons_succ]
  rw [List.getElem?_append_right (by simp)]
  simp [hi]

/-- Packing generated records uses exactly the original matching encoder;
there is no prepared index or decision answer in the input. -/
theorem packed_agrees (input : DenseWordRAM.Input) (memory : ℕ → ℤ) (source : ℕ)
    (square : input.2.1=input.1)
    (left : ∀ i, (hi : i < input.2.2.length) → memory (source+i)=(input.2.2[i]).1.val)
    (right : ∀ i, (hi : i < input.2.2.length) → memory (source+input.2.2.length+i)=(input.2.2[i]).2.val) :
    ∀ a, a < 4+2*input.2.2.length →
      headerMemory (arraysMemory memory source input.2.2.length) input.1 input.2.2.length a=
        (initial (r:=64) (DenseWordRAM.encode input)).data.2 a := by
  intro a within
  by_cases header : a < 4
  · interval_cases a <;>
      simp [headerMemory,initial,State.data,DenseWordRAM.encode,DenseWordRAM.words,square] <;> ring
  have headerFrame : headerMemory (arraysMemory memory source input.2.2.length) input.1 input.2.2.length a=
      arraysMemory memory source input.2.2.length a := by
    simp only [headerMemory,Function.update_apply]
    split_ifs <;> omega
  rw [headerFrame]
  by_cases first : a < 4+input.2.2.length
  · have hi : a-4 < input.2.2.length := by omega
    have address : a=4+(a-4) := by omega
    rw [address,initial_left input (a-4) hi]
    simp only [arraysMemory,prefixMemory]
    rw [ite_eq_right (by omega),ite_eq_left (by omega)]
    simpa only [Nat.add_sub_cancel_left] using left (a-4) hi
  · have hi : a-(4+input.2.2.length) < input.2.2.length := by omega
    have address : a=4+input.2.2.length+(a-(4+input.2.2.length)) := by omega
    rw [address,initial_right input _ hi]
    simp only [arraysMemory,prefixMemory]
    rw [ite_eq_left (by omega)]
    simpa only [Nat.add_sub_cancel_left] using right (a-(4+input.2.2.length)) hi

/-- All remaining words in the ordinary cold matching input are zero. -/
theorem initial_zero_after (input : DenseWordRAM.Input) :
    ∀ a, 4+2*input.2.2.length ≤ a →
      (initial (r:=64) (DenseWordRAM.encode input)).data.2 a=0 := by
  intro a outside
  simp only [initial,State.data]
  rw [if_neg (by omega)]
  have length : (DenseWordRAM.encode input).length=3+2*input.2.2.length := by
    simp only [DenseWordRAM.encode,List.length_map,DenseWordRAM.words_length]
  rw [List.getElem?_eq_none (by omega)]
  rfl

end LeanTrominoes.BipartiteMatching.PackWordRAM
