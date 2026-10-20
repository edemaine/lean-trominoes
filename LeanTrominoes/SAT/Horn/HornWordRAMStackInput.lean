/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.SAT.Horn.HornWordRAMStackBounds

/-! # Executing Horn stack initialization from the original input -/
namespace LeanTrominoes.Horn.WordRAM
open ComplexityAbstract.RAM

attribute [local simp] Reg.heap Reg.request Reg.allocated Reg.cursor Reg.zero Reg.one Reg.atoms
  Reg.rules Reg.occurrences Reg.heads Reg.edgeAtoms Reg.edgeRules Reg.seen Reg.buckets Reg.counters
  Reg.links Reg.stack Reg.index Reg.atom Reg.rule Reg.value Reg.top Reg.event Reg.scratch Reg.headValue Reg.output

theorem indexState_preserves (input : Input) (k : ℕ) (r : Fin 32)
    (hi : r≠Reg.index) (ha : r≠Reg.atom) (hr : r≠Reg.rule)
    (hv : r≠Reg.value) (hs : r≠Reg.scratch) :
    (indexState input k).1 r=(preparedInput input).1 r := by
  induction k with
  | zero => simp [indexState,NaturalData.set,hi]
  | succ k ih =>
    rw [indexState_succ,index10_registers]
    simpa only [Function.update_of_ne hi,Function.update_of_ne ha,Function.update_of_ne hr,
      Function.update_of_ne hv,Function.update_of_ne hs] using ih

private theorem preparedInput_scalars (input : Input) :
    (preparedInput input).1 Reg.rules=input.2.rules.size ∧ (preparedInput input).1 Reg.zero=0 := by
  simp [preparedInput,prepared5,prepared4,prepared3,prepared2,prepared1,allocationState,
    header10,header9,header8,header7,header6,header5,header4,header3,header2,header1,header0,
    NaturalData.initialized,NaturalData.allocated,NaturalData.allocatedRegisters,NaturalData.set,
    Allocation.frontier,Allocation.count,Allocation.result,Allocation.cursor,Allocation.zero,Allocation.one]

theorem indexedInput_scalars (input : Input) :
    (indexedInput input).1 Reg.rules=input.2.rules.size ∧ (indexedInput input).1 Reg.zero=0 ∧
    (indexedInput input).1 Reg.one=1 := by
  have rules := indexState_preserves input (Indexed.edges input.2).length Reg.rules
    (by decide) (by decide) (by decide) (by decide) (by decide)
  have zero := indexState_preserves input (Indexed.edges input.2).length Reg.zero
    (by decide) (by decide) (by decide) (by decide) (by decide)
  have one := (indexState_control input (Indexed.edges input.2).length).2.1
  exact ⟨rules.trans (preparedInput_scalars input).1,zero.trans (preparedInput_scalars input).2,one⟩

def indexedBound (input : Input) : ℕ :=
  indexBound (preparedBound input) (Indexed.edges input.2).length

theorem indexedInput_bounded (input : Input) :
    NaturalData.Bounded (indexedBound input) (indexedInput input) := by
  have before := preparedInput_bounded input
  have control := prepared5_controls (initialData input) (words input).length input.1
    input.2.rules.size (Indexed.edges input.2).length
  have one : ((preparedInput input).set Reg.index 0).1 Reg.one=1 := by
    simpa [preparedInput,NaturalData.set] using control.1
  have occurrences : ((preparedInput input).set Reg.index 0).1 Reg.occurrences=(Indexed.edges input.2).length := by
    simpa [preparedInput,NaturalData.set] using control.2
  exact index_prefix_bounded ((preparedInput input).set Reg.index 0)
    (before.set Reg.index (Nat.zero_le _)) one (by simp [NaturalData.set]) _ (by rw [occurrences])

theorem indexedBound_polynomial (input : Input) : indexedBound input≤1728*(size input+1)^3 := by
  have before : preparedBound input≤6*size input := by
    dsimp [preparedBound,prepareEnd,size]
    rw [words_length]
    omega
  have occurrences : (Indexed.edges input.2).length≤preparedBound input := by
    dsimp [preparedBound,prepareEnd]
    omega
  have bound := indexBound_polynomial (preparedBound input) (Indexed.edges input.2).length occurrences
  have power := Nat.pow_le_pow_left (show preparedBound input+1≤6*(size input+1) by omega) 3
  dsimp [indexedBound]
  calc
    indexBound (preparedBound input) (Indexed.edges input.2).length≤8*(preparedBound input+1)^3 := bound
    _≤8*(6*(size input+1))^3 := Nat.mul_le_mul_left _ power
    _=1728*(size input+1)^3 := by ring

theorem input_stack_bound (input : Input) :
    64*stackBound (indexedBound input) input.2.rules.size≤262144*(size input+1)^4 := by
  let T := size input+1
  have rule : input.2.rules.size≤size input := by dsimp [size]; omega
  have b := indexedBound_polynomial input
  have small : (size input+1)^2≤(size input+1)^4 :=
    Nat.pow_le_pow_right (by omega) (by omega)
  have bound : stackBound (indexedBound input) input.2.rules.size≤1730*(size input+1)^4 := by
    calc
      stackBound (indexedBound input) input.2.rules.size=
          (input.2.rules.size+1)*indexedBound input+2*input.2.rules.size*(input.2.rules.size+1) := by
            dsimp [stackBound]; ring
      _≤(size input+1)*(1728*(size input+1)^3)+2*(size input+1)*(size input+1) :=
        Nat.add_le_add (Nat.mul_le_mul (by omega) b)
          (Nat.mul_le_mul (Nat.mul_le_mul_left 2 (by omega)) (by omega))
      _=1728*(size input+1)^4+2*(size input+1)^2 := by ring
      _≤1730*(size input+1)^4 := by omega
  omega

def stackedInput (input : Input) : Data := stackedState (indexedInput input)

/-- Stack initialization executes for every sufficiently large logarithmic
word size; the input encoding and program are unchanged. -/
theorem initialStack_on_input {w : ℕ} (input : Input)
    (width : 27*Nat.log2 (size input+2)+2≤w) :
    NaturalData.Exec w initialStack (indexedInput input) (stackedInput input)
      (initialStackCost (indexedInput input)) := by
  apply initialStack_exec (indexedInput_bounded input) (indexedInput_scalars input).2.2
  rw [(indexedInput_scalars input).1]
  apply WordBounds.polynomial_fits_uniform 262144 4 (size input) w
  · have log : Nat.log2 (262144+1)=18 := by decide
    simp only [log,Nat.reduceMul,Nat.reduceAdd]
    omega
  · simpa only [Int.natAbs_natCast] using input_stack_bound input

end LeanTrominoes.Horn.WordRAM
