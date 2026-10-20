/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.SAT.Horn.HornWordRAMLayout

/-! # Contents of the Horn program's initialized arrays -/
namespace LeanTrominoes.Horn.WordRAM
open ComplexityAbstract.RAM

attribute [local simp] Reg.heap Reg.request Reg.allocated Reg.cursor Reg.zero Reg.one
  Reg.atoms Reg.rules Reg.occurrences Reg.heads Reg.edgeAtoms Reg.edgeRules Reg.seen
  Reg.buckets Reg.counters Reg.links Reg.stack Reg.index Reg.atom Reg.rule Reg.value
  Reg.top Reg.event Reg.scratch Reg.headValue Reg.output
  Allocation.frontier Allocation.count Allocation.result Allocation.cursor Allocation.zero Allocation.one
  header0 header1 header2 header3 header4 header5 header6 header7 header8 header9 header10
  prepared1 prepared2 prepared3 prepared4 prepared5 allocationState
  NaturalData.initialized NaturalData.allocated NaturalData.allocatedRegisters NaturalData.set

theorem clear_nat_apply (memory : ℕ → ℕ) (base count address : ℕ) :
    NaturalData.clear memory base count address=
      if base≤address ∧ address<base+count then 0 else memory address := by
  induction count generalizing memory base with
  | zero => simp [NaturalData.clear]
  | succ n ih =>
    rw [NaturalData.clear,ih]
    simp only [Function.update_apply]
    split_ifs <;> omega

/-- All three input arrays retain their original values; the five workspace
arrays start at zero. -/
def initialContents (input : Input) (slot : Slot) (i : ℕ) : ℕ :=
  if slot.val<3 then (initialData input).2 ((Layout.ofInput input).base slot+i) else 0

theorem preparedInput_pointers (input : Input) : (Layout.ofInput input).Pointers (preparedInput input) := by
  intro slot
  fin_cases slot <;>
    simp [preparedInput,pointer,Layout.ofInput,Layout.base,words_length,
      Nat.two_mul,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] <;> omega

theorem preparedInput_memory (input : Input) :
    (preparedInput input).2=
      NaturalData.clear
        (NaturalData.clear
          (NaturalData.clear
            (NaturalData.clear
              (NaturalData.clear (initialData input).2
                ((Layout.ofInput input).base Slot.seen) ((Layout.ofInput input).length Slot.seen))
              ((Layout.ofInput input).base Slot.buckets) ((Layout.ofInput input).length Slot.buckets))
            ((Layout.ofInput input).base Slot.counters) ((Layout.ofInput input).length Slot.counters))
          ((Layout.ofInput input).base Slot.links) ((Layout.ofInput input).length Slot.links))
        ((Layout.ofInput input).base Slot.stack) ((Layout.ofInput input).length Slot.stack) := by
  simp [preparedInput,Layout.ofInput,Layout.base,Layout.length,Slot.seen,Slot.buckets,Slot.counters,
    Slot.links,Slot.stack,words_length,Nat.two_mul,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm]
  all_goals repeat' first | omega | congr 1

theorem preparedInput_realizes (input : Input) :
    (Layout.ofInput input).Realizes (preparedInput input).2 (initialContents input) := by
  intro slot i within
  rw [preparedInput_memory]
  fin_cases slot <;>
    simp [initialContents,Layout.ofInput,Layout.base,Slot.seen,Slot.buckets,Slot.counters,
      Slot.links,Slot.stack,Layout.length,clear_nat_apply] at within ⊢ <;>
    first | omega | (split_ifs <;> first | rfl | omega)

end LeanTrominoes.Horn.WordRAM
