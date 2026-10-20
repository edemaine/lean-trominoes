/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.Graphs.Matching.BipartiteMatchingDenseWordRAMInput
import LeanTrominoes.Graphs.Matching.BipartiteMatchingDenseWordRAMRepresentation

/-! # Original edge tables and freshly zeroed workspace memory -/
namespace LeanTrominoes.BipartiteMatching.DenseWordRAM
open ComplexityAbstract.RAM
attribute [local simp] Reg.heap Reg.request Reg.allocated Reg.cursor Reg.zero Reg.one
  Reg.n Reg.m Reg.edges Reg.edgeLeft Reg.edgeRight Reg.partnerLeft Reg.partnerRight
  Reg.lengths Reg.rowLeft Reg.rowRight Reg.cells Reg.scratch
  Allocation.frontier Allocation.count Allocation.result Allocation.cursor Allocation.zero Allocation.one
  header0 header1 header2 header3 header4 header5 header6 header7 header8 header9
  prepared1 prepared2 prepared3 prepared4 prepared5 allocationState
  NaturalData.initialized NaturalData.allocated NaturalData.allocatedRegisters NaturalData.set

theorem clear_nat_apply (memory : Nat → Nat) (base count address : Nat) :
    NaturalData.clear memory base count address=if base≤address ∧ address<base+count then 0 else memory address := by
  induction count generalizing memory base with
  | zero => simp [NaturalData.clear]
  | succ n ih =>
    rw [NaturalData.clear,ih]
    simp only [Function.update_apply]
    split_ifs <;> omega

def initialContents (input : Input) (slot : Slot) (i : Nat) : Nat :=
  if slot.val<2 then (initialData input).2 ((Layout.ofInput input).base slot+i) else 0

theorem preparedInput_memory (input : Input) :
    (preparedInput input).2=
      NaturalData.clear
        (NaturalData.clear
          (NaturalData.clear
            (NaturalData.clear
              (NaturalData.clear (initialData input).2
                ((Layout.ofInput input).base Slot.partnerLeft) ((Layout.ofInput input).length Slot.partnerLeft))
              ((Layout.ofInput input).base Slot.partnerRight) ((Layout.ofInput input).length Slot.partnerRight))
            ((Layout.ofInput input).base Slot.lengths) ((Layout.ofInput input).length Slot.lengths))
          ((Layout.ofInput input).base Slot.rowLeft) ((Layout.ofInput input).length Slot.rowLeft))
        ((Layout.ofInput input).base Slot.rowRight) ((Layout.ofInput input).length Slot.rowRight) := by
  simp [preparedInput,Layout.ofInput,Layout.base,Layout.length,Slot.partnerLeft,Slot.partnerRight,
    Slot.lengths,Slot.rowLeft,Slot.rowRight,words_length,Nat.two_mul,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm]

theorem preparedInput_realizes (input : Input) :
    (Layout.ofInput input).Realizes (preparedInput input).2 (initialContents input) := by
  intro slot i within
  rw [preparedInput_memory]
  fin_cases slot <;>
    simp [initialContents,Layout.ofInput,Layout.base,Layout.length,Slot.partnerLeft,Slot.partnerRight,
      Slot.lengths,Slot.rowLeft,Slot.rowRight,clear_nat_apply] at within ⊢ <;>
    first | omega | (split_ifs <;> first | rfl | omega)

private theorem word_slice (input : Input) (prior values rest : List Nat)
    (table : words input=prior++values++rest) (i : Nat) (within : i<values.length) :
    (initialData input).2 (prior.length+1+i)=values[i] := by
  have address : prior.length+1+i≠0 := by omega
  simp only [initialData,address,ite_false]
  have offset : prior.length+1+i-1=prior.length+i := by omega
  rw [offset,table,List.append_assoc,List.getElem?_append_right (by omega)]
  simp [List.getElem?_append_left within,List.getElem?_eq_getElem within]

theorem initialContents_edgeLeft (input : Input) (i : Fin input.2.2.length) :
    initialContents input Slot.edgeLeft i.val=(input.2.2.get i).1.val := by
  have read := word_slice input [input.1,input.2.1,input.2.2.length]
    (input.2.2.map (fun e => e.1.val)) (input.2.2.map (fun e => e.2.val)) rfl i.val (by simpa using i.isLt)
  simpa [initialContents,Layout.ofInput,Layout.base,Slot.edgeLeft] using read

theorem initialContents_edgeRight (input : Input) (i : Fin input.2.2.length) :
    initialContents input Slot.edgeRight i.val=(input.2.2.get i).2.val := by
  have read := word_slice input ([input.1,input.2.1,input.2.2.length]++input.2.2.map (fun e => e.1.val))
    (input.2.2.map (fun e => e.2.val)) [] (by simp [words]) i.val (by simpa using i.isLt)
  simpa [initialContents,Layout.ofInput,Layout.base,Slot.edgeRight,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using read

theorem preparedInput_represents (input : Input) :
    Representation input empty (fun _ => none) (preparedInput input) := by
  refine ⟨preparedInput_pointers input,(preparedInput_controls input).1,(preparedInput_controls input).2.1,
    (preparedInput_controls input).2.2.1,(preparedInput_controls input).2.2.2.1,(preparedInput_controls input).2.2.2.2,?_⟩
  constructor
  · intro i
    exact (preparedInput_realizes input Slot.edgeLeft i.val i.isLt).trans (initialContents_edgeLeft input i)
  · intro i
    exact (preparedInput_realizes input Slot.edgeRight i.val i.isLt).trans (initialContents_edgeRight input i)
  · intro l
    simpa [initialContents,Slot.partnerLeft,optionCode,empty] using preparedInput_realizes input Slot.partnerLeft l.val l.isLt
  · intro r
    simpa [initialContents,Slot.partnerRight,optionCode,empty] using preparedInput_realizes input Slot.partnerRight r.val r.isLt
  · intro l
    simpa [initialContents,Slot.lengths,lengthCode] using preparedInput_realizes input Slot.lengths l.val l.isLt
  · intro l prior marked
    contradiction
  · intro l prior marked
    contradiction

end LeanTrominoes.BipartiteMatching.DenseWordRAM
