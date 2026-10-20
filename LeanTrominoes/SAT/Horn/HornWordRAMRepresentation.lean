/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.SAT.Horn.HornWordRAMInitializationCorrect

/-! # Representation relation at the Horn propagation boundary -/
namespace LeanTrominoes.Horn.WordRAM
open ComplexityAbstract.RAM

abbrev HornState (input : Input) := Worklist.State (Option (Fin input.1)) (Indexed.RuleId input.2)

def startState (input : Input) : HornState input :=
  Worklist.stackInitial (Indexed.edges input.2).reverse (Indexed.head input.2)

/-- Every field refers either to the original rules or to actual allocated
cells. Functions and lists in this relation are ghost data used in the proof. -/
structure MachineRep (input : Input) (state : HornState input) (data : Data) (contents : Tables) : Prop where
  realizes : (Layout.ofInput input).Realizes data.2 contents
  pointers : (Layout.ofInput input).Pointers data
  heads : ∀ r : Indexed.RuleId input.2, contents Slot.heads r.val=atomCode (Indexed.head input.2 r)
  buckets : ∀ a : Option (Fin input.1),
    Chain (Indexed.edges input.2).length (contents Slot.links) (contents Slot.edgeRules)
      (contents Slot.buckets (atomCode a))
      (((Worklist.index (Indexed.edges input.2).reverse).bucket a).map Fin.val)
  counters : ∀ r : Indexed.RuleId input.2, contents Slot.counters r.val=state.counter r
  seen : ∀ a : Option (Fin input.1), contents Slot.seen (atomCode a)=if state.seen a then 1 else 0
  stack : StackRep contents state.queue.reverse
  top : data.1 Reg.top=state.queue.length
  one : data.1 Reg.one=1
  zero : data.1 Reg.zero=0

/-- This representation is established by the executed initialization prefix,
without precomputing any worklist information in the input encoding. -/
theorem stackedInput_represents (input : Input) :
    ∃ contents, MachineRep input (startState input) (stackedInput input) contents := by
  obtain ⟨baseline,contents,tables,scan,queue⟩ := initialization_correct input
  refine ⟨contents,scan.realizes,scan.pointers,?_,?_,?_,?_,?_,?_,scan.one,scan.zero⟩
  · intro r
    rw [scan.unchanged Slot.heads (by decide),tables.untouched Slot.heads (by decide) (by decide) (by decide)]
    exact initialContents_head input r
  · intro a
    rw [scan.unchanged Slot.links (by decide),scan.unchanged Slot.edgeRules (by decide),
      scan.unchanged Slot.buckets (by decide)]
    simpa only [semanticIndex_complete] using tables.buckets a
  · intro r
    rw [scan.unchanged Slot.counters (by decide)]
    simpa only [startState,Worklist.stackInitial,Worklist.initial,Worklist.initialWithIndex,
      semanticIndex_complete] using tables.counters r
  · intro a
    rw [scan.unchanged Slot.seen (by decide),tables.untouched Slot.seen (by decide) (by decide) (by decide)]
    simp [initialContents,Slot.seen,startState,Worklist.stackInitial,Worklist.initial,Worklist.initialWithIndex]
  · change StackRep contents (startState input).queue.reverse
    have order : (startState input).queue=(scanEntries input baseline input.2.rules.size).reverse := queue.symm
    rw [order,List.reverse_reverse]
    exact scan.stack
  · change (stackedInput input).1 Reg.top=(startState input).queue.length
    have order : (startState input).queue=(scanEntries input baseline input.2.rules.size).reverse := queue.symm
    rw [order,List.length_reverse]
    exact scan.top

/-- All words at the propagation boundary obey one polynomial bound. -/
theorem stackedInput_bounded (input : Input) :
    NaturalData.Bounded (stackBound (indexedBound input) input.2.rules.size) (stackedInput input) := by
  have before := indexedInput_bounded input
  have start : NaturalData.Bounded (indexedBound input) (stackStart (indexedInput input)) :=
    (before.set Reg.top (Nat.zero_le _)).set Reg.index (Nat.zero_le _)
  have one : (stackStart (indexedInput input)).1 Reg.one=1 := by
    simpa [stackStart,NaturalData.set,Reg.top,Reg.index,Reg.one] using (indexedInput_scalars input).2.2
  have bound := stack_prefix_bounded (stackStart (indexedInput input)) start one
    (by simp [stackStart,NaturalData.set]) (by simp [stackStart,NaturalData.set,Reg.top,Reg.index])
    input.2.rules.size input.2.rules.size (by omega)
  simpa only [stackedInput,stackedState,(indexedInput_scalars input).1] using bound

end LeanTrominoes.Horn.WordRAM
