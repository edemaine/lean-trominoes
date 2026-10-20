/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.SAT.Horn.HornWordRAMStackArrays
import LeanTrominoes.SAT.Horn.HornWordRAMPropagation

/-! # The initial work stack agrees with Horn worklist semantics -/
namespace LeanTrominoes.Horn.WordRAM
open ComplexityAbstract.RAM

attribute [local simp] Slot.heads Slot.edgeAtoms Slot.edgeRules Slot.seen Slot.buckets Slot.counters Slot.links Slot.stack

def scanEntries (input : Input) (baseline : Tables) (k : ℕ) : List (Option (Fin input.1)) :=
  (((List.finRange input.2.rules.size).take k).filter
    (fun r => decide (baseline Slot.counters r.val=0))).map (Indexed.head input.2)

theorem scanEntries_length (input : Input) (baseline : Tables) (k : ℕ) :
    (scanEntries input baseline k).length≤k := by
  unfold scanEntries
  rw [List.length_map]
  exact (List.length_filter_le _ ((List.finRange input.2.rules.size).take k)).trans (List.length_take_le _ _)

theorem scanEntries_succ (input : Input) (baseline : Tables) (k : ℕ) (within : k< input.2.rules.size) :
    scanEntries input baseline (k+1)=
      if baseline Slot.counters k=0 then
        scanEntries input baseline k++[Indexed.head input.2 ⟨k,within⟩]
      else scanEntries input baseline k := by
  unfold scanEntries
  rw [List.take_succ_eq_append_getElem (by simpa using within)]
  simp only [List.filter_append,List.filter_cons,List.filter_nil,List.getElem_finRange,
    decide_eq_true_eq,List.map_append,List.map_cons,List.map_nil]
  split <;> simp_all

structure ScanRep (input : Input) (baseline : Tables) (k : ℕ) (data : Data) (contents : Tables) : Prop where
  realizes : (Layout.ofInput input).Realizes data.2 contents
  pointers : (Layout.ofInput input).Pointers data
  unchanged : ∀ slot, slot≠Slot.stack → contents slot=baseline slot
  stack : StackRep contents (scanEntries input baseline k)
  index : data.1 Reg.index=k
  top : data.1 Reg.top=(scanEntries input baseline k).length
  one : data.1 Reg.one=1
  zero : data.1 Reg.zero=0
  rules : data.1 Reg.rules=input.2.rules.size

theorem ScanRep.step (input : Input) (baseline contents : Tables) (k : ℕ) (data : Data)
    (before : ScanRep input baseline k data contents)
    (heads : ∀ r : Indexed.RuleId input.2, baseline Slot.heads r.val=atomCode (Indexed.head input.2 r))
    (within : k< input.2.rules.size) :
    ScanRep input baseline (k+1) (stackBodyState data)
      (stackContents contents k (scanEntries input baseline k).length) := by
  have room : (scanEntries input baseline k).length< input.2.rules.size :=
    (scanEntries_length input baseline k).trans_lt within
  have counters : contents Slot.counters=baseline Slot.counters := before.unchanged _ (by decide)
  have head : contents Slot.heads k=atomCode (Indexed.head input.2 ⟨k,within⟩) := by
    rw [before.unchanged Slot.heads (by decide)]
    exact heads ⟨k,within⟩
  have control := stackBody_control data
  refine ⟨(Layout.ofInput input).stackBody_realizes data contents before.realizes before.pointers
    k (scanEntries input baseline k).length before.index before.top before.zero within room,
    stackBody_pointers _ data before.pointers,?_,?_,?_,?_,
    control.2.1.trans before.one,control.2.2.1.trans before.zero,control.2.2.2.1.trans before.rules⟩
  · intro slot other
    unfold stackContents
    split
    · simpa only [Function.update_of_ne other] using before.unchanged slot other
    · exact before.unchanged slot other
  · rw [scanEntries_succ input baseline k within]
    unfold stackContents
    rw [counters]
    split
    · rw [head]
      exact before.stack.push contents _ _
    · exact before.stack
  · rw [control.1,before.index,before.one]
  · have pointer : data.1 Reg.counters=(Layout.ofInput input).base Slot.counters := before.pointers Slot.counters
    rw [stackBody_top,pointer,before.index,before.realizes Slot.counters k within,counters,
      before.zero,before.top,before.one,scanEntries_succ input baseline k within]
    split <;> simp

/-- Every reached scan state represents the filtered prefix of the rule
heads, with the stack pointer equal to the number of stored heads. -/
theorem scan_invariant (input : Input) (baseline : Tables)
    (realizes : (Layout.ofInput input).Realizes (indexedInput input).2 baseline)
    (pointers : (Layout.ofInput input).Pointers (indexedInput input))
    (tables : IndexTables input (Indexed.edges input.2).length baseline)
    (k : ℕ) (within : k≤ input.2.rules.size) :
    ∃ contents, ScanRep input baseline k
      ((stackBodyState^[k]) (stackStart (indexedInput input))) contents := by
  have heads (r : Indexed.RuleId input.2) : baseline Slot.heads r.val=atomCode (Indexed.head input.2 r) := by
    rw [tables.untouched Slot.heads (by decide) (by decide) (by decide)]
    exact initialContents_head input r
  induction k with
  | zero =>
    have controls := indexedInput_scalars input
    refine ⟨baseline,realizes,?_,?_,?_,?_,?_,?_,?_,?_⟩
    · exact (Layout.ofInput input).set_pointers _
        ((Layout.ofInput input).set_pointers _ pointers Reg.top (scalarRegister_of_large _ (by decide)) 0)
        Reg.index (scalarRegister_of_large _ (by decide)) 0
    · intros; rfl
    · simpa [scanEntries] using StackRep.empty (n := input.1) baseline
    · simp [stackStart,NaturalData.set]
    · simp [stackStart,NaturalData.set,scanEntries,Reg.top,Reg.index]
    · simpa [stackStart,NaturalData.set,Reg.top,Reg.index,Reg.one] using controls.2.2
    · simpa [stackStart,NaturalData.set,Reg.top,Reg.index,Reg.zero] using controls.2.1
    · simpa [stackStart,NaturalData.set,Reg.top,Reg.index,Reg.rules] using controls.1
  | succ k ih =>
    obtain ⟨contents,rep⟩ := ih (by omega)
    refine ⟨stackContents contents k (scanEntries input baseline k).length,?_⟩
    rw [Function.iterate_succ_apply']
    exact rep.step input baseline contents k _ heads (by omega)

/-- The stack's top-to-bottom order is exactly the reverse fact list used
by the verified stack worklist semantics. -/
theorem scanEntries_complete (input : Input) (baseline : Tables)
    (tables : IndexTables input (Indexed.edges input.2).length baseline) :
    (scanEntries input baseline input.2.rules.size).reverse=
      (Worklist.stackInitial (Indexed.edges input.2).reverse (Indexed.head input.2)).queue := by
  have counters (r : Indexed.RuleId input.2) : baseline Slot.counters r.val=
      (Worklist.index (Indexed.edges input.2).reverse).counter r := by
    simpa only [semanticIndex_complete] using tables.counters r
  have full : (List.finRange input.2.rules.size).take input.2.rules.size=List.finRange input.2.rules.size :=
    List.take_of_length_le (by simp)
  simp only [scanEntries,full,counters,Worklist.stackInitial,Worklist.initial,
    Worklist.initialWithIndex,Worklist.Enumeration.values]

end LeanTrominoes.Horn.WordRAM
