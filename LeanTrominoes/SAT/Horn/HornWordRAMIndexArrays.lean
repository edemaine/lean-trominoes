/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.SAT.Horn.HornWordRAMInitialization

/-! # Logical array effects of occurrence indexing

The instruction certificate and this theorem use the same `index10` state.
The theorem proves that its physical stores implement a link insertion and
counter increment, while preserving every other array cell.
-/
namespace LeanTrominoes.Horn.WordRAM
open ComplexityAbstract.RAM

def indexedContents (contents : Slot → ℕ → ℕ) (event atom rule : ℕ) : Slot → ℕ → ℕ :=
  let linked := Function.update contents Slot.links
    (Function.update (contents Slot.links) event (contents Slot.buckets atom))
  let bucketed := Function.update linked Slot.buckets
    (Function.update (linked Slot.buckets) atom (event+1))
  Function.update bucketed Slot.counters
    (Function.update (bucketed Slot.counters) rule (contents Slot.counters rule+1))

theorem index10_pointers (layout : Layout) (data : Data) (before : layout.Pointers data) :
    layout.Pointers (index10 data) := by
  intro slot
  rw [index10_registers]
  have index := scalarRegister_of_large Reg.index (by decide)
  have atom := scalarRegister_of_large Reg.atom (by decide)
  have rule := scalarRegister_of_large Reg.rule (by decide)
  have value := scalarRegister_of_large Reg.value (by decide)
  have scratch := scalarRegister_of_large Reg.scratch (by decide)
  simpa only [Function.update_of_ne (Ne.symm (index slot)),Function.update_of_ne (Ne.symm (scratch slot)),
    Function.update_of_ne (Ne.symm (value slot)),Function.update_of_ne (Ne.symm (rule slot)),
    Function.update_of_ne (Ne.symm (atom slot))] using before slot

/-- Each checked seventeen-instruction iteration performs exactly the usual
occurrence-index update on its logical arrays. -/
theorem index10_realizes (layout : Layout) (data : Data) (contents : Slot → ℕ → ℕ)
    (before : layout.Realizes data.2 contents) (pointers : layout.Pointers data)
    (event atom rule : ℕ) (idx : data.1 Reg.index=event) (unit : data.1 Reg.one=1)
    (eventBound : event<layout.events) (atomBound : atom<layout.numVars+1) (ruleBound : rule<layout.rules)
    (sourceAtom : contents Slot.edgeAtoms event=atom) (sourceRule : contents Slot.edgeRules event=rule) :
    layout.Realizes (index10 data).2 (indexedContents contents event atom rule) := by
  have ptrAtoms : data.1 Reg.edgeAtoms=layout.base Slot.edgeAtoms := pointers Slot.edgeAtoms
  have ptrRules : data.1 Reg.edgeRules=layout.base Slot.edgeRules := pointers Slot.edgeRules
  have ptrLinks : data.1 Reg.links=layout.base Slot.links := pointers Slot.links
  have ptrBuckets : data.1 Reg.buckets=layout.base Slot.buckets := pointers Slot.buckets
  have ptrCounters : data.1 Reg.counters=layout.base Slot.counters := pointers Slot.counters
  have atomValue : indexAtom data=atom := by
    unfold indexAtom
    rw [ptrAtoms,idx,before Slot.edgeAtoms event (by exact eventBound),sourceAtom]
  have ruleValue : indexRule data=rule := by
    unfold indexRule
    rw [ptrRules,idx,before Slot.edgeRules event (by exact eventBound),sourceRule]
  have bucketValue : data.2 (layout.base Slot.buckets+atom)=contents Slot.buckets atom :=
    before _ _ atomBound
  have counterNotBucket : layout.base Slot.counters+rule≠layout.base Slot.buckets+atom :=
    layout.disjoint _ _ (by decide) _ _ ruleBound atomBound
  have counterNotLink : layout.base Slot.counters+rule≠layout.base Slot.links+event :=
    layout.disjoint _ _ (by decide) _ _ ruleBound eventBound
  have counterValue : indexCounter data=contents Slot.counters rule := by
    simp only [indexCounter,indexBucketsMemory,indexLinksMemory,ptrCounters,ptrBuckets,ptrLinks,
      atomValue,ruleValue,idx,unit]
    rw [Function.update_of_ne counterNotBucket,Function.update_of_ne counterNotLink]
    exact before _ _ ruleBound
  let linked := Function.update contents Slot.links
    (Function.update (contents Slot.links) event (contents Slot.buckets atom))
  let bucketed := Function.update linked Slot.buckets
    (Function.update (linked Slot.buckets) atom (event+1))
  have link := layout.write_realizes data.2 contents before Slot.links event (contents Slot.buckets atom)
    (by exact eventBound)
  have bucket := layout.write_realizes _ linked link Slot.buckets atom (event+1) (by exact atomBound)
  have counter := layout.write_realizes _ bucketed bucket Slot.counters rule (contents Slot.counters rule+1)
    (by exact ruleBound)
  rw [index10_memory]
  simpa only [indexBucketsMemory,indexLinksMemory,ptrCounters,ptrBuckets,ptrLinks,
    atomValue,ruleValue,idx,unit,bucketValue,counterValue,indexedContents,linked,bucketed,
    Function.update_of_ne (show Slot.counters≠Slot.buckets by decide),
    Function.update_of_ne (show Slot.counters≠Slot.links by decide)] using counter

end LeanTrominoes.Horn.WordRAM
