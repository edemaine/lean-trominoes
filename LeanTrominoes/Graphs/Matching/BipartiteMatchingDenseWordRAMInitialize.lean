/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.Graphs.Matching.BipartiteMatchingDenseWordRAMRepresentation
import LeanTrominoes.Graphs.Matching.BipartiteMatchingDenseWordRAMSemantics
import LeanTrominoes.Graphs.Matching.BipartiteMatchingDenseWordRAMCopy

/-! # Reinitializing search roots by ordinary array writes -/
namespace LeanTrominoes.BipartiteMatching.DenseWordRAM
open ComplexityAbstract.RAM

def PathsBound (input : Input) (paths : DenseSearch.Paths (Fin input.1) (Fin input.2.1)) : Prop :=
  ∀ l prior, paths l=some prior → prior.length≤ input.1

theorem MemoryRep.emptyPath (input : Input) (matching : State (Fin input.1) (Fin input.2.1))
    (paths : DenseSearch.Paths (Fin input.1) (Fin input.2.1)) (memory : Nat → Nat)
    (rep : MemoryRep input matching paths memory) (bound : PathsBound input paths)
    (vertex : Fin input.1) (value : Option (List (Fin input.1 × Fin input.2.1)))
    (empty : ∀ prior, value=some prior → prior=[]) :
    MemoryRep input matching (Function.update paths vertex value)
      (Function.update memory ((Layout.ofInput input).base Slot.lengths+vertex.val) (lengthCode value)) := by
  let a := Layout.ofInput input
  have unchanged (slot : Slot) (i : Nat) (within : i<a.length slot) (different : slot≠Slot.lengths) :
      Function.update memory (a.base Slot.lengths+vertex.val) (lengthCode value) (a.base slot+i)=memory (a.base slot+i) := by
    exact Function.update_of_ne (a.disjoint slot Slot.lengths different i vertex.val within vertex.isLt) _ _
  constructor
  · intro i
    rw [unchanged Slot.edgeLeft i.val i.isLt (by decide)]
    exact rep.edgeLeft i
  · intro i
    rw [unchanged Slot.edgeRight i.val i.isLt (by decide)]
    exact rep.edgeRight i
  · intro l
    rw [unchanged Slot.partnerLeft l.val l.isLt (by decide)]
    exact rep.partnerLeft l
  · intro r
    rw [unchanged Slot.partnerRight r.val r.isLt (by decide)]
    exact rep.partnerRight r
  · intro l
    by_cases same : l=vertex
    · subst l; simp
    · have different : (Layout.ofInput input).base Slot.lengths+l.val≠(Layout.ofInput input).base Slot.lengths+vertex.val := by
        intro equal
        exact same (Fin.ext (by omega))
      simpa [Function.update_of_ne same,Function.update_of_ne different] using rep.lengths l
  · intro l prior marked j
    by_cases same : l=vertex
    · subst l
      have nil := empty prior (by simpa using marked)
      subst prior
      exact Fin.elim0 j
    · have old : paths l=some prior := by simpa [Function.update_of_ne same] using marked
      have jbound : j.val< input.1 := by have := bound l prior old; have := j.isLt; omega
      rw [unchanged Slot.rowLeft (l.val*input.1+j.val) (row_index_bound l.isLt jbound) (by decide)]
      exact rep.rowLeft l prior old j
  · intro l prior marked j
    by_cases same : l=vertex
    · subst l
      have nil := empty prior (by simpa using marked)
      subst prior
      exact Fin.elim0 j
    · have old : paths l=some prior := by simpa [Function.update_of_ne same] using marked
      have jbound : j.val< input.1 := by have := bound l prior old; have := j.isLt; omega
      rw [unchanged Slot.rowRight (l.val*input.1+j.val) (row_index_bound l.isLt jbound) (by decide)]
      exact rep.rowRight l prior old j

attribute [local simp] Reg.one Reg.zero Reg.n Reg.m Reg.edges Reg.partnerLeft Reg.lengths Reg.index Reg.value Reg.scratch

def initialize1 (d : Data) := readState d Reg.partnerLeft Reg.index Reg.value
def initialize2 (d : Data) :=
  if (initialize1 d).1 Reg.value=(initialize1 d).1 Reg.zero then
    writeState (initialize1 d) Reg.lengths Reg.index Reg.one
  else writeState (initialize1 d) Reg.lengths Reg.index Reg.zero

def initializeState (d : Data) := (initialize2 d).set Reg.index (d.1 Reg.index+d.1 Reg.one)
def initializeCost (d : Data) := if (initialize1 d).1 Reg.value=(initialize1 d).1 Reg.zero then 6 else 7

theorem initializeCost_bound (d : Data) : initializeCost d≤7 := by unfold initializeCost; split <;> omega

attribute [local simp] initialize1 initialize2 initializeState readState writeState NaturalData.set NaturalData.store

theorem initializeBody_exec {B : Nat} (d : Data) (before : NaturalData.Bounded B d)
    (addressLeft : d.1 Reg.partnerLeft+d.1 Reg.index≤B) (addressLength : d.1 Reg.lengths+d.1 Reg.index≤B)
    (incrementFits : d.1 Reg.index+d.1 Reg.one≤B) :
    Natural.Exec B initializeBody d (initializeState d) (initializeCost d) := by
  have first : Natural.Exec B (read Reg.partnerLeft Reg.index Reg.value) d (initialize1 d) 2 :=
    native_read _ _ _ _ addressLeft (before.2 _)
  have bounded := first.bounded before
  have after : Natural.Exec B
      (.branch (.eq Reg.value Reg.zero) (write Reg.lengths Reg.index Reg.one) (write Reg.lengths Reg.index Reg.zero))
      (initialize1 d) (initialize2 d) (initializeCost d-3) := by
    by_cases free : (initialize1 d).1 Reg.value=(initialize1 d).1 Reg.zero
    · have written := native_write (initialize1 d) Reg.lengths Reg.index Reg.one (by decide)
        (by simpa using addressLength) (bounded.1 _)
      have branch := Natural.Exec.branch_yes (no := write Reg.lengths Reg.index Reg.zero)
        (show Natural.Holds (.eq Reg.value Reg.zero) (initialize1 d) from free) written
      simpa only [initialize2,initializeCost,free,ite_true,Nat.reduceSub,Nat.reduceAdd] using branch
    · have written := native_write (initialize1 d) Reg.lengths Reg.index Reg.zero (by decide)
        (by simpa using addressLength) (bounded.1 _)
      have branch := Natural.Exec.branch_no (yes := write Reg.lengths Reg.index Reg.one)
        (show ¬Natural.Holds (.eq Reg.value Reg.zero) (initialize1 d) from free) written
      simpa only [initialize2,initializeCost,free,ite_false,Nat.reduceSub,Nat.reduceAdd] using branch
  have idx2 : (initialize2 d).1 Reg.index=d.1 Reg.index := by unfold initialize2; split <;> simp
  have one2 : (initialize2 d).1 Reg.one=d.1 Reg.one := by unfold initialize2; split <;> simp
  have last : Natural.Exec B (increment Reg.index) (initialize2 d) (initializeState d) 1 := by
    simpa only [increment,add,initializeState,idx2,one2] using Natural.Exec.atom
      (Natural.Step.add (bound := B) (initialize2 d) Reg.index Reg.index Reg.one
        (by rw [idx2,one2]; exact incrementFits))
  have cost : 2+(initializeCost d-3+1)=initializeCost d := by unfold initializeCost; split <;> omega
  simpa only [initializeBody,cost] using first.seq (after.seq last)

end LeanTrominoes.BipartiteMatching.DenseWordRAM
