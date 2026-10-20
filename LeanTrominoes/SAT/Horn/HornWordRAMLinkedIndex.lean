/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.SAT.Horn.HornWordRAMInputTables

/-! # The linked occurrence index built in physical RAM memory

A chain is a certificate for following the program's one-based occurrence
pointers. In particular, it proves that every dereference is within the
allocated occurrence array. Inserting a fresh node preserves all old chains.
-/
namespace LeanTrominoes.Horn.WordRAM

inductive Chain (limit : ℕ) (links labels : ℕ → ℕ) : ℕ → List ℕ → Prop
  | nil : Chain limit links labels 0 []
  | cons (i : ℕ) (within : i<limit) (rest : List ℕ)
      (tail : Chain limit links labels (links i) rest) :
      Chain limit links labels (i+1) (labels i::rest)

theorem Chain.pointer_bound {limit links labels pointer values}
    (chain : Chain limit links labels pointer values) : pointer≤limit := by
  cases chain <;> omega

theorem Chain.zero_iff {limit links labels pointer values}
    (chain : Chain limit links labels pointer values) : pointer=0 ↔ values=[] := by
  cases chain <;> simp

/-- Changing fresh or out-of-range cells does not change a certified chain. -/
theorem Chain.frame {limit links labels pointer values}
    (chain : Chain limit links labels pointer values) (larger : ℕ) (le : limit≤larger)
    (newLinks newLabels : ℕ → ℕ)
    (link : ∀ i, i<limit → newLinks i=links i)
    (label : ∀ i, i<limit → newLabels i=labels i) :
    Chain larger newLinks newLabels pointer values := by
  induction chain with
  | nil => exact .nil
  | cons i within rest tail ih =>
    rw [← label i within]
    apply Chain.cons i (by omega)
    simpa only [link i within] using ih

/-- A single load of a nonzero pointer yields the next rule and chain. -/
theorem Chain.nonzero {limit links labels pointer values}
    (chain : Chain limit links labels pointer values) (nonzero : pointer≠0) :
    ∃ rest, pointer-1<limit ∧ values=labels (pointer-1)::rest ∧
      Chain limit links labels (links (pointer-1)) rest := by
  cases chain with
  | nil => contradiction
  | cons i within rest tail => exact ⟨rest,by simpa using within,by simp,by simpa using tail⟩

abbrev Tables := Slot → ℕ → ℕ

/-- The semantic index processes the occurrence stream in reverse because
physical indexing pushes each new occurrence onto its atom's bucket. -/
def semanticIndex (input : Input) (processed : ℕ) :=
  Worklist.index ((Indexed.edges input.2).take processed).reverse

structure IndexTables (input : Input) (processed : ℕ) (contents : Tables) : Prop where
  untouched : ∀ slot, slot≠Slot.links → slot≠Slot.buckets → slot≠Slot.counters →
    contents slot=initialContents input slot
  buckets : ∀ a : Option (Fin input.1),
    Chain processed (contents Slot.links) (contents Slot.edgeRules)
      (contents Slot.buckets (atomCode a))
      (((semanticIndex input processed).bucket a).map Fin.val)
  counters : ∀ r : Indexed.RuleId input.2,
    contents Slot.counters r.val=(semanticIndex input processed).counter r

theorem initialContents_indexTables (input : Input) : IndexTables input 0 (initialContents input) := by
  constructor
  · intros; rfl
  · intro a
    simpa [initialContents,Slot.buckets,semanticIndex,Worklist.index] using
      (Chain.nil (limit := 0) (links := initialContents input Slot.links)
        (labels := initialContents input Slot.edgeRules))
  · intro r
    simp [initialContents,Slot.counters,semanticIndex,Worklist.index]

theorem semanticIndex_succ (input : Input) (k : ℕ) (within : k<(Indexed.edges input.2).length) :
    semanticIndex input (k+1)=
      ⟨Function.update (semanticIndex input k).bucket (Indexed.edges input.2)[k].1
          ((Indexed.edges input.2)[k].2::(semanticIndex input k).bucket (Indexed.edges input.2)[k].1),
        Function.update (semanticIndex input k).counter (Indexed.edges input.2)[k].2
          ((semanticIndex input k).counter (Indexed.edges input.2)[k].2+1)⟩ := by
  unfold semanticIndex
  rw [List.take_succ_eq_append_getElem within,List.reverse_append]
  rfl

attribute [local simp] Slot.heads Slot.edgeAtoms Slot.edgeRules Slot.seen Slot.buckets
  Slot.counters Slot.links Slot.stack

@[simp] theorem indexedContents_links (c : Tables) (event atom rule : ℕ) :
    indexedContents c event atom rule Slot.links=
      Function.update (c Slot.links) event (c Slot.buckets atom) := by simp [indexedContents]

@[simp] theorem indexedContents_buckets (c : Tables) (event atom rule : ℕ) :
    indexedContents c event atom rule Slot.buckets=
      Function.update (c Slot.buckets) atom (event+1) := by simp [indexedContents]

@[simp] theorem indexedContents_counters (c : Tables) (event atom rule : ℕ) :
    indexedContents c event atom rule Slot.counters=
      Function.update (c Slot.counters) rule (c Slot.counters rule+1) := by simp [indexedContents]

@[simp] theorem indexedContents_edgeRules (c : Tables) (event atom rule : ℕ) :
    indexedContents c event atom rule Slot.edgeRules=c Slot.edgeRules := by simp [indexedContents]

theorem IndexTables.step (input : Input) (k : ℕ) (contents : Tables)
    (before : IndexTables input k contents) (within : k<(Indexed.edges input.2).length) :
    IndexTables input (k+1)
      (indexedContents contents k (atomCode (Indexed.edges input.2)[k].1)
        (Indexed.edges input.2)[k].2.val) := by
  have labels : contents Slot.edgeRules k=(Indexed.edges input.2)[k].2.val := by
    rw [before.untouched Slot.edgeRules (by decide) (by decide) (by decide)]
    exact initialContents_edgeRule input k within
  constructor
  · intro slot link bucket counter
    simp only [indexedContents,Function.update_of_ne counter,
      Function.update_of_ne bucket,Function.update_of_ne link]
    exact before.untouched slot link bucket counter
  · intro a
    have old := before.buckets a
    have framed := old.frame (k+1) (by omega)
      (Function.update (contents Slot.links) k (contents Slot.buckets (atomCode (Indexed.edges input.2)[k].1)))
      (contents Slot.edgeRules)
      (fun i hi => Function.update_of_ne (by omega : i≠k) _ _) (fun _ _ => rfl)
    simp only [indexedContents_links,indexedContents_buckets,indexedContents_edgeRules,
      semanticIndex_succ input k within]
    by_cases same : a=(Indexed.edges input.2)[k].1
    · subst a
      simp only [Function.update_self,List.map_cons]
      rw [← labels]
      apply Chain.cons k (by omega)
      simpa only [Function.update_self] using framed
    · have codes : atomCode a≠atomCode (Indexed.edges input.2)[k].1 :=
        fun h => same (atomCode_injective h)
      simpa only [Function.update_of_ne same,Function.update_of_ne codes] using framed
  · intro r
    simp only [indexedContents_counters,semanticIndex_succ input k within]
    by_cases same : r=(Indexed.edges input.2)[k].2
    · subst r
      simpa only [Function.update_self] using congrArg (·+1) (before.counters (Indexed.edges input.2)[k].2)
    · have codes : r.val≠(Indexed.edges input.2)[k].2.val := fun h => same (Fin.ext h)
      simpa only [Function.update_of_ne same,Function.update_of_ne codes] using before.counters r

end LeanTrominoes.Horn.WordRAM
