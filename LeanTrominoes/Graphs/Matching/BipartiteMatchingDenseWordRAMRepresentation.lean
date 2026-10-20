/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.Graphs.Matching.BipartiteMatchingDenseWordRAMLayout
import LeanTrominoes.Graphs.Matching.BipartiteMatchingDenseRewire

/-! # Physical representation of finite matchings and discovered path rows -/
namespace LeanTrominoes.BipartiteMatching.DenseWordRAM
open ComplexityAbstract.RAM

def optionCode {n : Nat} : Option (Fin n) → Nat
  | none => 0
  | some vertex => vertex.val+1

def lengthCode {L R : Type*} : Option (List (L × R)) → Nat
  | none => 0
  | some prior => prior.length+1

structure MemoryRep (input : Input) (matching : State (Fin input.1) (Fin input.2.1))
    (paths : DenseSearch.Paths (Fin input.1) (Fin input.2.1)) (memory : Nat → Nat) : Prop where
  edgeLeft : ∀ i : Fin input.2.2.length,
    memory ((Layout.ofInput input).base Slot.edgeLeft+i.val)=(input.2.2.get i).1.val
  edgeRight : ∀ i : Fin input.2.2.length,
    memory ((Layout.ofInput input).base Slot.edgeRight+i.val)=(input.2.2.get i).2.val
  partnerLeft : ∀ l : Fin input.1,
    memory ((Layout.ofInput input).base Slot.partnerLeft+l.val)=optionCode (matching.left l)
  partnerRight : ∀ r : Fin input.2.1,
    memory ((Layout.ofInput input).base Slot.partnerRight+r.val)=optionCode (matching.right r)
  lengths : ∀ l : Fin input.1,
    memory ((Layout.ofInput input).base Slot.lengths+l.val)=lengthCode (paths l)
  rowLeft : ∀ l prior, paths l=some prior → ∀ j : Fin prior.length,
    memory ((Layout.ofInput input).base Slot.rowLeft+(l.val*input.1+j.val))=(prior.get j).1.val
  rowRight : ∀ l prior, paths l=some prior → ∀ j : Fin prior.length,
    memory ((Layout.ofInput input).base Slot.rowRight+(l.val*input.1+j.val))=(prior.get j).2.val

structure Representation (input : Input) (matching : State (Fin input.1) (Fin input.2.1))
    (paths : DenseSearch.Paths (Fin input.1) (Fin input.2.1)) (data : Data) : Prop where
  pointers : (Layout.ofInput input).Pointers data
  n : data.1 Reg.n=input.1
  m : data.1 Reg.m=input.2.1
  edges : data.1 Reg.edges=input.2.2.length
  one : data.1 Reg.one=1
  zero : data.1 Reg.zero=0
  memory : MemoryRep input matching paths data.2

theorem path_length_bound {L R : Type*} [DecidableEq L] [DecidableEq R] [Fintype L]
    {adj : L → R → Prop} {matching : State L R} {paths : DenseSearch.Paths L R}
    (inv : DenseSearch.Invariant adj matching paths) (l : L) (prior : List (L × R))
    (marked : paths l=some prior) : prior.length+1≤Fintype.card L := by
  have simple := inv.simple l prior marked
  have bound : (prior.map Prod.fst++[l]).length≤Fintype.card L := by
    rw [← List.toFinset_card_of_nodup simple]
    exact Finset.card_le_univ _
  simpa using bound

theorem optionCode_bound {n : Nat} (value : Option (Fin n)) : optionCode value≤n := by
  cases value with
  | none => simp [optionCode]
  | some v => dsimp [optionCode]; have := v.isLt; omega

theorem lengthCode_bound {n m : Nat} {matching : State (Fin n) (Fin m)}
    {adj : Fin n → Fin m → Prop} {paths : DenseSearch.Paths (Fin n) (Fin m)}
    (inv : DenseSearch.Invariant adj matching paths) (l : Fin n) : lengthCode (paths l)≤n := by
  cases marked : paths l with
  | none => simp [lengthCode]
  | some prior => simpa [lengthCode] using path_length_bound inv l prior marked

theorem optionCode_zero_iff {n : Nat} (value : Option (Fin n)) : optionCode value=0 ↔ value=none := by
  cases value <;> simp [optionCode]

theorem lengthCode_zero_iff {L R : Type*} (value : Option (List (L × R))) :
    lengthCode value=0 ↔ value=none := by
  cases value <;> simp [lengthCode]

theorem optionCode_some {n : Nat} (value : Option (Fin n)) (vertex : Fin n) :
    optionCode value=vertex.val+1 ↔ value=some vertex := by
  cases value with
  | none => simp [optionCode]
  | some other => simp [optionCode,Fin.ext_iff]

theorem Representation.set_scalar (input : Input) (matching : State (Fin input.1) (Fin input.2.1))
    (paths : DenseSearch.Paths (Fin input.1) (Fin input.2.1)) (data : Data)
    (rep : Representation input matching paths data) (reg : Fin 64) (value : Nat)
    (scalar : ScalarRegister reg) (safe : reg≠Reg.n ∧ reg≠Reg.m ∧ reg≠Reg.edges ∧ reg≠Reg.one ∧ reg≠Reg.zero) :
    Representation input matching paths (data.set reg value) := by
  refine ⟨(Layout.ofInput input).set_pointers data rep.pointers reg scalar value,?_,?_,?_,?_,?_,rep.memory⟩
  · simpa [NaturalData.set,Ne.symm safe.1] using rep.n
  · simpa [NaturalData.set,Ne.symm safe.2.1] using rep.m
  · simpa [NaturalData.set,Ne.symm safe.2.2.1] using rep.edges
  · simpa [NaturalData.set,Ne.symm safe.2.2.2.1] using rep.one
  · simpa [NaturalData.set,Ne.symm safe.2.2.2.2] using rep.zero

end LeanTrominoes.BipartiteMatching.DenseWordRAM
