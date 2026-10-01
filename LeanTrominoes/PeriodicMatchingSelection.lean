/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.PeriodicMatchingIndex

/-! # One-pass selection of the matched protoedges

The returned table stores references into the input edge records. Arbitrary
coordinate vectors and parallel protoedges require no search or arithmetic.
The matching at every lattice translate is described by this finite table.
-/
namespace LeanTrominoes.PeriodicBipartite
variable {L R : Type*} {d : Nat} [DecidableEq L] [DecidableEq R] [Fintype L] [Fintype R]

def select (matching : BipartiteMatching.State L R) : List (Edge L R d) → L → Option (Edge L R d)
  | [] => fun _ => none
  | e::es =>
    let old := select matching es
    if matching.left e.left=some e.right then Function.update old e.left (some e) else old

/-- Twelve primitive operations per edge suffice, including the conditional write. -/
def executeSelect (matching : BipartiteMatching.State L R) : List (Edge L R d) → (L → Option (Edge L R d)) × Nat
  | [] => (fun _ => none,1)
  | e::es =>
    let old := executeSelect matching es
    (if matching.left e.left=some e.right then Function.update old.1 e.left (some e) else old.1,old.2+12)

theorem executeSelect_table (matching : BipartiteMatching.State L R) (edges : List (Edge L R d)) :
    (executeSelect matching edges).1=select matching edges := by
  induction edges <;> simp_all [executeSelect,select]

theorem executeSelect_cost (matching : BipartiteMatching.State L R) (edges : List (Edge L R d)) :
    (executeSelect matching edges).2=12*edges.length+1 := by
  induction edges <;> simp_all [executeSelect] <;> omega

theorem select_some (matching : BipartiteMatching.State L R) (edges : List (Edge L R d))
    (l : L) (e : Edge L R d) (selected : select matching edges l=some e) :
    e ∈ edges ∧ e.left=l ∧ matching.left l=some e.right := by
  induction edges with
  | nil => simp [select] at selected
  | cons a es ih =>
    by_cases paired : matching.left a.left=some a.right
    · by_cases equal : l=a.left
      · subst l
        have same : a=e := by simpa [select,paired] using selected
        subst e
        exact ⟨List.mem_cons_self,rfl,paired⟩
      · have old : select matching es l=some e := by simpa [select,paired,equal] using selected
        obtain ⟨member,left,mate⟩ := ih old
        exact ⟨List.mem_cons_of_mem _ member,left,mate⟩
    · have old : select matching es l=some e := by simpa [select,paired] using selected
      obtain ⟨member,left,mate⟩ := ih old
      exact ⟨List.mem_cons_of_mem _ member,left,mate⟩

theorem select_none (matching : BipartiteMatching.State L R) (edges : List (Edge L R d)) (l : L) :
    select matching edges l=none ↔ ∀ e ∈ edges, e.left=l → matching.left l ≠ some e.right := by
  induction edges with
  | nil => simp [select]
  | cons a es ih =>
    by_cases paired : matching.left a.left=some a.right
    · by_cases equal : l=a.left
      · subst l; simp [select,paired]
      · simp only [select,paired,if_true,Function.update_of_ne equal,ih,List.mem_cons]
        constructor
        · intro old e member left
          rcases member with same | member
          · subst e; exact (equal left.symm).elim
          · exact old e member left
        · intro all e member; exact all e (Or.inr member)
    · simp only [select,paired,if_false,ih,List.mem_cons]
      constructor
      · intro old e member left
        rcases member with same | member
        · subst e; rwa [← left]
        · exact old e member left
      · intro all e member; exact all e (Or.inr member)

def TableSpec (edges : List (Edge L R d)) (table : L → Option (Edge L R d)) : Prop :=
  ∃ f : (L × Lattice d) ≃ (R × Lattice d),
    (∀ u, Adj edges u (f u)) ∧ TranslationInvariant f ∧
    ∀ l z, ∃ e, table l=some e ∧ f (l,z)=(e.right,z+e.offset)

theorem select_complete (matching : BipartiteMatching.State L R) (edges : List (Edge L R d))
    (supported : BipartiteMatching.Supported (fun l r => r ∈ buckets edges l) matching)
    (full : BipartiteMatching.Full matching) (l : L) : ∃ e, select matching edges l=some e := by
  apply Option.ne_none_iff_exists'.mp
  intro none
  obtain ⟨r,paired⟩ := Option.ne_none_iff_exists'.mp (full l)
  obtain ⟨e,member,left,right⟩ := (buckets_mem edges l r).mp (supported l r paired)
  exact (select_none matching edges l).mp none e member left (by rwa [right])

theorem select_period_one (matching : BipartiteMatching.State L R) (edges : List (Edge L R d))
    (consistent : BipartiteMatching.Consistent matching)
    (supported : BipartiteMatching.Supported (fun l r => r ∈ buckets edges l) matching)
    (full : BipartiteMatching.Full matching) (balanced : Fintype.card L=Fintype.card R) :
    TableSpec edges (select matching edges) := by
  classical
  choose chosen selected using select_complete matching edges supported full
  have facts (l : L) := select_some matching edges l (chosen l) (selected l)
  have injective : Function.Injective (fun l => (chosen l).right) := by
    intro l k equal
    change (chosen l).right=(chosen k).right at equal
    have one := (consistent l (chosen l).right).mp (facts l).2.2
    have two := (consistent k (chosen k).right).mp (facts k).2.2
    rw [← equal] at two
    exact Option.some.inj (one.symm.trans two)
  let f : L ≃ R := Equiv.ofBijective (fun l => (chosen l).right)
    ((Fintype.bijective_iff_injective_and_card _).mpr ⟨injective,balanced⟩)
  refine ⟨lift f (fun l => (chosen l).offset),?_,lift_translation f _,?_⟩
  · intro u
    exact ⟨chosen u.1,(facts u.1).1,(facts u.1).2.1,rfl,rfl⟩
  · intro l z
    exact ⟨chosen l,selected l,rfl⟩

theorem TableSpec.period_one (edges : List (Edge L R d)) (table : L → Option (Edge L R d))
    (valid : TableSpec edges table) : HasPeriodOneMatching edges := by
  obtain ⟨f,supported,invariant,_⟩ := valid
  exact ⟨f,supported,invariant⟩

end LeanTrominoes.PeriodicBipartite
