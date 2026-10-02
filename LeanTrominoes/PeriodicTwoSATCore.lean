/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.PeriodicImplicationReach

/-! # Periodic binary clauses and their implication graph in any dimension

An absent clause is empty; duplicate literals encode units. Arbitrary offsets
are allowed here. Locality is imposed only by the polynomial-time theorem.
-/
namespace LeanTrominoes.PeriodicTwoSAT
open PeriodicLatticeGraph ImplicationGraph
variable {V : Type*} {d : Nat}
abbrev Signed (V : Type*) := V × Bool
abbrev Literal (V : Type*) (d : Nat) := Signed V × Lattice d
abbrev Clause (V : Type*) (d : Nat) := Option (Literal V d × Literal V d)
abbrev Formula (V : Type*) (d : Nat) := List (Clause V d)

def negate (a : Signed V) : Signed V := (a.1,!a.2)
theorem negate_involutive : Function.Involutive (@negate V) := by rintro ⟨a,b⟩; simp [negate]

def Truth (model : V → Lattice d → Prop) (a : Signed V) (z : Lattice d) : Prop :=
  if a.2 then model a.1 z else ¬ model a.1 z

theorem truth_negate (model : V → Lattice d → Prop) (a : Signed V) (z : Lattice d) :
    Truth model (negate a) z ↔ ¬ Truth model a z := by
  obtain ⟨v,b⟩ := a
  cases b <;> simp [Truth,negate]

def Holds (model : V → Lattice d → Prop) (z : Lattice d) : Clause V d → Prop
  | none => False
  | some (a,b) => Truth model a.1 (z+a.2) ∨ Truth model b.1 (z+b.2)
def Satisfies (formula : Formula V d) (model : V → Lattice d → Prop) : Prop :=
  ∀ c ∈ formula, ∀ z, Holds model z c
def Satisfiable (formula : Formula V d) : Prop := ∃ model, Satisfies formula model

def clauseArcs : Clause V d → List (Arc (Signed V) d)
  | none => []
  | some (a,b) => [⟨negate a.1,b.1,b.2-a.2⟩,⟨negate b.1,a.1,a.2-b.2⟩]
def arcs (formula : Formula V d) := formula.flatMap clauseArcs

theorem arcs_skew (formula : Formula V d) : SkewArcs (arcs formula) negate := by
  intro e member
  obtain ⟨c,hc,he⟩ := List.mem_flatMap.mp member
  cases c with
  | none => simp [clauseArcs] at he
  | some pair =>
    obtain ⟨a,b⟩ := pair
    rcases (by simpa [clauseArcs] using he : e=⟨negate a.1,b.1,b.2-a.2⟩ ∨ e=⟨negate b.1,a.1,a.2-b.2⟩) with rfl | rfl
    all_goals apply List.mem_flatMap.mpr; refine ⟨some (a,b),hc,?_⟩
    all_goals simp [clauseArcs,skewArc,negate,neg_sub]

def graph (formula : Formula V d) := implicationReach (arcs formula) negate negate_involutive (arcs_skew formula)

private theorem clause_edge (formula : Formula V d) (a b : Literal V d) (member : some (a,b) ∈ formula)
    (z : Lattice d) : Adj (arcs formula) (negate a.1,z+a.2) (b.1,z+b.2) := by
  refine ⟨⟨negate a.1,b.1,b.2-a.2⟩,List.mem_flatMap.mpr ⟨some (a,b),member,by simp [clauseArcs]⟩,rfl,rfl,?_⟩
  change z+b.2=(z+a.2)+(b.2-a.2)
  abel

private theorem model_edge (formula : Formula V d) (model : V → Lattice d → Prop)
    (satisfied : Satisfies formula model) {u v : Signed V × Lattice d}
    (edge : Adj (arcs formula) u v) (trueSource : Truth model u.1 u.2) : Truth model v.1 v.2 := by
  obtain ⟨e,he,source,target,displacement⟩ := edge
  obtain ⟨c,hc,he⟩ := List.mem_flatMap.mp he
  cases c with
  | none => simp [clauseArcs] at he
  | some pair =>
    obtain ⟨a,b⟩ := pair
    rcases (by simpa [clauseArcs] using he : e=⟨negate a.1,b.1,b.2-a.2⟩ ∨ e=⟨negate b.1,a.1,a.2-b.2⟩) with rfl | rfl
    · have clause := satisfied (some (a,b)) hc (u.2-a.2)
      change Truth model a.1 (u.2-a.2+a.2) ∨ Truth model b.1 (u.2-a.2+b.2) at clause
      have coordinate : u.2-a.2+b.2=v.2 := by rw [displacement]; abel
      rw [sub_add_cancel,coordinate] at clause
      have negA : ¬ Truth model a.1 u.2 := (truth_negate model a.1 u.2).mp (by change negate a.1=u.1 at source; rw [source]; exact trueSource)
      exact target ▸ clause.resolve_left negA
    · have clause := satisfied (some (a,b)) hc (u.2-b.2)
      change Truth model a.1 (u.2-b.2+a.2) ∨ Truth model b.1 (u.2-b.2+b.2) at clause
      have coordinate : u.2-b.2+a.2=v.2 := by rw [displacement]; abel
      rw [sub_add_cancel,coordinate] at clause
      have negB : ¬ Truth model b.1 u.2 := (truth_negate model b.1 u.2).mp (by change negate b.1=u.1 at source; rw [source]; exact trueSource)
      exact target ▸ clause.resolve_right negB

/-- Models of clauses are exactly complete consistent upward-closed implication sets. -/
theorem satisfiable_iff_graph (formula : Formula V d) :
    Satisfiable formula ↔ none ∉ formula ∧ ∃ T, (graph formula).Model T := by
  classical
  constructor
  · rintro ⟨model,satisfied⟩
    refine ⟨fun member => satisfied none member 0, {u | Truth model u.1 u.2},?_,?_⟩
    · rintro ⟨a,z⟩
      exact truth_negate model a z
    · intro a ha b path
      induction path with
      | refl => exact ha
      | @tail w v path edge ih => exact model_edge formula model satisfied edge ih
  · rintro ⟨noEmpty,T,model⟩
    let assignment := fun a z => ((a,true),z) ∈ T
    have truth (a : Signed V) (z : Lattice d) : Truth assignment a z ↔ (a,z) ∈ T := by
      obtain ⟨a,b⟩ := a
      cases b
      · exact (model.1 ((a,true),z)).symm
      · rfl
    refine ⟨assignment,?_⟩
    intro c member z
    cases c with
    | none => exact False.elim (noEmpty member)
    | some pair =>
      obtain ⟨a,b⟩ := pair
      change Truth assignment a.1 (z+a.2) ∨ Truth assignment b.1 (z+b.2)
      by_cases one : Truth assignment a.1 (z+a.2)
      · exact Or.inl one
      · have absent : (a.1,z+a.2) ∉ T := fun h => one ((truth _ _).mpr h)
        have negative := (model.1 (a.1,z+a.2)).mpr absent
        have edge := clause_edge formula a b member z
        have reached := model.2 _ negative _ (Relation.ReflTransGen.single edge)
        exact Or.inr ((truth _ _).mpr reached)

/-- Local input offsets lie in the unit box. Implication offsets then lie in twice that box. -/
def Local (formula : Formula V d) : Prop := ∀ a b, some (a,b) ∈ formula →
  (∀ i, (a.2 i).natAbs ≤ 1) ∧ (∀ i, (b.2 i).natAbs ≤ 1)

theorem local_arcs (formula : Formula V d) (locality : Local formula) :
    ∀ e ∈ arcs formula, ∀ i, (e.offset i).natAbs ≤ 2 := by
  intro e member i
  obtain ⟨c,hc,he⟩ := List.mem_flatMap.mp member
  cases c with
  | none => simp [clauseArcs] at he
  | some pair =>
    obtain ⟨a,b⟩ := pair
    obtain ⟨ha,hb⟩ := locality a b hc
    rcases (by simpa [clauseArcs] using he : e=⟨negate a.1,b.1,b.2-a.2⟩ ∨ e=⟨negate b.1,a.1,a.2-b.2⟩) with rfl | rfl
    · exact (Int.natAbs_sub_le _ _).trans (by have := ha i; have := hb i; omega)
    · exact (Int.natAbs_sub_le _ _).trans (by have := ha i; have := hb i; omega)

end LeanTrominoes.PeriodicTwoSAT
