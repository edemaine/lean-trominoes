/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.PeriodicCNFOneDimensional

/-! # Localizing clauses whose individual incidences are local

A clause can span two cells even when every incidence has offset at most one.
Introduce a shadow variable at the clause cell for each referenced translate,
with two binary clauses equating it to the original variable. This preserves
satisfiability and makes every clause local without strengthening the input
promise.
-/
namespace LeanTrominoes.PeriodicCNF.EdgeLocalization
variable {V : Type}

def shadow (l : PeriodicLiteral V) : PeriodicLiteral (V × Cell) :=
  ⟨(l.atom,l.offset),(0,0),l.value⟩

def bridge (l : PeriodicLiteral V) (b : Bool) : PeriodicClause (V × Cell) :=
  [⟨(l.atom,l.offset),(0,0),!b⟩, ⟨(l.atom,(0,0)),l.offset,b⟩]

def clause (c : PeriodicClause V) : List (PeriodicClause (V × Cell)) :=
  c.map shadow :: c.flatMap (fun l => [bridge l true, bridge l false])

def formula (f : PeriodicCNF V) : PeriodicCNF (V × Cell) :=
  ⟨f.clauses.flatMap clause⟩

private theorem bridge_iff (a : V × Cell → Cell → Bool) (x : Cell)
    (l : PeriodicLiteral V) :
    (bridge l true).Holds a x ∧ (bridge l false).Holds a x ↔
      a (l.atom,l.offset) x = a (l.atom,(0,0)) (Cell.add x l.offset) := by
  simp only [bridge, PeriodicClause.Holds, List.mem_cons, List.not_mem_nil,
    or_false, exists_eq_or_imp, exists_eq_left, PeriodicLiteral.Holds,
    Cell.add, Int.add_zero, Bool.not_true, Bool.not_false]
  cases a (l.atom,l.offset) x <;>
    cases a (l.atom,(0,0)) (x.1+l.offset.1,x.2+l.offset.2) <;> simp_all

theorem satisfiable_iff (f : PeriodicCNF V) : (formula f).Satisfiable ↔ f.Satisfiable := by
  constructor
  · rintro ⟨a,ha⟩
    refine ⟨fun v x => a (v,(0,0)) x, ?_⟩
    intro x c hc
    have main := ha x (c.map shadow) (List.mem_flatMap.mpr ⟨c,hc,by simp [clause]⟩)
    obtain ⟨selected,selectedMem,h⟩ := main
    obtain ⟨l,hl,rfl⟩ := List.mem_map.mp selectedMem
    have eq : a (l.atom,l.offset) x = a (l.atom,(0,0)) (Cell.add x l.offset) := by
      apply (bridge_iff a x l).1
      constructor <;> apply ha x _ <;>
        exact List.mem_flatMap.mpr ⟨c,hc,List.mem_cons_of_mem _
          (List.mem_flatMap.mpr ⟨l,hl,by simp⟩)⟩
    refine ⟨l,hl,?_⟩
    simpa only [shadow, PeriodicLiteral.Holds, Cell.add, Int.add_zero, eq] using h
  · rintro ⟨a,ha⟩
    let lifted : V × Cell → Cell → Bool := fun v x => a v.1 (Cell.add x v.2)
    refine ⟨lifted,?_⟩
    intro x d hd
    obtain ⟨c,hc,hd⟩ := List.mem_flatMap.mp hd
    rcases List.mem_cons.mp hd with rfl | hd
    · obtain ⟨l,hl,h⟩ := ha x c hc
      refine ⟨shadow l,List.mem_map.mpr ⟨l,hl,rfl⟩,?_⟩
      simpa [shadow,PeriodicLiteral.Holds,lifted,Cell.add] using h
    · obtain ⟨l,_,hd⟩ := List.mem_flatMap.mp hd
      have both := (bridge_iff lifted x l).2 (by simp [lifted,Cell.add])
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hd
      rcases hd with rfl | rfl
      · exact both.1
      · exact both.2

/-- The incidence graph's edge-locality promise, with the clause at offset zero. -/
def EdgeLocal (f : PeriodicCNF V) : Prop :=
  ∀ c ∈ f.clauses, ∀ l ∈ c, l.offset.1.natAbs + l.offset.2.natAbs ≤ 1

private theorem bridge_local (l : PeriodicLiteral V) (b : Bool)
    (h : l.offset.1.natAbs + l.offset.2.natAbs ≤ 1) : (bridge l b).IsLocal := by
  intro a ha z hz
  simp only [bridge,List.mem_cons,List.not_mem_nil,or_false] at ha hz
  rcases ha with rfl | rfl <;> rcases hz with rfl | rfl <;>
    simp_all [PeriodicClause.offsetDistance]

theorem isLocal (f : PeriodicCNF V) (h : EdgeLocal f) : (formula f).IsLocal := by
  intro d hd
  obtain ⟨c,hc,hd⟩ := List.mem_flatMap.mp hd
  rcases List.mem_cons.mp hd with rfl | hd
  · intro a ha b hb
    obtain ⟨a,_,rfl⟩ := List.mem_map.mp ha
    obtain ⟨b,_,rfl⟩ := List.mem_map.mp hb
    simp [shadow,PeriodicClause.offsetDistance]
  · obtain ⟨l,hl,hd⟩ := List.mem_flatMap.mp hd
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hd
    rcases hd with rfl | rfl <;> exact bridge_local l _ (h c hc l hl)

theorem isOneDimensional (f : PeriodicCNF V) (h : f.IsOneDimensional) :
    (formula f).IsOneDimensional := by
  intro d hd a ha
  obtain ⟨c,hc,hd⟩ := List.mem_flatMap.mp hd
  rcases List.mem_cons.mp hd with rfl | hd
  · obtain ⟨a,_,rfl⟩ := List.mem_map.mp ha
    rfl
  · obtain ⟨l,hl,hd⟩ := List.mem_flatMap.mp hd
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hd
    rcases hd with rfl | rfl <;>
      simp only [bridge,List.mem_cons,List.not_mem_nil,or_false] at ha <;>
      rcases ha with rfl | rfl
    · rfl
    · exact h c hc l hl
    · rfl
    · exact h c hc l hl

theorem width (f : PeriodicCNF V) {k : Nat} (hk : 2 ≤ k) (h : f.WidthAtMost k) :
    (formula f).WidthAtMost k := by
  intro d hd
  obtain ⟨c,hc,hd⟩ := List.mem_flatMap.mp hd
  rcases List.mem_cons.mp hd with rfl | hd
  · simpa [PeriodicClause.WidthAtMost] using h c hc
  · obtain ⟨l,_,hd⟩ := List.mem_flatMap.mp hd
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hd
    rcases hd with rfl | rfl <;> simpa [bridge,PeriodicClause.WidthAtMost] using hk

end LeanTrominoes.PeriodicCNF.EdgeLocalization
