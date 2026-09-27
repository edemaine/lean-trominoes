/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.PeriodicCNF
import LeanTrominoes.PeriodicHornCore

/-! # Period-one Horn models for the existing periodic CNF representation

Repeated copies of a literal do not affect the Horn condition. There is at
most one distinct positive literal per Horn clause.
-/
namespace LeanTrominoes
namespace PeriodicClause
variable {V : Type*}

def IsHorn (c : PeriodicClause V) : Prop :=
  ∀ a ∈ c, ∀ b ∈ c, a.value=true → b.value=true → a=b

def hornRule (c : PeriodicClause V) : Horn.PeriodicRule V Cell :=
  ⟨(c.filter (fun l => !l.value)).map (fun l => (l.atom,l.offset)),
    ((c.filter (fun l => l.value)).head?).map (fun l => (l.atom,l.offset))⟩

private theorem holds_iff_implication (c : PeriodicClause V) (model : V → Cell → Bool) (z : Cell) :
    c.Holds model z ↔
      (∀ l ∈ c, l.value=false → model l.atom (Cell.add z l.offset)=true) →
        ∃ l ∈ c, l.value=true ∧ model l.atom (Cell.add z l.offset)=true := by
  classical
  constructor
  · rintro ⟨l,hl,holds⟩ premises
    cases value : l.value with
    | true => exact ⟨l,hl,value,by simpa [PeriodicLiteral.Holds,value] using holds⟩
    | false =>
      have yes := premises l hl value
      have no : model l.atom (Cell.add z l.offset)=false := by simpa [PeriodicLiteral.Holds,value] using holds
      simp_all
  · intro implication
    by_contra absent
    have premises : ∀ l ∈ c, l.value=false → model l.atom (Cell.add z l.offset)=true := by
      intro l hl value
      have no : model l.atom (Cell.add z l.offset) ≠ false := by
        intro h
        exact absent ⟨l,hl,by simpa [PeriodicLiteral.Holds,value] using h⟩
      exact Bool.eq_true_of_not_eq_false no
    obtain ⟨l,hl,value,h⟩ := implication premises
    exact absent ⟨l,hl,by simpa [PeriodicLiteral.Holds,value] using h⟩

private theorem positive_head (c : PeriodicClause V) (horn : c.IsHorn) (P : PeriodicLiteral V → Prop) :
    (∃ l ∈ c, l.value=true ∧ P l) ↔
      match (c.filter (fun l => l.value)).head? with
      | none => False
      | some l => P l := by
  cases positives : c.filter (fun l => l.value) with
  | nil =>
    simp only [List.head?_nil,iff_false]
    rintro ⟨l,hl,value,_⟩
    have member : l ∈ c.filter (fun l => l.value) := List.mem_filter.mpr ⟨hl,value⟩
    simp [positives] at member
  | cons first rest =>
    have member : first ∈ c.filter (fun l => l.value) := by rw [positives]; simp
    obtain ⟨hf,value⟩ := List.mem_filter.mp member
    simp only [List.head?_cons]
    constructor
    · rintro ⟨l,hl,lv,h⟩
      exact (horn l hl first hf lv value) ▸ h
    · intro h
      exact ⟨first,hf,value,h⟩

theorem hornRule_correct (c : PeriodicClause V) (horn : c.IsHorn) (model : V → Cell → Bool) (z : Cell) :
    c.Holds model z ↔ c.hornRule.Holds (fun a p => model a p=true) z := by
  rw [holds_iff_implication,positive_head c horn]
  simp only [hornRule,Horn.PeriodicRule.Holds,List.forall_mem_map,List.forall_mem_filter,Bool.not_eq_true']
  have add_eq (p q : Cell) : Cell.add p q=p+q := rfl
  simp only [add_eq]
  cases (c.filter (fun l => l.value)).head? <;> rfl

end PeriodicClause
namespace PeriodicCNF
variable {V : Type*}

def IsHorn (f : PeriodicCNF V) : Prop := ∀ c ∈ f.clauses, c.IsHorn

def hornRules (f : PeriodicCNF V) : List (Horn.PeriodicRule V Cell) := f.clauses.map PeriodicClause.hornRule

theorem hornRules_correct (f : PeriodicCNF V) (horn : f.IsHorn) (model : V → Cell → Bool) :
    f.Satisfies model ↔ Horn.PeriodicSatisfies f.hornRules (fun a p => model a p=true) := by
  simp only [Satisfies,Horn.PeriodicSatisfies,hornRules,List.forall_mem_map]
  constructor
  · intro h c hc z
    exact (PeriodicClause.hornRule_correct c (horn c hc) model z).mp (h z c hc)
  · intro h z c hc
    exact (PeriodicClause.hornRule_correct c (horn c hc) model z).mpr (h c hc z)

theorem horn_period_one (f : PeriodicCNF V) (horn : f.IsHorn) (sat : f.Satisfiable) :
    ∃ model : V → Bool, f.Satisfies (fun a _ => model a) := by
  classical
  obtain ⟨model,hm⟩ := sat
  obtain ⟨uniform,hu⟩ := Horn.exists_period_one f.hornRules ⟨_,(hornRules_correct f horn model).mp hm⟩
  refine ⟨fun a => decide (uniform a),(hornRules_correct f horn _).mpr ?_⟩
  simpa using hu

theorem horn_satisfiable_iff_finite (f : PeriodicCNF V) (horn : f.IsHorn) :
    f.Satisfiable ↔ Horn.Satisfiable (f.hornRules.map Horn.PeriodicRule.erase) := by
  classical
  constructor
  · rintro ⟨model,hm⟩
    exact (Horn.periodic_satisfiable_iff _).mp ⟨_,(hornRules_correct f horn model).mp hm⟩
  · intro h
    obtain ⟨model,hm⟩ := (Horn.periodic_satisfiable_iff _).mpr h
    refine ⟨fun a p => decide (model a p),(hornRules_correct f horn _).mpr ?_⟩
    simpa using hm

end PeriodicCNF
end LeanTrominoes
