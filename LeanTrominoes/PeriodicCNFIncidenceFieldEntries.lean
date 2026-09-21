/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.ListLastOccurrenceEntries
import LeanTrominoes.PeriodicCNFFieldOccurrences

/-! # Incidence variable order recovered from flat literal addresses -/
namespace LeanTrominoes.PeriodicCNF.IncidenceFields
open FlatScanner FieldPredicate PeriodicCNFFlatEncoding LastOccurrenceEntries

def entries (f : PeriodicCNF Nat) : List (Nat × Nat) :=
  (allLiteralEntries 1 f.clauses).map fun e => (e.1,e.2.atom)

theorem entries_sorted (f : PeriodicCNF Nat) : ((entries f).map Prod.fst).SortedLT := by
  simpa only [entries,List.map_map,Function.comp_def] using allLiteralEntries_sorted 1 f.clauses

theorem entries_atoms (f : PeriodicCNF Nat) : (entries f).map Prod.snd = f.variableOccurrences := by
  have row (ls : List (PeriodicLiteral Nat)) (start : Nat) :
      (literalEntries start ls).map (fun e => e.2.atom) = ls.map PeriodicLiteral.atom := by
    induction ls generalizing start with
    | nil => rfl
    | cons l ls ih => simp [literalEntries,ih]
  suffices ∀ start, (allLiteralEntries start f.clauses).map (fun e => e.2.atom) =
      f.clauses.flatMap (fun c => c.map PeriodicLiteral.atom) by
    simpa only [entries,List.map_map,Function.comp_def,variableOccurrences] using this 1
  induction f.clauses with
  | nil => intro start; rfl
  | cons c cs ih => intro start; simp [allLiteralEntries,List.map_append,row,ih]

theorem mem_entries (f : PeriodicCNF Nat) (p atom : Nat) :
    (p,atom) ∈ entries f ↔ p < (formulaFields f).length ∧
      (literalMarks 1 f.clauses).testBit p = true ∧ (formulaFields f)[p]?.getD 0 = atom := by
  constructor
  · intro h
    obtain ⟨⟨q,l⟩,hl,eq⟩ := List.mem_map.mp h
    have hp : q=p := congrArg Prod.fst eq
    have ha : l.atom=atom := congrArg Prod.snd eq
    subst q
    exact ⟨literal_bound f hl,(literalMarks_testBit _ _ _).mpr ⟨l,hl⟩,(literalEntry_atom f hl).trans ha⟩
  · rintro ⟨_,hp,ha⟩
    obtain ⟨l,hl⟩ := (literalMarks_testBit _ _ _).mp hp
    exact List.mem_map.mpr ⟨(p,l),hl,by simpa [literalEntry_atom f hl] using ha⟩

def representatives (f : PeriodicCNF Nat) : List (Nat × Nat) := retained (entries f)

theorem representatives_atoms (f : PeriodicCNF Nat) :
    (representatives f).map Prod.snd = f.variableOccurrences.dedup := by
  rw [representatives,map_retained _ (entries_sorted f),entries_atoms]

theorem representatives_addresses_nodup (f : PeriodicCNF Nat) :
    ((representatives f).map Prod.fst).Nodup := retained_addresses_nodup _ (entries_sorted f)

def representative (f : PeriodicCNF Nat) (p : Nat) : Prop :=
  (literalMarks 1 f.clauses).testBit p = true ∧
    ∀ q < (formulaFields f).length, p < q → (literalMarks 1 f.clauses).testBit q = true →
      (formulaFields f)[q]?.getD 0 ≠ (formulaFields f)[p]?.getD 0

theorem mem_representatives (f : PeriodicCNF Nat) (p : Nat) :
    p ∈ (representatives f).map Prod.fst ↔ p < (formulaFields f).length ∧ representative f p := by
  constructor
  · intro h
    obtain ⟨⟨q,a⟩,he,hp⟩ := List.mem_map.mp h
    have eq : q=p := hp
    subst q
    obtain ⟨he,hs⟩ := List.mem_filter.mp he
    have hm := (mem_entries f p a).mp he
    refine ⟨hm.1,hm.2.1,?_⟩
    intro q hq hpq hmq heq
    have other := (mem_entries f q ((formulaFields f)[q]?.getD 0)).mpr ⟨hq,hmq,rfl⟩
    exact (of_decide_eq_true hs) _ other hpq (hm.2.2.symm.trans heq.symm)
  · rintro ⟨hp,hm,hs⟩
    refine List.mem_map.mpr ⟨(p,(formulaFields f)[p]?.getD 0),?_,rfl⟩
    apply List.mem_filter.mpr
    refine ⟨(mem_entries _ _ _).mpr ⟨hp,hm,rfl⟩,decide_eq_true ?_⟩
    intro other ho hpo heq
    have he := (mem_entries f other.1 other.2).mp ho
    exact hs other.1 he.1 hpo he.2.1 (he.2.2.trans heq.symm)

end LeanTrominoes.PeriodicCNF.IncidenceFields
