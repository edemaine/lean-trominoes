/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.PeriodicCNFFieldTransition
import LeanTrominoes.ListAtMostThree

/-! # Recognizing three-occurrence formulas by flat literal addresses -/
namespace LeanTrominoes.PeriodicCNF.FieldOccurrences
open FlatScanner PeriodicCNFFlatEncoding FieldPredicate

def addresses (f : PeriodicCNF Nat) (atom : Nat) : List Nat :=
  ((allLiteralEntries 1 f.clauses).filter fun e => e.2.atom == atom).map Prod.fst

theorem mem_addresses (f : PeriodicCNF Nat) (atom p : Nat) :
    p ∈ addresses f atom ↔ p < (formulaFields f).length ∧
      (literalMarks 1 f.clauses).testBit p=true ∧ (formulaFields f)[p]?.getD 0=atom := by
  simp only [addresses,List.mem_map,List.mem_filter,beq_iff_eq]
  constructor
  · rintro ⟨⟨q,l⟩,⟨hl,ha⟩,rfl⟩
    exact ⟨literal_bound f hl,(literalMarks_testBit _ _ _).mpr ⟨l,hl⟩,
      (literalEntry_atom f hl).trans ha⟩
  · rintro ⟨_,hp,ha⟩
    obtain ⟨l,hl⟩ := (literalMarks_testBit _ _ _).mp hp
    exact ⟨(p,l),⟨hl,(literalEntry_atom f hl).symm.trans ha⟩,rfl⟩

theorem addresses_nodup (f : PeriodicCNF Nat) (atom : Nat) : (addresses f atom).Nodup := by
  have sub := (List.filter_sublist (p := fun e : Nat × PeriodicLiteral Nat => e.2.atom == atom)
    (l := allLiteralEntries 1 f.clauses)).map Prod.fst
  exact (allLiteralEntries_sorted 1 f.clauses).nodup.sublist sub

private theorem literal_count (start atom : Nat) (ls : List (PeriodicLiteral Nat)) :
    ((literalEntries start ls).filter fun e => e.2.atom == atom).length =
      (ls.map PeriodicLiteral.atom).count atom := by
  induction ls generalizing start with
  | nil => simp [literalEntries]
  | cons l ls ih =>
    by_cases h : l.atom=atom <;> simp [literalEntries,List.filter_cons,ih,List.count_cons,h]

theorem addresses_length (f : PeriodicCNF Nat) (atom : Nat) :
    (addresses f atom).length = f.variableOccurrences.count atom := by
  simp only [addresses,List.length_map,variableOccurrences]
  suffices ∀ start, ((allLiteralEntries start f.clauses).filter fun e => e.2.atom == atom).length =
      (f.clauses.flatMap fun c => c.map PeriodicLiteral.atom).count atom from this 1
  induction f.clauses with
  | nil => simp [allLiteralEntries]
  | cons c cs ih =>
    intro start
    simp [allLiteralEntries,List.filter_append,literal_count,ih,List.count_append]

def Raw (f : PeriodicCNF Nat) : Prop :=
  ∀ a < (formulaFields f).length, ∀ b < (formulaFields f).length,
  ∀ c < (formulaFields f).length, ∀ d < (formulaFields f).length,
    (literalMarks 1 f.clauses).testBit a=true →
    (literalMarks 1 f.clauses).testBit b=true →
    (literalMarks 1 f.clauses).testBit c=true →
    (literalMarks 1 f.clauses).testBit d=true →
    (formulaFields f)[b]?.getD 0=(formulaFields f)[a]?.getD 0 →
    (formulaFields f)[c]?.getD 0=(formulaFields f)[a]?.getD 0 →
    (formulaFields f)[d]?.getD 0=(formulaFields f)[a]?.getD 0 →
    a=b ∨ a=c ∨ a=d ∨ b=c ∨ b=d ∨ c=d

theorem raw_correct (f : PeriodicCNF Nat) : Raw f ↔ f.OccurrencesAtMost 3 := by
  constructor
  · intro check atom
    rw [← addresses_length]
    apply (list_length_le_three_iff _ (addresses_nodup f atom)).mpr
    intro a ha b hb c hc d hd
    rw [mem_addresses] at ha hb hc hd
    exact check a ha.1 b hb.1 c hc.1 d hd.1 ha.2.1 hb.2.1 hc.2.1 hd.2.1
      (hb.2.2.trans ha.2.2.symm) (hc.2.2.trans ha.2.2.symm) (hd.2.2.trans ha.2.2.symm)
  · intro bound a ha b hb c hc d hd ma mb mc md eb ec ed
    have h := bound ((formulaFields f)[a]?.getD 0)
    rw [← addresses_length] at h
    apply (list_length_le_three_iff _ (addresses_nodup f _)).mp h
    · exact (mem_addresses _ _ _).mpr ⟨ha,ma,rfl⟩
    · exact (mem_addresses _ _ _).mpr ⟨hb,mb,eb⟩
    · exact (mem_addresses _ _ _).mpr ⟨hc,mc,ec⟩
    · exact (mem_addresses _ _ _).mpr ⟨hd,md,ed⟩

open BoundedArithmetic BoundedArithmetic.Expr

/-- Four marked addresses with the same atom must include a duplicate. -/
def duplicateExpr : Expr :=
  orE (eqE (var 3) (var 2)) <|
  orE (eqE (var 3) (var 1)) <|
  orE (eqE (var 3) (var 0)) <|
  orE (eqE (var 2) (var 1)) <|
  orE (eqE (var 2) (var 0)) (eqE (var 1) (var 0))

def guardExpr : Expr :=
  .all (var 0) <| .all (var 1) <| .all (var 2) <| .all (var 3) <|
  impE (.testBit (var 6) (var 3)) <|
  impE (.testBit (var 6) (var 2)) <|
  impE (.testBit (var 6) (var 1)) <|
  impE (.testBit (var 6) (var 0)) <|
  impE (eqE (field 4 (var 2)) (field 4 (var 3))) <|
  impE (eqE (field 4 (var 1)) (field 4 (var 3))) <|
  impE (eqE (field 4 (var 0)) (field 4 (var 3))) duplicateExpr

theorem guard_correct (f : PeriodicCNF Nat) :
    guardExpr.Truth (input f 0 0) ↔ f.OccurrencesAtMost 3 := by
  rw [← raw_correct]
  have lookup (a b c d : Nat) (e : Expr) :
      (field 4 e).eval (d::c::b::a::input f 0 0) =
        (formulaFields f)[e.eval (d::c::b::a::input f 0 0)]?.getD 0 := by
    exact field_eval 4 e [d,c,b,a,(formulaFields f).length,clauseMarks 1 f.clauses,
      literalMarks 1 f.clauses,0,0] (formulaFields f) rfl
  simp only [guardExpr,duplicateExpr,truth_all,truth_imp,truth_or,truth_eq,truth_bit,lookup]
  simp [Raw,input,context,Expr.eval]

end LeanTrominoes.PeriodicCNF.FieldOccurrences
