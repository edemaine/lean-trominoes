/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.PeriodicCNFFieldPredicate
import LeanTrominoes.PeriodicCNFFlatLookup
import LeanTrominoes.PeriodicCNFFieldWindow

/-! # Correctness of compiled horizontal and locality tests -/
namespace LeanTrominoes.PeriodicCNF.FieldPredicate
open PeriodicCNFFlatEncoding FlatScanner Turing.ToPartrec

private theorem code_eq (a b : Int) : Encodable.encode a=Encodable.encode b ↔ a=b :=
  Encodable.encode_injective.eq_iff

theorem nearby_codes (a b : Int) :
    (Encodable.encode a=Encodable.encode b ∨
      Encodable.encode a=Code.intCodeSuccessor (Encodable.encode b) ∨
      Encodable.encode b=Code.intCodeSuccessor (Encodable.encode a)) ↔ (a-b).natAbs ≤ 1 := by
  rw [Code.intCodeSuccessor_encode,Code.intCodeSuccessor_encode]
  simp only [code_eq]
  omega

theorem clause_x (f : PeriodicCNF Nat) {h : Nat} {c : PeriodicClause Nat}
    (hc : (h,c) ∈ clauseEntries 1 f.clauses) (i : Nat) (hi : i<c.length) :
    (formulaFields f)[h+2+4*i]?.getD 0 = Encodable.encode c[i].offset.1 := by
  have e := congrArg (fun x : Option Nat => x.getD 0) (clauseEntry_literal f hc i hi 1 (by decide))
  rw [show h+1+4*i+1 = h+2+4*i by omega] at e
  simpa [literalFields] using e

theorem clause_atom (f : PeriodicCNF Nat) {h : Nat} {c : PeriodicClause Nat}
    (hc : (h,c) ∈ clauseEntries 1 f.clauses) (i : Nat) (hi : i<c.length) :
    (formulaFields f)[h+1+4*i]?.getD 0 = c[i].atom := by
  have e := congrArg (fun x : Option Nat => x.getD 0) (clauseEntry_literal f hc i hi 0 (by decide))
  simpa [literalFields] using e

theorem clause_value (f : PeriodicCNF Nat) {h : Nat} {c : PeriodicClause Nat}
    (hc : (h,c) ∈ clauseEntries 1 f.clauses) (i : Nat) (hi : i<c.length) :
    (formulaFields f)[h+4+4*i]?.getD 0 = encodeBoolField c[i].value := by
  have e := congrArg (fun x : Option Nat => x.getD 0) (clauseEntry_literal f hc i hi 3 (by decide))
  rw [show h+1+4*i+3 = h+4+4*i by omega] at e
  simpa [literalFields] using e

theorem clause_bound (f : PeriodicCNF Nat) {h : Nat} {c : PeriodicClause Nat}
    (hc : (h,c) ∈ clauseEntries 1 f.clauses) : h<(formulaFields f).length := by
  have b := (clauseEntries_bounds 1 f.clauses hc).2
  simpa only [formulaFields,List.length_cons,Nat.add_comm 1] using b

theorem literal_bound (f : PeriodicCNF Nat) {p : Nat} {l : PeriodicLiteral Nat}
    (hl : (p,l) ∈ allLiteralEntries 1 f.clauses) : p<(formulaFields f).length := by
  have b := (allLiteralEntries_bounds 1 f.clauses hl).2
  simpa only [formulaFields,List.length_cons,Nat.add_comm 1] using b

theorem horizontal_typed (f : PeriodicCNF Nat) :
    Horizontal (formulaFields f).length (literalMarks 1 f.clauses) (formulaFields f) ↔
      f.IsOneDimensional := by
  have lookup {p : Nat} {l : PeriodicLiteral Nat} (hp : (p,l) ∈ allLiteralEntries 1 f.clauses) :
      (formulaFields f)[p+2]?.getD 0 = Encodable.encode l.offset.2 := by
    simpa [literalFields] using congrArg (fun x : Option Nat => x.getD 0)
      (literalEntry_fields f hp 2 (by decide))
  constructor
  · intro raw c hc l hl
    obtain ⟨p,hp⟩ := (allLiteralEntries_members 1 f.clauses l).mpr ⟨c,hc,hl⟩
    have e := raw p (literal_bound f hp) ((literalMarks_testBit _ _ _).mpr ⟨l,hp⟩)
    rw [lookup hp] at e
    exact Encodable.encode_injective (show Encodable.encode l.offset.2 = Encodable.encode (0 : Int) from e)
  · intro typed p _ hp
    obtain ⟨l,hl⟩ := (literalMarks_testBit _ _ _).mp hp
    obtain ⟨c,hc,hcl⟩ := (allLiteralEntries_members 1 f.clauses l).mp ⟨p,hl⟩
    rw [lookup hl,typed c hc l hcl]
    rfl

theorem local_typed (f : PeriodicCNF Nat) :
    Local (formulaFields f).length (clauseMarks 1 f.clauses) (formulaFields f) ↔ f.IsLocalOnLine := by
  constructor
  · intro raw c hc a ha b hb
    obtain ⟨h,hh⟩ := (clauseEntries_members 1 f.clauses c).mpr hc
    obtain ⟨i,hi,rfl⟩ := List.mem_iff_getElem.mp ha
    obtain ⟨j,hj,rfl⟩ := List.mem_iff_getElem.mp hb
    have e := raw h (clause_bound f hh) ((clauseMarks_testBit _ _ _).mpr ⟨c,hh⟩)
    rw [clauseEntry_header f hh] at e
    have e' := e i hi j hj
    dsimp only at e'
    rw [clause_x f hh i hi,clause_x f hh j hj] at e'
    exact (nearby_codes _ _).mp e'
  · intro typed h _ hh i hi j hj
    obtain ⟨c,hc⟩ := (clauseMarks_testBit _ _ _).mp hh
    rw [clauseEntry_header f hc] at hi hj
    dsimp only
    rw [clause_x f hc i hi,clause_x f hc j hj]
    apply (nearby_codes _ _).mpr
    exact typed c ((clauseEntries_members 1 f.clauses c).mp ⟨h,hc⟩)
      c[i] (List.getElem_mem hi) c[j] (List.getElem_mem hj)

theorem phase_typed (c : PeriodicClause Nat) (locality : c.IsLocalOnLine)
    {l : PeriodicLiteral Nat} (hl : l ∈ c) :
    phaseValue (Encodable.encode l.offset.1) (Encodable.encode (LineWindow.anchor c)) =
      (LineWindow.position c l).val := by
  have eq := LineWindow.position_eq locality hl
  have bound := (LineWindow.position c l).isLt
  unfold phaseValue
  rw [Code.intCodeSuccessor_encode]
  simp only [code_eq]
  split_ifs <;> omega

end LeanTrominoes.PeriodicCNF.FieldPredicate
