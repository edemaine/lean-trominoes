/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.PeriodicExactOneFieldPredicate

/-! # Correctness of the compiled exact-one transition -/
namespace LeanTrominoes.PeriodicCNF.ExactOneFieldPredicate
open PeriodicCNFFlatEncoding FlatScanner BoundedArithmetic BoundedArithmetic.Expr

private theorem count_three (bs : List Bool) (hw : bs.length≤3) :
    bs.count true = (bs[0]?.getD false).toNat + (bs[1]?.getD false).toNat +
      (bs[2]?.getD false).toNat := by
  rcases bs with _ | ⟨a,bs⟩
  · rfl
  rcases bs with _ | ⟨b,bs⟩
  · cases a <;> rfl
  rcases bs with _ | ⟨c,bs⟩
  · cases a <;> cases b <;> rfl
  cases bs with
  | nil => cases a <;> cases b <;> cases c <;> rfl
  | cons d bs => simp only [List.length_cons] at hw; omega

private theorem slot_typed (f : PeriodicCNF Nat) (word : Nat) {h : Nat}
    {c : PeriodicClause Nat} (hc : (h,c)∈clauseEntries 1 f.clauses)
    (locality : c.IsLocalOnLine) (i : Nat) :
    slotValue ((formulaFields f)[h]?.getD 0)
      (FieldPredicate.LiteralTrue (formulaFields f).length (literalMarks 1 f.clauses) word h · (formulaFields f)) i =
    ((c.map fun l => FieldWindow.value f l.atom
      (FieldWindow.decodeWord f word (LineWindow.position c l)) == l.value)[i]?.getD false).toNat := by
  rw [clauseEntry_header f hc]
  by_cases hi : i<c.length
  · simp only [slotValue,hi,if_true,List.getElem?_map,List.getElem?_eq_getElem hi,Option.map_some,Option.getD_some]
    apply congrArg Bool.toNat
    apply Bool.eq_iff_iff.mpr
    simp only [decide_eq_true_eq,beq_iff_eq]
    exact FieldPredicate.literal_typed f word hc locality i hi
  · simp [slotValue,hi]

theorem valid_typed (f : PeriodicCNF Nat) (word : Nat) (locality : f.IsLocalOnLine) :
    Valid (formulaFields f).length (clauseMarks 1 f.clauses) (literalMarks 1 f.clauses) word (formulaFields f) ↔
      f.WidthAtMost 3 ∧ ExactOneFieldWindow.Valid f (FieldWindow.decodeWord f word) := by
  have row (h : Nat) (c : PeriodicClause Nat) (hc : (h,c)∈clauseEntries 1 f.clauses)
      (width : c.length≤3) :
      slotValue ((formulaFields f)[h]?.getD 0)
        (FieldPredicate.LiteralTrue (formulaFields f).length (literalMarks 1 f.clauses) word h · (formulaFields f)) 0 +
      slotValue ((formulaFields f)[h]?.getD 0)
        (FieldPredicate.LiteralTrue (formulaFields f).length (literalMarks 1 f.clauses) word h · (formulaFields f)) 1 +
      slotValue ((formulaFields f)[h]?.getD 0)
        (FieldPredicate.LiteralTrue (formulaFields f).length (literalMarks 1 f.clauses) word h · (formulaFields f)) 2 =
      (c.map fun l => FieldWindow.value f l.atom
        (FieldWindow.decodeWord f word (LineWindow.position c l)) == l.value).count true := by
    have cl := locality c ((clauseEntries_members 1 f.clauses c).mp ⟨h,hc⟩)
    rw [slot_typed f word hc cl 0,slot_typed f word hc cl 1,slot_typed f word hc cl 2]
    exact (count_three _ (by simpa using width)).symm
  constructor
  · intro raw
    have width : f.WidthAtMost 3 := by
      intro c hc
      obtain ⟨h,hh⟩ := (clauseEntries_members 1 f.clauses c).mpr hc
      have bound := (raw h (FieldPredicate.clause_bound f hh) ((clauseMarks_testBit _ _ _).mpr ⟨c,hh⟩)).1
      rwa [clauseEntry_header f hh] at bound
    refine ⟨width,?_⟩
    intro c hc
    obtain ⟨h,hh⟩ := (clauseEntries_members 1 f.clauses c).mpr hc
    have result := (raw h (FieldPredicate.clause_bound f hh) ((clauseMarks_testBit _ _ _).mpr ⟨c,hh⟩)).2
    rw [row h c hh (width c hc)] at result
    exact result
  · rintro ⟨width,typed⟩ h _ hh
    obtain ⟨c,hc⟩ := (clauseMarks_testBit _ _ _).mp hh
    have mem := (clauseEntries_members 1 f.clauses c).mp ⟨h,hc⟩
    refine ⟨?_,?_⟩
    · rw [clauseEntry_header f hc]
      exact width c mem
    · rw [row h c hc (width c mem)]
      exact typed c mem

abbrev context := FieldPredicate.context
abbrev input := FieldPredicate.input

def check (f : PeriodicCNF Nat) (a b : Nat) : Bool := decide (transition.eval (input f a b) ≠ 0)
def decision : Expr := .ite transition 1 0

theorem decision_noPower : decision.noPower=true := by simp [decision,Expr.noPower,transition_noPower]

theorem decision_eval (f : PeriodicCNF Nat) (a b : Nat) :
    decision.eval (input f a b) = (check f a b).toNat := by
  by_cases h : transition.eval (input f a b)=0 <;> simp [decision,Expr.eval,check,h]

theorem check_true (f : PeriodicCNF Nat) (a b : Nat) : check f a b=true ↔
    f.IsOneDimensional ∧ f.IsLocalOnLine ∧ f.WidthAtMost 3 ∧ ExactOneFieldWindow.packedTransition f a b := by
  simp only [check,decide_eq_true_eq]
  change transition.Truth (FieldPredicate.input f a b) ↔ _
  rw [FieldPredicate.input,transition_correct,FieldPredicate.horizontal_typed,
    FieldPredicate.local_typed,FieldPredicate.overlap_typed]
  constructor
  · rintro ⟨hh,hl,hv,ho⟩
    have v := (valid_typed f a hl).mp hv
    exact ⟨hh,hl,v.1,v.2,ho⟩
  · rintro ⟨hh,hl,hw,hv,ho⟩
    exact ⟨hh,hl,(valid_typed f a hl).mpr ⟨hw,hv⟩,ho⟩

theorem cycle_iff (f : PeriodicCNF Nat) :
    FiniteState.HasCycle (fun a b : FieldWindow.PackedState f => check f a.val b.val=true) ↔
      PeriodicExactOneCNF.LocalOneDimensionalThreeSAT f := by
  constructor
  · rintro ⟨period,states,steps⟩
    have first := (check_true f _ _).mp (steps 0)
    refine ⟨first.2.2.1,first.1,(isLocal_iff_isLocalOnLine first.1).mpr first.2.1,?_⟩
    apply (ExactOneFieldWindow.satisfiable_iff_packed_cycle f first.1 first.2.1).mpr
    exact ⟨period,states,fun i => ((check_true f _ _).mp (steps i)).2.2.2⟩
  · rintro ⟨hw,hh,hl,hs⟩
    have localLine := (isLocal_iff_isLocalOnLine hh).mp hl
    obtain ⟨period,states,steps⟩ := (ExactOneFieldWindow.satisfiable_iff_packed_cycle f hh localLine).mp hs
    exact ⟨period,states,fun i => (check_true f _ _).mpr ⟨hh,localLine,hw,steps i⟩⟩
end LeanTrominoes.PeriodicCNF.ExactOneFieldPredicate
