/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.PeriodicCNFFieldSyntax

/-! # The compiled field predicate is the finite CNF window transition -/
namespace LeanTrominoes.PeriodicCNF.FieldPredicate
open PeriodicCNFFlatEncoding FlatScanner Turing.ToPartrec BoundedArithmetic BoundedArithmetic.Expr

theorem atom_typed (f : PeriodicCNF Nat) (word atom : Nat) (column : Fin 3) :
    AtomTrue (formulaFields f).length (literalMarks 1 f.clauses) word column.val atom (formulaFields f) ↔
      FieldWindow.value f atom (FieldWindow.decodeWord f word column) = true := by
  rw [FieldWindow.value_true]
  change (∃ p<(formulaFields f).length, _ ∧ _ ∧ _) ↔
    ∃ p : Fin (formulaFields f).length, _ ∧ _ ∧ word.testBit (p.val+(formulaFields f).length*column.val)=true
  constructor
  · rintro ⟨p,hp,h⟩; exact ⟨⟨p,hp⟩,h⟩
  · rintro ⟨p,h⟩; exact ⟨p.val,p.isLt,h⟩

theorem clause_anchor (f : PeriodicCNF Nat) {h : Nat} {c : PeriodicClause Nat}
    (hc : (h,c) ∈ clauseEntries 1 f.clauses) (hn : 0<c.length) :
    (formulaFields f)[h+2]?.getD 0 = Encodable.encode (LineWindow.anchor c) := by
  have e := clause_x f hc 0 hn
  cases c with
  | nil => simp at hn
  | cons l ls => simpa [LineWindow.anchor] using e

theorem literal_typed (f : PeriodicCNF Nat) (word : Nat) {h : Nat} {c : PeriodicClause Nat}
    (hc : (h,c) ∈ clauseEntries 1 f.clauses) (locality : c.IsLocalOnLine) (i : Nat) (hi : i<c.length) :
    LiteralTrue (formulaFields f).length (literalMarks 1 f.clauses) word h i (formulaFields f) ↔
      FieldWindow.value f c[i].atom (FieldWindow.decodeWord f word (LineWindow.position c c[i])) = c[i].value := by
  unfold LiteralTrue
  rw [clause_atom f hc i hi,clause_x f hc i hi,clause_anchor f hc (by omega),clause_value f hc i hi]
  rw [phase_typed c locality (List.getElem_mem hi)]
  dsimp only
  rw [atom_typed]
  cases hv : c[i].value <;>
    cases hw : FieldWindow.value f c[i].atom (FieldWindow.decodeWord f word (LineWindow.position c c[i])) <;>
    simp [encodeBoolField,hv,hw]

theorem valid_typed (f : PeriodicCNF Nat) (word : Nat) (locality : f.IsLocalOnLine) :
    Valid (formulaFields f).length (clauseMarks 1 f.clauses) (literalMarks 1 f.clauses) word (formulaFields f) ↔
      FieldWindow.Valid f (FieldWindow.decodeWord f word) := by
  constructor
  · intro raw c hc
    obtain ⟨h,hh⟩ := (clauseEntries_members 1 f.clauses c).mpr hc
    obtain ⟨i,hi,holds⟩ := raw h (clause_bound f hh) ((clauseMarks_testBit _ _ _).mpr ⟨c,hh⟩)
    rw [clauseEntry_header f hh] at hi
    exact ⟨c[i],List.getElem_mem hi,(literal_typed f word hh (locality c hc) i hi).mp holds⟩
  · intro typed h _ hh
    obtain ⟨c,hc⟩ := (clauseMarks_testBit _ _ _).mp hh
    have mem := (clauseEntries_members 1 f.clauses c).mp ⟨h,hc⟩
    obtain ⟨l,hl,holds⟩ := typed c mem
    obtain ⟨i,hi,rfl⟩ := List.mem_iff_getElem.mp hl
    refine ⟨i,by rwa [clauseEntry_header f hc],?_⟩
    exact (literal_typed f word hc (locality c mem) i hi).mpr holds

theorem overlap_typed (f : PeriodicCNF Nat) (a b : Nat) :
    Overlap (formulaFields f).length a b ↔ ∀ i : Fin 2,
      FieldWindow.decodeWord f a i.succ = FieldWindow.decodeWord f b i.castSucc := by
  constructor
  · intro raw i
    funext p
    fin_cases i
    · change a.testBit (p.val+(formulaFields f).length*1) = b.testBit (p.val+(formulaFields f).length*0)
      simpa using (raw p.val p.isLt).1
    · change a.testBit (p.val+(formulaFields f).length*2) = b.testBit (p.val+(formulaFields f).length*1)
      simpa using (raw p.val p.isLt).2
  · intro typed p hp
    have h0 := congrFun (typed 0) ⟨p,hp⟩
    have h1 := congrFun (typed 1) ⟨p,hp⟩
    change a.testBit (p+(formulaFields f).length*1) = b.testBit (p+(formulaFields f).length*0) at h0
    change a.testBit (p+(formulaFields f).length*2) = b.testBit (p+(formulaFields f).length*1) at h1
    simpa [Overlap] using And.intro h0 h1

def input (f : PeriodicCNF Nat) (a b : Nat) : List Nat :=
  context (formulaFields f).length (clauseMarks 1 f.clauses) (literalMarks 1 f.clauses) a b (formulaFields f)

theorem transition_typed (f : PeriodicCNF Nat) (a b : Nat) :
    transition.Truth (input f a b) ↔ f.IsOneDimensional ∧ f.IsLocalOnLine ∧ FieldWindow.packedTransition f a b := by
  rw [input,transition_correct,horizontal_typed,local_typed,overlap_typed]
  constructor
  · rintro ⟨hh,hl,hv,ho⟩
    exact ⟨hh,hl,(valid_typed f a hl).mp hv,ho⟩
  · rintro ⟨hh,hl,hv,ho⟩
    exact ⟨hh,hl,(valid_typed f a hl).mpr hv,ho⟩

def check (f : PeriodicCNF Nat) (a b : Nat) : Bool := decide (transition.eval (input f a b) ≠ 0)

def decision : Expr := .ite transition 1 0

theorem decision_noPower : decision.noPower = true := by simp [decision,Expr.noPower,transition_noPower]

theorem decision_eval (f : PeriodicCNF Nat) (a b : Nat) :
    decision.eval (input f a b) = (check f a b).toNat := by
  by_cases h : transition.eval (input f a b)=0 <;> simp [decision,Expr.eval,check,Truth,h]

theorem check_true (f : PeriodicCNF Nat) (a b : Nat) : check f a b=true ↔
    f.IsOneDimensional ∧ f.IsLocalOnLine ∧ FieldWindow.packedTransition f a b := by
  simpa only [check,decide_eq_true_eq,Truth] using transition_typed f a b

theorem cycle_iff (f : PeriodicCNF Nat) :
    FiniteState.HasCycle (fun a b : FieldWindow.PackedState f => check f a.val b.val=true) ↔
      LocalPeriodicCNF1DSAT f := by
  constructor
  · rintro ⟨period,states,steps⟩
    have first := (check_true f _ _).mp (steps 0)
    refine ⟨first.1,first.2.1,?_⟩
    apply (PeriodicCNF.satisfiable_iff_satisfiableOnLine first.1).mp
    apply (FieldWindow.satisfiable_iff_packed_cycle f first.1 first.2.1).mpr
    exact ⟨period,states,fun i => ((check_true f _ _).mp (steps i)).2.2⟩
  · rintro ⟨hh,hl,hs⟩
    have sat := (PeriodicCNF.satisfiable_iff_satisfiableOnLine hh).mpr hs
    obtain ⟨period,states,steps⟩ := (FieldWindow.satisfiable_iff_packed_cycle f hh hl).mp sat
    exact ⟨period,states,fun i => (check_true f _ _).mpr ⟨hh,hl,steps i⟩⟩

end LeanTrominoes.PeriodicCNF.FieldPredicate
