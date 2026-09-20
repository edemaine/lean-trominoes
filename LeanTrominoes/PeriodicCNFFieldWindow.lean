/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.PeriodicCNFFlatLayout
import LeanTrominoes.PeriodicCNFLineWindow
import Mathlib.Data.BitVec
import Mathlib.Logic.Equiv.Fin.Basic

/-! # Field-indexed windows for the compiled one-dimensional CNF checker

Repeated occurrences are combined by OR. Thus every column represents an
assignment even when its occurrence bits disagree, and every assignment has
a representing column. No consistency side condition is needed.
-/
namespace LeanTrominoes.PeriodicCNF.FieldWindow
open PeriodicCNFFlatEncoding FlatScanner

abbrev size (f : PeriodicCNF Nat) := (formulaFields f).length
abbrev Column (f : PeriodicCNF Nat) := Fin (size f) → Bool
abbrev Window (f : PeriodicCNF Nat) := LocalWindow.Window (Column f) 2

def value (f : PeriodicCNF Nat) (a : Nat) (column : Column f) : Bool :=
  decide (∃ p : Fin (size f), (literalMarks 1 f.clauses).testBit p.val = true ∧
    (formulaFields f)[p.val]?.getD 0 = a ∧ column p = true)

@[simp] theorem value_true (f : PeriodicCNF Nat) (a : Nat) (column : Column f) :
    value f a column = true ↔ ∃ p : Fin (size f),
      (literalMarks 1 f.clauses).testBit p.val = true ∧
      (formulaFields f)[p.val]?.getD 0 = a ∧ column p = true := by simp [value]

theorem atom_represented (f : PeriodicCNF Nat) {c : PeriodicClause Nat} (hc : c ∈ f.clauses)
    {l : PeriodicLiteral Nat} (hl : l ∈ c) :
    ∃ p : Fin (size f), (literalMarks 1 f.clauses).testBit p.val = true ∧
      (formulaFields f)[p.val]?.getD 0 = l.atom := by
  obtain ⟨p,hp⟩ := (allLiteralEntries_members 1 f.clauses l).mpr ⟨c,hc,hl⟩
  have bound := (allLiteralEntries_bounds 1 f.clauses hp).2
  have hsize : p < size f := by simpa only [size,formulaFields,List.length_cons,Nat.add_comm] using bound
  exact ⟨⟨p,hsize⟩,(literalMarks_testBit _ _ _).mpr ⟨l,hp⟩,literalEntry_atom f hp⟩

theorem value_of_assignment (f : PeriodicCNF Nat) {c : PeriodicClause Nat} (hc : c ∈ f.clauses)
    {l : PeriodicLiteral Nat} (hl : l ∈ c) (assignment : Nat → Bool) :
    value f l.atom (fun p => assignment ((formulaFields f)[p.val]?.getD 0)) = assignment l.atom := by
  obtain ⟨p,hp,ha⟩ := atom_represented f hc hl
  cases h : assignment l.atom with
  | false =>
    apply Bool.eq_false_iff.mpr
    intro hv
    obtain ⟨q,hq,he,hv⟩ := (value_true _ _ _).mp hv
    change assignment ((formulaFields f)[q.val]?.getD 0) = true at hv
    rw [he,h] at hv
    contradiction
  | true =>
    apply (value_true _ _ _).mpr
    refine ⟨p,hp,ha,?_⟩
    change assignment ((formulaFields f)[p.val]?.getD 0) = true
    rw [ha]; exact h

def Valid (f : PeriodicCNF Nat) (window : Window f) : Prop :=
  ∀ c ∈ f.clauses, ∃ l ∈ c, value f l.atom (window (LineWindow.position c l)) = l.value

theorem satisfiable_iff (f : PeriodicCNF Nat) (locality : f.IsLocalOnLine) :
    f.SatisfiableOnLine ↔ LocalWindow.Satisfiable 2 (Valid f) := by
  constructor
  · rintro ⟨assignment,satisfies⟩
    refine ⟨fun x p => assignment ((formulaFields f)[p.val]?.getD 0) x,?_⟩
    intro x c hc
    obtain ⟨l,hl,holds⟩ := satisfies (x+1-LineWindow.anchor c) c hc
    refine ⟨l,hl,?_⟩
    change value f l.atom (fun p => assignment ((formulaFields f)[p.val]?.getD 0)
      (x+(LineWindow.position c l).val)) = l.value
    rw [value_of_assignment f hc hl (fun a => assignment a (x+(LineWindow.position c l).val))]
    have pos := LineWindow.position_eq (locality c hc) hl
    change assignment l.atom ((x+1-LineWindow.anchor c)+l.offset.1) = l.value at holds
    have coords : x+(LineWindow.position c l).val = (x+1-LineWindow.anchor c)+l.offset.1 := by omega
    rw [coords]; exact holds
  · rintro ⟨configuration,valid⟩
    refine ⟨fun a x => value f a (configuration x),?_⟩
    intro x c hc
    obtain ⟨l,hl,holds⟩ := valid (x+LineWindow.anchor c-1) c hc
    refine ⟨l,hl,?_⟩
    have pos := LineWindow.position_eq (locality c hc) hl
    change value f l.atom (configuration ((x+LineWindow.anchor c-1)+(LineWindow.position c l).val)) = l.value at holds
    change value f l.atom (configuration (x+l.offset.1)) = l.value
    have coords : (x+LineWindow.anchor c-1)+(LineWindow.position c l).val = x+l.offset.1 := by omega
    rw [coords] at holds
    exact holds

def decodeWord (f : PeriodicCNF Nat) (word : Nat) : Window f :=
  fun c p => word.testBit (finProdFinEquiv (c,p)).val

def encodeWindow (f : PeriodicCNF Nat) (w : Window f) : Nat :=
  (BitVec.ofBoolListLE (List.ofFn fun i : Fin (3*size f) =>
    w (finProdFinEquiv.symm i).1 (finProdFinEquiv.symm i).2)).toNat

theorem decodeWord_encodeWindow (f : PeriodicCNF Nat) (w : Window f) :
    decodeWord f (encodeWindow f w) = w := by
  funext c p
  simp only [decodeWord,encodeWindow,BitVec.testBit_toNat,BitVec.getLsbD_ofBoolListLE,
    List.getD_eq_getElem?_getD,List.getElem?_ofFn]
  rw [dif_pos (finProdFinEquiv (c,p)).isLt]
  change w (finProdFinEquiv.symm (finProdFinEquiv (c,p))).1
    (finProdFinEquiv.symm (finProdFinEquiv (c,p))).2 = w c p
  rw [Equiv.symm_apply_apply]

theorem encodeWindow_lt (f : PeriodicCNF Nat) (w : Window f) :
    encodeWindow f w < 2^(3*size f) := by
  have h := (BitVec.ofBoolListLE (List.ofFn fun i : Fin (3*size f) =>
    w (finProdFinEquiv.symm i).1 (finProdFinEquiv.symm i).2)).isLt
  simpa [encodeWindow] using h

def packedTransition (f : PeriodicCNF Nat) (first second : Nat) : Prop :=
  LocalWindow.Transition (Valid f) (decodeWord f first) (decodeWord f second)

abbrev PackedState (f : PeriodicCNF Nat) := Fin (2^(3*size f))

theorem satisfiable_iff_packed_cycle (f : PeriodicCNF Nat)
    (horizontal : f.IsOneDimensional) (locality : f.IsLocalOnLine) :
    f.Satisfiable ↔ FiniteState.HasCycle
      (fun a b : PackedState f => packedTransition f a.val b.val) := by
  rw [PeriodicCNF.satisfiable_iff_satisfiableOnLine horizontal,satisfiable_iff f locality,
    LocalWindow.satisfiable_iff_cycle]
  constructor
  · rintro ⟨period,states,step⟩
    refine ⟨period,fun i => ⟨encodeWindow f (states i),encodeWindow_lt f (states i)⟩,?_⟩
    intro i
    simpa only [packedTransition,decodeWord_encodeWindow] using step i
  · rintro ⟨period,states,step⟩
    exact ⟨period,fun i => decodeWord f (states i).val,step⟩

end LeanTrominoes.PeriodicCNF.FieldWindow
