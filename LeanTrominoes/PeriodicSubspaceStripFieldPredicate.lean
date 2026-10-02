/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.PeriodicSubspaceStripEncoding
import LeanTrominoes.PeriodicSubspaceStripPacked
import LeanTrominoes.BoundedArithmeticLogic

/-! # A compiled transition test for arbitrary strip footprints -/
namespace LeanTrominoes.PeriodicSubspaceTiling.Strip.FieldPredicate
open BoundedArithmetic BoundedArithmetic.Expr Turing.ToPartrec

def field (depth : Nat) (index : Expr) : Expr := .load (index+.literal (5+depth))
def kind (depth : Nat) (r : Expr) : Expr := field depth (var (depth+2)+3*r)
def proto (depth : Nat) (r : Expr) : Expr := field depth (var (depth+2)+3*r+1)
def offset (depth : Nat) (r : Expr) : Expr := field depth (var (depth+2)+3*r+2)
def magnitude (a : Expr) : Expr := .ite (a%2) (a/2+1) (a/2)
def column (depth : Nat) (r : Expr) : Expr :=
  .ite ((offset depth r)%2) (var (depth+1)+(offset depth r)/2+1)
    (var (depth+1)-(offset depth r)/2)

/-- `r` and `col` use the context after the additional occurrence binder. -/
def selected (depth : Nat) (r col : Expr) : Expr := existsE (var depth)
  (andE (eqE (kind (depth+1) (var 0)) (kind (depth+1) r))
    (.testBit (var (depth+4)) (var 0+var (depth+1)*col)))

def bounds : Expr := .all (var 0) (leE (magnitude (offset 1 (var 0))) (var 2))
def contained : Expr := .all (var 0)
  (impE (selected 1 (var 1) (var 3))
    (existsE (var 3) (eqE (field 2 (var 0)) (proto 2 (var 1)))))
def covered : Expr := .all (var 2)
  (existsE (var 1) (andE (eqE (proto 2 (var 0)) (field 2 (var 1)))
    (selected 2 (var 1) (column 3 (var 1)))))
def unique : Expr :=
  let inTarget := existsE (var 4) (eqE (field 3 (var 0)) (proto 3 (var 2)))
  let both := andE (selected 2 (var 2) (column 3 (var 2)))
    (selected 2 (var 1) (column 3 (var 1)))
  let premise := andE inTarget (andE (eqE (proto 2 (var 1)) (proto 2 (var 0))) both)
  let conclusion := andE (eqE (kind 2 (var 1)) (kind 2 (var 0)))
    (eqE (offset 2 (var 1)) (offset 2 (var 0)))
  .all (var 0) (.all (var 1) (impE premise conclusion))
def mandatory : Expr := .all (field 0 (var 2+3*var 0)) (.all (var 1)
  (impE (eqE (kind 2 (var 0)) (field 2 (var 4+3*var 2+1+var 1)))
    (selected 2 (var 1) (var 4))))
def overlap : Expr := .all (2*var 1) (.all (var 1)
  (eqE (.testBit (var 5) (var 0+var 2*(var 1+1)))
    (.testBit (var 6) (var 0+var 2*var 1))))
def transition : Expr := andE bounds (andE contained (andE covered (andE unique (andE mandatory overlap))))
def decision : Expr := .ite transition 1 0
theorem decision_noPower : decision.noPower=true := by decide

def context (n bound count first second : Nat) (fields : List Nat) : List Nat :=
  [n,bound,count,first,second]++fields
def input (data : Input) (first second : Nat) : List Nat :=
  context data.2.1.2.length data.1 data.2.1.1.length first second
    (Encoding.dataFields data.2.1 ++ (data.2.2.length :: data.2.2))
def magnitudeCode (z : Nat) : Nat := if z%2=0 then z/2 else z/2+1
def columnCode (bound z : Nat) : Nat := if z%2=0 then bound-z/2 else bound+z/2+1
def Atom (n count word col row : Nat) (fields : List Nat) : Prop :=
  ∃ i<n, fields[count+3*i]?.getD 0=fields[count+3*row]?.getD 0 ∧
    word.testBit (i+n*col)=true
def Bounds (n bound count : Nat) (fields : List Nat) : Prop :=
  ∀ i<n, magnitudeCode (fields[count+3*i+2]?.getD 0) ≤ bound
def Contained (n bound count word : Nat) (fields : List Nat) : Prop :=
  ∀ i<n, Atom n count word bound i fields →
    ∃ q<count, fields[q]?.getD 0=fields[count+3*i+1]?.getD 0
def Covered (n bound count word : Nat) (fields : List Nat) : Prop :=
  ∀ q<count, ∃ i<n, fields[count+3*i+1]?.getD 0=fields[q]?.getD 0 ∧
    Atom n count word (columnCode bound (fields[count+3*i+2]?.getD 0)) i fields
def Unique (n bound count word : Nat) (fields : List Nat) : Prop :=
  ∀ i<n, ∀ j<n, (∃ q<count, fields[q]?.getD 0=fields[count+3*i+1]?.getD 0) →
    fields[count+3*i+1]?.getD 0=fields[count+3*j+1]?.getD 0 →
    Atom n count word (columnCode bound (fields[count+3*i+2]?.getD 0)) i fields →
    Atom n count word (columnCode bound (fields[count+3*j+2]?.getD 0)) j fields →
      fields[count+3*i]?.getD 0=fields[count+3*j]?.getD 0 ∧
      fields[count+3*i+2]?.getD 0=fields[count+3*j+2]?.getD 0
def Mandatory (n bound count word : Nat) (fields : List Nat) : Prop :=
  ∀ p<fields[count+3*n]?.getD 0, ∀ r<n,
    fields[count+3*r]?.getD 0=fields[count+3*n+1+p]?.getD 0 →
      Atom n count word bound r fields
def Overlap (n bound first second : Nat) : Prop :=
  ∀ c<2*bound, ∀ i<n, first.testBit (i+n*(c+1))=second.testBit (i+n*c)

theorem field_eval (depth : Nat) (index : Expr) (front fields : List Nat)
    (length : front.length=5+depth) :
    (field depth index).eval (front++fields)=fields[index.eval (front++fields)]?.getD 0 := by
  simp only [field,Expr.eval,Op.eval]
  rw [List.getElem?_append_right (by omega)]
  congr 2; omega

@[simp] theorem field0 (index : Expr) (n b t a z : Nat) (fields : List Nat) :
    (field 0 index).eval (context n b t a z fields)=
      fields[index.eval (context n b t a z fields)]?.getD 0 :=
  field_eval 0 index [n,b,t,a,z] fields rfl
@[simp] theorem field1 (index : Expr) (r n b t a z : Nat) (fields : List Nat) :
    (field 1 index).eval (r::context n b t a z fields)=
      fields[index.eval (r::context n b t a z fields)]?.getD 0 :=
  field_eval 1 index [r,n,b,t,a,z] fields rfl
@[simp] theorem field2 (index : Expr) (s r n b t a z : Nat) (fields : List Nat) :
    (field 2 index).eval (s::r::context n b t a z fields)=
      fields[index.eval (s::r::context n b t a z fields)]?.getD 0 :=
  field_eval 2 index [s,r,n,b,t,a,z] fields rfl
@[simp] theorem field3 (index : Expr) (i s r n b t a z : Nat) (fields : List Nat) :
    (field 3 index).eval (i::s::r::context n b t a z fields)=
      fields[index.eval (i::s::r::context n b t a z fields)]?.getD 0 :=
  field_eval 3 index [i,s,r,n,b,t,a,z] fields rfl
theorem magnitude_eval (e : Expr) (values : List Nat) :
    (magnitude e).eval values=magnitudeCode (e.eval values) := rfl

@[simp] theorem selected1_correct (r n b t a z : Nat) (fields : List Nat) :
    (selected 1 (var 1) (var 3)).Truth (r::context n b t a z fields) ↔ Atom n t a b r fields := by
  simp only [selected,truth_exists,truth_and,truth_eq,truth_bit,kind,field2]
  simp [Atom,context,field,Expr.eval,Op.eval]
@[simp] theorem selected2_first (s r n b t a z : Nat) (fields : List Nat) :
    (selected 2 (var 2) (column 3 (var 2))).Truth (s::r::context n b t a z fields) ↔
      Atom n t a (columnCode b (fields[t+3*r+2]?.getD 0)) r fields := by
  simp only [selected,truth_exists,truth_and,truth_eq,truth_bit,kind,column,offset,field3]
  simp [Atom,context,columnCode,field,Expr.eval,Op.eval]
@[simp] theorem selected2_second (s r n b t a z : Nat) (fields : List Nat) :
    (selected 2 (var 1) (column 3 (var 1))).Truth (s::r::context n b t a z fields) ↔
      Atom n t a (columnCode b (fields[t+3*s+2]?.getD 0)) s fields := by
  simp only [selected,truth_exists,truth_and,truth_eq,truth_bit,kind,column,offset,field3]
  simp [Atom,context,columnCode,field,Expr.eval,Op.eval]
@[simp] theorem selected2_center (r p n b t a z : Nat) (fields : List Nat) :
    (selected 2 (var 1) (var 4)).Truth (r::p::context n b t a z fields) ↔
      Atom n t a b r fields := by
  simp only [selected,truth_exists,truth_and,truth_eq,truth_bit,kind]
  simp [Atom,context,field,Expr.eval,Op.eval]
@[simp] theorem mandatory_correct (n b t a z : Nat) (fields : List Nat) :
    mandatory.Truth (context n b t a z fields) ↔ Mandatory n b t a fields := by
  simp only [mandatory,truth_all,truth_imp,truth_eq,kind,field0,field2,selected2_center]
  simp [Mandatory,context,Expr.eval,Op.eval]
@[simp] theorem bounds_correct (n b t a z : Nat) (fields : List Nat) :
    bounds.Truth (context n b t a z fields) ↔ Bounds n b t fields := by
  simp only [bounds,truth_all,truth_le,magnitude_eval,offset,field1]
  simp [Bounds,context,Expr.eval,Op.eval]
@[simp] theorem contained_correct (n b t a z : Nat) (fields : List Nat) :
    contained.Truth (context n b t a z fields) ↔ Contained n b t a fields := by
  simp only [contained,truth_all,truth_imp,selected1_correct,truth_exists,truth_eq,proto,field2]
  simp [Contained,context,Expr.eval,Op.eval]
@[simp] theorem covered_correct (n b t a z : Nat) (fields : List Nat) :
    covered.Truth (context n b t a z fields) ↔ Covered n b t a fields := by
  simp only [covered,truth_all,truth_exists,truth_and,truth_eq,proto,field2,selected2_second]
  simp [Covered,context,Expr.eval,Op.eval]
@[simp] theorem unique_correct (n b t a z : Nat) (fields : List Nat) :
    unique.Truth (context n b t a z fields) ↔ Unique n b t a fields := by
  simp only [unique,truth_all,truth_imp,truth_and,truth_eq,truth_exists,proto,kind,offset,field2,field3,
    selected2_first,selected2_second]
  simp [Unique,and_imp,context,Expr.eval,Op.eval]
private theorem bool_toNat_eq (a b : Bool) : a.toNat=b.toNat ↔ a=b := by cases a <;> cases b <;> decide

@[simp] theorem overlap_correct (n b t a z : Nat) (fields : List Nat) :
    overlap.Truth (context n b t a z fields) ↔ Overlap n b a z := by
  simp only [overlap,truth_all,truth_eq]
  simp [Overlap,context,Expr.eval,Op.eval,bool_toNat_eq]
theorem transition_correct (n b t a z : Nat) (fields : List Nat) :
    transition.Truth (context n b t a z fields) ↔
      Bounds n b t fields ∧ Contained n b t a fields ∧ Covered n b t a fields ∧
        Unique n b t a fields ∧ Mandatory n b t a fields ∧ Overlap n b a z := by simp [transition]

end LeanTrominoes.PeriodicSubspaceTiling.Strip.FieldPredicate
