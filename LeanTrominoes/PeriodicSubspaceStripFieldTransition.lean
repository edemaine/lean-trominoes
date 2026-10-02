/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.PeriodicSubspaceStripFieldPredicate

/-! # Correctness of the native finite-footprint strip transition -/
namespace LeanTrominoes.PeriodicSubspaceTiling.Strip.FieldPredicate
open Turing.ToPartrec BoundedArithmetic

theorem recordFields_get (rs : List ((Nat × Nat) × Int)) (tail : List Nat)
    (i : Nat) (axis : Fin 3) (hi : i<rs.length) :
    (rs.flatMap Encoding.recordFields ++ tail)[3*i+axis.val]?.getD 0 =
      (Encoding.recordFields rs[i])[axis.val]?.getD 0 := by
  induction rs generalizing i with
  | nil => simp at hi
  | cons r rs ih =>
    cases i with
    | zero => fin_cases axis <;> simp [Encoding.recordFields]
    | succ i =>
      have h := ih i (by simpa using hi)
      have address : 3*(i+1)+axis.val=(3*i+axis.val)+1+1+1 := by omega
      simpa [Encoding.recordFields,address] using h

def nativeFields (f : Input) : List Nat := Encoding.dataFields f.2.1 ++ (f.2.2.length :: f.2.2)

theorem record_field (f : Input) (i : Nat) (hi : i<f.2.1.2.length) (axis : Fin 3) :
    (nativeFields f)[f.2.1.1.length+3*i+axis.val]?.getD 0 =
      (Encoding.recordFields f.2.1.2[i])[axis.val]?.getD 0 := by
  simp only [nativeFields,Encoding.dataFields,List.append_assoc]
  rw [List.getElem?_append_right (by omega)]
  have address : f.2.1.1.length+3*i+axis.val-f.2.1.1.length=3*i+axis.val := by omega
  rw [address]
  exact recordFields_get f.2.1.2 (f.2.2.length :: f.2.2) i axis hi

@[simp] theorem kind_field (f : Input) (i : Nat) (hi : i<f.2.1.2.length) :
    (nativeFields f)[f.2.1.1.length+3*i]?.getD 0=f.2.1.2[i].1.1 := by
  simpa [Encoding.recordFields] using record_field f i hi 0
@[simp] theorem proto_field (f : Input) (i : Nat) (hi : i<f.2.1.2.length) :
    (nativeFields f)[f.2.1.1.length+3*i+1]?.getD 0=f.2.1.2[i].1.2 := by
  simpa [Encoding.recordFields] using record_field f i hi 1
@[simp] theorem offset_field (f : Input) (i : Nat) (hi : i<f.2.1.2.length) :
    (nativeFields f)[f.2.1.1.length+3*i+2]?.getD 0=Encodable.encode f.2.1.2[i].2 := by
  simpa [Encoding.recordFields] using record_field f i hi 2
@[simp] theorem target_field (f : Input) (q : Nat) (hq : q<f.2.1.1.length) :
    (nativeFields f)[q]?.getD 0=f.2.1.1[q] := by
  simp only [nativeFields,Encoding.dataFields,List.append_assoc]
  rw [List.getElem?_append_left hq,List.getElem?_eq_getElem hq,Option.getD_some]

@[simp] theorem magnitude_encode (z : Int) : magnitudeCode (Encodable.encode z)=z.natAbs := by
  cases z with
  | ofNat n => change (if (2*n)%2=0 then (2*n)/2 else (2*n)/2+1)=n; simp
  | negSucc n => change (if (2*n+1)%2=0 then (2*n+1)/2 else (2*n+1)/2+1)=n+1; simp; omega

theorem column_encode (bound : Nat) (z : Int) (hz : z.natAbs≤bound) :
    columnCode bound (Encodable.encode z)=(position bound (0,-z)).val := by
  change columnCode bound (Encodable.encode z)=((bound : Int)+ -z).toNat % (2*bound+1)
  have small : ((bound : Int)+ -z).toNat < 2*bound+1 := by omega
  rw [Nat.mod_eq_of_lt small]
  cases z with
  | ofNat n =>
    change (if (2*n)%2=0 then bound-(2*n)/2 else bound+(2*n)/2+1)=((bound : Int)+ -(n : Int)).toNat
    simp only [Nat.mul_mod,Nat.mod_self,Nat.zero_mul,Nat.zero_mod,Nat.mul_div_cancel_left _ (by omega : 0<2),ite_true]
    omega
  | negSucc n =>
    change (if (2*n+1)%2=0 then bound-(2*n+1)/2 else bound+(2*n+1)/2+1)=((bound : Int)+ -Int.negSucc n).toNat
    simp only [Nat.add_mod,Nat.mul_mod,Nat.mod_self,Nat.zero_mul,Nat.zero_mod,Nat.zero_add]
    norm_num
    omega

theorem atom_native (f : Input) (word col row : Nat) (hr : row<f.2.1.2.length)
    (hc : col<2*f.1+1) :
    Atom f.2.1.2.length f.2.1.1.length word col row (nativeFields f) ↔
      value f.2.1 f.2.1.2[row].1.1 (decodeWord f.2.1 f.1 word ⟨col,hc⟩)=true := by
  simp only [Atom]
  simp only [value,decide_eq_true_eq,decodeWord]
  constructor
  · rintro ⟨i,hi,equal,selected⟩
    exact ⟨⟨i,hi⟩,by simpa only [Fin.getElem_fin,kind_field f i hi,kind_field f row hr] using equal,selected⟩
  · rintro ⟨i,equal,selected⟩
    exact ⟨i.val,i.isLt,by simpa only [Fin.getElem_fin,kind_field f i i.isLt,kind_field f row hr] using equal,selected⟩

def rowCandidate (f : Input) (i : Fin f.2.1.2.length) : Nat × Int :=
  (f.2.1.2[i].1.1,-f.2.1.2[i].2)

theorem candidate_rows (f : Input) (q : Nat) (c : Nat × Int) :
    c∈candidates f.2.1 q ↔ ∃ i : Fin f.2.1.2.length, f.2.1.2[i].1.2=q ∧ c=rowCandidate f i := by
  constructor
  · intro hc
    obtain ⟨r,hr,hq,eq⟩ := candidate_record f.2.1 hc
    obtain ⟨i,hi,record⟩ := List.mem_iff_getElem.mp hr
    exact ⟨⟨i,hi⟩,by simpa only [Fin.getElem_fin,record] using hq,by simpa only [rowCandidate,Fin.getElem_fin,record] using eq⟩
  · rintro ⟨i,hq,rfl⟩
    apply List.mem_filterMap.mpr
    exact ⟨f.2.1.2[i],List.getElem_mem i.isLt,by
      change (if f.2.1.2[i.val].1.2=q then some _ else none)=some _
      have hq : f.2.1.2[i.val].1.2=q := hq
      rw [if_pos hq]; rfl⟩

def rowSelected (f : Input) (word : Nat) (i : Fin f.2.1.2.length) : Prop :=
  value f.2.1 (rowCandidate f i).1
    (decodeWord f.2.1 f.1 word (position f.1 (rowCandidate f i)))=true

theorem row_atom (f : Input) (bounded : Bounded f.2.1 f.1) (word : Nat)
    (i : Nat) (hi : i<f.2.1.2.length) :
    Atom f.2.1.2.length f.2.1.1.length word
      (columnCode f.1 ((nativeFields f)[f.2.1.1.length+3*i+2]?.getD 0)) i (nativeFields f) ↔
        rowSelected f word ⟨i,hi⟩ := by
  rw [offset_field f i hi,column_encode f.1 _ (bounded _ (List.getElem_mem hi))]
  have eq : position f.1 (0,-f.2.1.2[i].2)=position f.1 (rowCandidate f ⟨i,hi⟩) := rfl
  rw [eq,atom_native f word _ i hi (position f.1 _).isLt]
  rfl

theorem bounds_native (f : Input) :
    Bounds f.2.1.2.length f.1 f.2.1.1.length (nativeFields f) ↔ Bounded f.2.1 f.1 := by
  simp +contextual only [Bounds,offset_field,magnitude_encode,Bounded,List.mem_iff_getElem]
  constructor
  · intro h r hr
    obtain ⟨i,hi,rfl⟩ := hr
    exact h i hi
  · intro h i hi
    exact h _ ⟨i,hi,rfl⟩

theorem contained_native (f : Input) (word : Nat) :
    Contained f.2.1.2.length f.1 f.2.1.1.length word (nativeFields f) ↔
    ∀ r∈f.2.1.2, value f.2.1 r.1.1 (decodeWord f.2.1 f.1 word (center f.1))=true → r.1.2∈f.2.1.1 := by
  simp +contextual only [Contained,proto_field,target_field,atom_native f word f.1 _ _ (by omega)]
  constructor
  · intro h r hr selected
    obtain ⟨i,hi,rfl⟩ := List.mem_iff_getElem.mp hr
    obtain ⟨q,hq,equal⟩ := h i hi selected
    rw [target_field f q hq] at equal
    exact equal ▸ List.getElem_mem hq
  · intro h i hi selected
    obtain ⟨q,hq,equal⟩ := List.mem_iff_getElem.mp (h _ (List.getElem_mem hi) selected)
    exact ⟨q,hq,by simpa only [target_field f q hq] using equal⟩

theorem covering_native (f : Input) (bounded : Bounded f.2.1 f.1) (word : Nat) :
    Covered f.2.1.2.length f.1 f.2.1.1.length word (nativeFields f) ∧
      Unique f.2.1.2.length f.1 f.2.1.1.length word (nativeFields f) ↔
    ∀ q∈f.2.1.1, ∃! c, c∈candidates f.2.1 q ∧
      value f.2.1 c.1 (decodeWord f.2.1 f.1 word (position f.1 c))=true := by
  simp only [Covered,Unique]
  have atom (i : Nat) (hi : i<f.2.1.2.length) := row_atom f bounded word i hi
  constructor
  · rintro ⟨cover,unique⟩ q hq
    obtain ⟨j,hj,rfl⟩ := List.mem_iff_getElem.mp hq
    obtain ⟨i,hi,proto,selected⟩ := cover j hj
    rw [proto_field f i hi,target_field f j hj] at proto
    have selected := (atom i hi).mp selected
    refine ⟨rowCandidate f ⟨i,hi⟩,⟨(candidate_rows f _ _).mpr ⟨⟨i,hi⟩,by simpa only [Fin.getElem_fin] using proto,rfl⟩,selected⟩,?_⟩
    intro c hc
    obtain ⟨k,hk,rfl⟩ := (candidate_rows f _ _).mp hc.1
    have eq := unique k k.isLt i hi
      ⟨j,hj,by simpa only [target_field f j hj,proto_field f k k.isLt,Fin.getElem_fin] using hk.symm⟩
      (by simpa only [proto_field f k k.isLt,proto_field f i hi,Fin.getElem_fin] using hk.trans proto.symm)
      ((atom k k.isLt).mpr hc.2) ((atom i hi).mpr selected)
    simp only [kind_field f k k.isLt,kind_field f i hi,offset_field f k k.isLt,offset_field f i hi] at eq
    have offsetEq := Encodable.encode_injective eq.2
    simp only [rowCandidate,Fin.getElem_fin,Prod.mk.injEq]
    exact ⟨eq.1,congrArg Neg.neg offsetEq⟩
  · intro cover
    constructor
    · intro q hq
      obtain ⟨c,hc,_⟩ := cover _ (List.getElem_mem hq)
      obtain ⟨i,hi,rfl⟩ := (candidate_rows f _ _).mp hc.1
      exact ⟨i.val,i.isLt,
        by simpa only [proto_field f i i.isLt,target_field f q hq,Fin.getElem_fin] using hi,
        (atom i i.isLt).mpr hc.2⟩
    · intro i hi j hj target proto first second
      obtain ⟨q,hq,equal⟩ := target
      rw [target_field f q hq,proto_field f i hi] at equal
      rw [proto_field f i hi,proto_field f j hj] at proto
      have first := (atom i hi).mp first
      have second := (atom j hj).mp second
      have member : f.2.1.2[i].1.2∈f.2.1.1 := equal ▸ List.getElem_mem hq
      obtain ⟨c,hc,unique⟩ := cover _ member
      have ai := unique (rowCandidate f ⟨i,hi⟩)
        ⟨(candidate_rows f _ _).mpr ⟨⟨i,hi⟩,rfl,rfl⟩,first⟩
      have aj := unique (rowCandidate f ⟨j,hj⟩)
        ⟨(candidate_rows f _ _).mpr ⟨⟨j,hj⟩,by simpa only [Fin.getElem_fin] using proto.symm,rfl⟩,second⟩
      have eq := ai.trans aj.symm
      rw [kind_field f i hi,kind_field f j hj,offset_field f i hi,offset_field f j hj]
      exact ⟨by simpa only [rowCandidate,Fin.getElem_fin] using congrArg Prod.fst eq,
        congrArg Encodable.encode (neg_injective (congrArg Prod.snd eq))⟩

theorem overlap_native (f : Input) (a b : Nat) :
    Overlap f.2.1.2.length f.1 a b ↔ ∀ c : Fin (2*f.1),
      decodeWord f.2.1 f.1 a c.succ=decodeWord f.2.1 f.1 b c.castSucc := by
  constructor
  · intro h c
    funext i
    exact h c.val c.isLt i.val i.isLt
  · intro h c hc i hi
    exact congrFun (h ⟨c,hc⟩) ⟨i,hi⟩

theorem dataFields_length (data : Data) : (Encoding.dataFields data).length=data.1.length+3*data.2.length := by
  have rows (rs : List ((Nat × Nat) × Int)) : (rs.flatMap Encoding.recordFields).length=3*rs.length := by
    induction rs with
    | nil => rfl
    | cons r rs ih => simp [Encoding.recordFields,ih]; omega
  simp only [Encoding.dataFields,List.length_append,rows]

@[simp] theorem forced_count (f : Input) :
    (nativeFields f)[f.2.1.1.length+3*f.2.1.2.length]?.getD 0=f.2.2.length := by
  unfold nativeFields
  rw [← dataFields_length,List.getElem?_append_right (by omega)]
  simp

@[simp] theorem forced_field (f : Input) (p : Nat) (hp : p<f.2.2.length) :
    (nativeFields f)[f.2.1.1.length+3*f.2.1.2.length+1+p]?.getD 0=f.2.2[p] := by
  unfold nativeFields
  rw [← dataFields_length,List.getElem?_append_right (by omega)]
  have address : (Encoding.dataFields f.2.1).length+1+p-(Encoding.dataFields f.2.1).length=p+1 := by omega
  rw [address,List.getElem?_cons_succ,List.getElem?_eq_getElem hp,Option.getD_some]

theorem mandatory_native (f : Input) (word : Nat) :
    Mandatory f.2.1.2.length f.1 f.2.1.1.length word (nativeFields f) ↔
    ∀ r∈f.2.1.2, r.1.1∈f.2.2 → value f.2.1 r.1.1 (decodeWord f.2.1 f.1 word (center f.1))=true := by
  simp only [Mandatory,forced_count]
  constructor
  · intro h r hr hk
    obtain ⟨i,hi,rfl⟩ := List.mem_iff_getElem.mp hr
    obtain ⟨p,hp,equal⟩ := List.mem_iff_getElem.mp hk
    apply (atom_native f word f.1 i hi (by omega)).mp
    apply h p hp i hi
    simpa only [kind_field f i hi,forced_field f p hp] using equal.symm
  · intro h p hp i hi equal
    rw [kind_field f i hi,forced_field f p hp] at equal
    apply (atom_native f word f.1 i hi (by omega)).mpr
    exact h _ (List.getElem_mem hi) (equal ▸ List.getElem_mem hp)

theorem transition_native (f : Input) (a b : Nat) :
    transition.Truth (input f a b) ↔ Bounded f.2.1 f.1 ∧ packedCompletionTransition f.2 f.1 a b := by
  change transition.Truth (context _ _ _ _ _ (nativeFields f)) ↔ _
  rw [transition_correct,bounds_native,contained_native,mandatory_native,overlap_native]
  constructor
  · rintro ⟨bounded,contained,covered,unique,mandatory,overlap⟩
    exact ⟨bounded,⟨⟨contained,(covering_native f bounded a).mp ⟨covered,unique⟩⟩,mandatory⟩,overlap⟩
  · rintro ⟨bounded,⟨⟨contained,covering⟩,mandatory⟩,overlap⟩
    obtain ⟨covered,unique⟩ := (covering_native f bounded a).mpr covering
    exact ⟨bounded,contained,covered,unique,mandatory,overlap⟩

def check (f : Input) (a b : Nat) : Bool := decide (transition.eval (input f a b) ≠ 0)

theorem decision_eval (f : Input) (a b : Nat) :
    decision.eval (input f a b)=(check f a b).toNat := by
  by_cases h : transition.eval (input f a b)=0 <;> simp [decision,Expr.eval,check,h]

theorem check_true (f : Input) (a b : Nat) : check f a b=true ↔
    Bounded f.2.1 f.1 ∧ packedCompletionTransition f.2 f.1 a b := by
  simpa only [check,decide_eq_true_eq,Expr.Truth] using transition_native f a b

theorem cycle_iff (f : Input) :
    FiniteState.HasCycle (fun a b : Fin (2^Strip.bits f.2.1 f.1) => check f a b=true) ↔ Problem f := by
  constructor
  · rintro ⟨period,states,steps⟩
    have bounded := ((check_true f _ _).mp (steps 0)).1
    refine ⟨bounded,?_⟩
    apply (completable_iff_cycle f.2 f.1 bounded).mpr
    apply (packed_completion_cycle_iff f.2 f.1).mp
    exact ⟨period,states,fun i => ((check_true f _ _).mp (steps i)).2⟩
  · rintro ⟨bounded,tiled⟩
    obtain ⟨period,states,steps⟩ := (packed_completion_cycle_iff f.2 f.1).mpr
      ((completable_iff_cycle f.2 f.1 bounded).mp tiled)
    exact ⟨period,states,fun i => (check_true f _ _).mpr ⟨bounded,steps i⟩⟩

end LeanTrominoes.PeriodicSubspaceTiling.Strip.FieldPredicate
