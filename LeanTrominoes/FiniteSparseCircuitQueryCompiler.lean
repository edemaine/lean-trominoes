/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.FiniteDrawingCircuit
import LeanTrominoes.CompletionSparseDrawing
import LeanTrominoes.UnaryColumnPairCompiler
import LeanTrominoes.UnaryColumnSignedEncoding
import LeanTrominoes.UnaryColumnLookupSupport

/-! # Polynomial-time signed-coordinate queries in a finite sparse drawing -/
noncomputable section
namespace LeanTrominoes.CompletionPattern.Runtime.FiniteDrawing
open _root_.Computability Turing UnaryColumn Gadget Gadget.PeriodicOrthogonalDrawing LBricks
set_option maxHeartbeats 2000000

def decodeKey (key : Nat) : Cell :=
  ((Encodable.decode (α := Int) (Nat.unpair key).1).getD 0,
    (Encodable.decode (α := Int) (Nat.unpair key).2).getD 0)

@[simp] theorem decodeKey_pair (c : Cell) :
    decodeKey (Nat.pair (Encodable.encode c.1) (Encodable.encode c.2))=c := by
  simp [decodeKey]
  change (Equiv.intEquivNat.symm (Equiv.intEquivNat c.1),
    Equiv.intEquivNat.symm (Equiv.intEquivNat c.2))=c
  simp

private theorem lookup_mem {entries : List DrawingEntry} {c : Cell} {v : OrthogonalCellType}
    (eq : entries.lookup c=some v) : (c,v)∈entries := by
  induction entries with
  | nil => simp at eq
  | cons a entries ih =>
    obtain ⟨p,k⟩ := a
    by_cases h : c=p
    · subst p
      simp only [List.lookup_cons,beq_self_eq_true,Option.some.injEq] at eq
      subst k
      simp
    · have beq : (c==p)=false := beq_eq_false_iff_ne.mpr h
      simp only [List.lookup_cons,beq] at eq
      exact List.mem_cons_of_mem _ (ih eq)

variable {Symbol Index : Type} [Fintype Symbol] [Inhabited Symbol]
  {rows : List Symbol → List Index} {query : List Symbol → Index → Cell}
  {drawing : List Symbol → PeriodicOrthogonalDrawing} {entries : List Symbol → List DrawingEntry}

/-- Negative and exterior queries return blank, without periodic wrapping. -/
def queryKindCompiler
    (qx : Compiler rows (fun s i => Encodable.encode (query s i).1))
    (qy : Compiler rows (fun s i => Encodable.encode (query s i).2))
    (ex : Compiler entries (fun _ a => a.1.1.toNat))
    (ey : Compiler entries (fun _ a => a.1.2.toNat))
    (ev : Compiler entries (fun _ a => (kindIndex (kindOf a.2)).val))
    (model : ∀ s,SparseModel (drawing s) (entries s)) :
    Compiler rows (fun s i => (kindIndex (finiteDrawingKinds (drawing s) (query s i))).val) := by
  let keys := pair (signedDifference ex (constant ex 0)) (signedDifference ey (constant ey 0))
  let queries := pair qx qy
  let datum := fun s key => (kindIndex (finiteDrawingKinds (drawing s) (decodeKey key))).val
  have key_eq (s : List Symbol) (a : DrawingEntry) (ha : a∈entries s) :
      Nat.pair (Encodable.encode ((a.1.1.toNat:Int)-(0:Nat)))
        (Encodable.encode ((a.1.2.toNat:Int)-(0:Nat)))=
      Nat.pair (Encodable.encode a.1.1) (Encodable.encode a.1.2) := by
    have bounds := (model s).bounds a ha
    have x : (a.1.1.toNat:Int)=a.1.1 := by omega
    have y : (a.1.2.toNat:Int)=a.1.2 := by omega
    simp only [x,y,Nat.cast_zero,sub_zero]
  let result := keyedSupported queries keys ev datum (by
    intro s a ha
    rw [key_eq s a ha]
    simp only [datum,decodeKey_pair]
    have inside := (model s).bounds a ha
    simp only [finiteDrawingKinds,Circuit.cutDomain,Circuit.rectangleInside,if_pos inside,
      drawingKinds,(model s).consistent a ha]) (by
    intro s i hi missing
    simp only [datum,decodeKey_pair]
    by_cases inside : Circuit.rectangleInside (drawing s).horizontalPeriod (drawing s).verticalPeriod (query s i)
    · have readback := (model s).lookup (query s i) inside
      have none : (entries s).lookup (query s i)=none := by
        cases found : (entries s).lookup (query s i) with
        | none => rfl
        | some v =>
          exfalso
          have member := lookup_mem found
          apply missing
          refine ⟨(query s i,v),member,?_⟩
          exact key_eq s _ member
      simp only [finiteDrawingKinds,Circuit.cutDomain,if_pos inside,drawingKinds,readback,none,Option.getD_none]
      rfl
    · simp only [finiteDrawingKinds,Circuit.cutDomain,if_neg inside]
      rfl)
  exact result.of_eq (fun s => by simp only [datum,decodeKey_pair])
end LeanTrominoes.CompletionPattern.Runtime.FiniteDrawing
