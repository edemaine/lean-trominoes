/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.FiniteCoordinateColumns

/-! # Decoding and finite alphabets for explicit unary coordinate inputs -/
namespace LeanTrominoes.Tromino.FiniteCoordinateColumns
open _root_.Computability
open UnaryFieldEncoderMachine (unaryFields)

def symbolBool : UnaryFieldEncoderMachine.Symbol → Bool
  | .unit => true
  | .delimiter => false

theorem unaryFields_bool (numbers : List Nat) :
    (unaryFields numbers).map symbolBool=CompletionStripEncoding.unaryFields numbers := by
  induction numbers with
  | nil => rfl
  | cons n ns ih =>
    simp [UnaryFieldEncoderMachine.unaryFields_cons,UnaryFieldEncoderMachine.unaryField,
      CompletionStripEncoding.unaryFields,List.map_replicate,symbolBool,ih]

def readColumn (column : Field) (source : List Token) : Option (List Nat) :=
  CompletionStripEncoding.decodeUnaryAux 0 ((source.flatMap (projection column)).map symbolBool)

@[simp] theorem readColumn_encode (column : Field) (input : Input) :
    readColumn column (encodeInput input)=some (values input column) := by
  have projected := projection_encode column (input,[])
  simp only [encode,List.map_nil,List.append_nil] at projected
  rw [readColumn,projected,unaryFields_bool,CompletionStripEncoding.decodeUnaryAux_unaryFields]

def readCells : List Nat → List Nat → Option (List Cell)
  | [],[] => some []
  | x::xs,y::ys => do
      let x ← Encodable.decode (α := Int) x
      let y ← Encodable.decode (α := Int) y
      let rest ← readCells xs ys
      pure ((x,y)::rest)
  | _,_ => none

@[simp] theorem readCells_codes (cells : List Cell) :
    readCells (cells.map fun c => Encodable.encode c.1) (cells.map fun c => Encodable.encode c.2)=
      some cells := by
  induction cells with
  | nil => rfl
  | cons cell cells ih =>
    rcases cell with ⟨x,y⟩
    simp [readCells,ih]
    change Equiv.intEquivNat.symm (Equiv.intEquivNat x)=x ∧
      Equiv.intEquivNat.symm (Equiv.intEquivNat y)=y
    simp

def readPrefill : List Nat → List Nat → List Nat → Option (List (Placement Unit))
  | [],[],[] => some []
  | s::ss,x::xs,y::ys => do
      let symmetry ← CompletionStripEncoding.decodeSymmetry s
      let x ← Encodable.decode (α := Int) x
      let y ← Encodable.decode (α := Int) y
      let rest ← readPrefill ss xs ys
      pure (⟨(),symmetry,(x,y)⟩::rest)
  | _,_,_ => none

@[simp] theorem readPrefill_codes (prefill : List (Placement Unit)) :
    readPrefill (prefill.map fun p => CompletionStripEncoding.symmetryCode p.symmetry)
      (prefill.map fun p => Encodable.encode p.offset.1)
      (prefill.map fun p => Encodable.encode p.offset.2)=some prefill := by
  induction prefill with
  | nil => rfl
  | cons p ps ih =>
    rcases p with ⟨⟨⟩,s,x,y⟩
    simp [readPrefill,ih]
    change Equiv.intEquivNat.symm (Equiv.intEquivNat x)=x ∧
      Equiv.intEquivNat.symm (Equiv.intEquivNat y)=y
    simp

def decodeInput (source : List Token) : Option Input := do
  let xs ← readColumn .regionX source
  let ys ← readColumn .regionY source
  let ss ← readColumn .prefillSymmetry source
  let px ← readColumn .prefillX source
  let py ← readColumn .prefillY source
  let cells ← readCells xs ys
  let prefill ← readPrefill ss px py
  pure ⟨cells,prefill⟩

@[simp] theorem decodeInput_encodeInput (input : Input) :
    decodeInput (encodeInput input)=some input := by
  rcases input with ⟨cells,prefill⟩
  simp [decodeInput,values]

def finEncoding : FiniteEncoding Input where
  Γ := Token
  ΓFin := inferInstance
  encoding := {
    encode := encodeInput
    decode := decodeInput
    decode_encode := decodeInput_encodeInput }

def regionEncoding : FiniteEncoding (List Cell) where
  Γ := Token
  ΓFin := inferInstance
  encoding := {
    encode cells := encodeInput ⟨cells,[]⟩
    decode source := (decodeInput source).map Input.cells
    decode_encode cells := by simp }

end LeanTrominoes.Tromino.FiniteCoordinateColumns
