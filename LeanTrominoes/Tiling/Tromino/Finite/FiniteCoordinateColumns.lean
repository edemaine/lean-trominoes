/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.Computation.Encoding.Unary.UnarySortedTripleCompiler
import LeanTrominoes.Tiling.Completion.CompletionStripEncoding
import LeanTrominoes.Tiling.Tromino.Finite.FiniteTrominoVerifierBackend

/-! # Explicit unary coordinate columns for finite tromino instances

Each coordinate uses the canonical natural code of its signed integer, supplied
in unary. Field tags separate region coordinates, preplacement coordinates,
and symmetry codes. Certificate bits have their own tag.
-/
namespace LeanTrominoes.Tromino.FiniteCoordinateColumns
open _root_.Computability Turing
open UnaryFieldEncoderMachine (unaryFields)

structure Input where
  cells : List Cell
  prefill : List (Placement Unit)

inductive Field
  | regionX | regionY | prefillSymmetry | prefillX | prefillY
  deriving DecidableEq, Fintype, Inhabited

inductive Token
  | field (column : Field) (symbol : UnaryFieldEncoderMachine.Symbol)
  | bit (value : Bool)
  deriving DecidableEq, Fintype, Inhabited

def fields : List Field := [.regionX,.regionY,.prefillSymmetry,.prefillX,.prefillY]

def values (input : Input) : Field → List Nat
  | .regionX => input.cells.map fun cell => Encodable.encode cell.1
  | .regionY => input.cells.map fun cell => Encodable.encode cell.2
  | .prefillSymmetry => input.prefill.map fun p => CompletionStripEncoding.symmetryCode p.symmetry
  | .prefillX => input.prefill.map fun p => Encodable.encode p.offset.1
  | .prefillY => input.prefill.map fun p => Encodable.encode p.offset.2

def encodeInput (input : Input) : List Token :=
  fields.flatMap fun column => (unaryFields (values input column)).map (Token.field column)

def encode (input : Input × List Bool) : List Token :=
  encodeInput input.1 ++ input.2.map Token.bit

def projection (column : Field) : Token → List UnaryFieldEncoderMachine.Symbol
  | .field other symbol => if column=other then [symbol] else []
  | .bit _ => []

@[simp] theorem projection_column (column other : Field) (source : List UnaryFieldEncoderMachine.Symbol) :
    (source.map (Token.field other)).flatMap (projection column) =
      if column=other then source else [] := by
  by_cases h : column=other <;> simp [List.flatMap_map,projection,h]

private theorem flatMap_empty {α β : Type} (source : List α) :
    source.flatMap (fun _ => ([] : List β)) = [] := by
  induction source <;> simp_all

@[simp] theorem projection_encode (column : Field) (input : Input × List Bool) :
    (encode input).flatMap (projection column) = unaryFields (values input.1 column) := by
  cases column <;> simp [encode,encodeInput,fields,List.flatMap_map,projection,flatMap_empty]

noncomputable def columnComputableInPolyTime (column : Field) :
    TM2ComputableInPolyTime encode unaryFields (fun input => values input.1 column) := by
  let prepared := TM2PolyTimeInputEncodingTransport.of_prepare encode
    (FiniteBlockTransducer.computableInPolyTime (projection column))
    (fun _ => rfl) (fun _ => rfl)
  exact TM2PolyTimeOutputEncodingTransport.of_identity_output_eq prepared (projection_encode column)

noncomputable def regionX :
    EncodedUnaryColumn.Compiler encode (fun input => input.1.cells)
      (fun _ cell => Encodable.encode cell.1) := columnComputableInPolyTime .regionX
noncomputable def regionY :
    EncodedUnaryColumn.Compiler encode (fun input => input.1.cells)
      (fun _ cell => Encodable.encode cell.2) := columnComputableInPolyTime .regionY
noncomputable def prefillX :
    EncodedUnaryColumn.Compiler encode (fun input => input.1.prefill)
      (fun _ p => Encodable.encode p.offset.1) := columnComputableInPolyTime .prefillX
noncomputable def prefillY :
    EncodedUnaryColumn.Compiler encode (fun input => input.1.prefill)
      (fun _ p => Encodable.encode p.offset.2) := columnComputableInPolyTime .prefillY
noncomputable def prefillSymmetry :
    EncodedUnaryColumn.Compiler encode (fun input => input.1.prefill)
      (fun _ p => CompletionStripEncoding.symmetryCode p.symmetry) :=
  columnComputableInPolyTime .prefillSymmetry

def positive (n : Nat) := n/2*(1-n%2)
def negative (n : Nat) := (n/2+1)*(n%2)

theorem positive_encode (z : Int) : positive (Encodable.encode z)=z.toNat := by
  cases z with
  | ofNat n =>
    change positive (2*n)=n
    simp [positive,Nat.mul_comm]
  | negSucc n =>
    change positive (2*n+1)=0
    simp [positive,Nat.add_div,Nat.mul_comm]

theorem negative_encode (z : Int) : negative (Encodable.encode z)=(-z).toNat := by
  cases z with
  | ofNat n =>
    change negative (2*n)=(-Int.ofNat n).toNat
    simp [negative,Nat.mul_comm]
  | negSucc n =>
    change negative (2*n+1)=n+1
    simp [negative,Nat.add_div,Nat.mul_comm]

theorem positive_sub_negative (z : Int) :
    (positive (Encodable.encode z):Int)-negative (Encodable.encode z)=z := by
  rw [positive_encode,negative_encode]
  omega

end LeanTrominoes.Tromino.FiniteCoordinateColumns

noncomputable section
namespace LeanTrominoes.EncodedUnaryColumn
open _root_.Computability Turing
variable {Input Symbol Index : Type} [Fintype Symbol] [Inhabited Symbol]
  {encodeInput : Input → List Symbol} {rows : Input → List Index} {f : Input → Index → Nat}

private def parity (c : Compiler encodeInput rows f) :
    Compiler encodeInput rows (fun s i => f s i%2) :=
  (residue c 2 (by decide) (fun i => i.val)).of_eq (fun _ => rfl)

def signedPositive (c : Compiler encodeInput rows f) :
    Compiler encodeInput rows (fun s i => Tromino.FiniteCoordinateColumns.positive (f s i)) :=
  multiply (halve c) (sub (constant c 1) (parity c))

def signedNegative (c : Compiler encodeInput rows f) :
    Compiler encodeInput rows (fun s i => Tromino.FiniteCoordinateColumns.negative (f s i)) :=
  multiply (add (halve c) (constant c 1)) (parity c)

end LeanTrominoes.EncodedUnaryColumn
