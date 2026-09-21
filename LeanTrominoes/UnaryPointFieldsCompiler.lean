/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.UnaryColumnSignedEncoding
import LeanTrominoes.PeriodicDrawingArithmeticFields

/-! # Serializing signed point columns to the native drawing fields -/
noncomputable section
namespace LeanTrominoes.UnaryColumn
open Computability Turing
open UnaryFieldEncoderMachine (unaryFields)
variable {Symbol Index : Type} [Fintype Symbol] [Inhabited Symbol]
  {rows : List Symbol → List Index} {f g : List Symbol → Index → Nat}

def pairFields (first : Compiler rows f) (second : Compiler rows g) :
    TM2ComputableInPolyTime id unaryFields (fun s => (rows s).flatMap fun i => [f s i,g s i]) := by
  let result := finishBlocks (appendBlocks (blocks first) (blocks second))
  apply TM2PolyTimeOutputEncodingTransport.of_encoded_output_eq result
  intro s
  induction rows s with
  | nil => rfl
  | cons i rest ih =>
    simp only [id_eq] at ih
    simp [List.flatMap_cons,
      UnaryFieldEncoderMachine.unaryFields_cons,ih,List.append_assoc]

def pointFieldsCompiler {point : List Symbol → Index → Cell}
    (px : Compiler rows (fun s i => (point s i).1.toNat))
    (nx : Compiler rows (fun s i => (-(point s i).1).toNat))
    (py : Compiler rows (fun s i => (point s i).2.toNat))
    (ny : Compiler rows (fun s i => (-(point s i).2).toNat)) :
    TM2ComputableInPolyTime id unaryFields
      (fun s => (rows s).flatMap fun i => PeriodicGridDrawing.Arithmetic.pointFields (point s i)) := by
  let result := pairFields (signedDifference px nx) (signedDifference py ny)
  apply TM2ComputableInPolyTime.of_eq result
  intro s
  apply congrArg (fun f : Index → List Nat => (rows s).flatMap f)
  funext i
  have hx : ((point s i).1.toNat:Int)-(-(point s i).1).toNat=(point s i).1 := by omega
  have hy : ((point s i).2.toNat:Int)-(-(point s i).2).toNat=(point s i).2 := by omega
  change [Encodable.encode _,Encodable.encode _]=_
  rw [hx,hy]
  rfl

end LeanTrominoes.UnaryColumn
end
