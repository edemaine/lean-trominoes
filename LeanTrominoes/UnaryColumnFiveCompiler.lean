/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.UnaryColumnSerialization

/-! # Serializing five aligned unary columns -/
noncomputable section
namespace LeanTrominoes.UnaryColumn
open Computability Turing
open UnaryFieldEncoderMachine (unaryFields)
variable {Source Index : Type} [Fintype Source] [Inhabited Source]
  {rows : List Source → List Index} {a b c d e : List Source → Index → Nat}

def five (ca : Compiler rows a) (cb : Compiler rows b) (cc : Compiler rows c)
    (cd : Compiler rows d) (ce : Compiler rows e) :
    TM2ComputableInPolyTime id unaryFields
      (fun s => (rows s).flatMap fun i => [a s i,b s i,c s i,d s i,e s i]) := by
  let result := finishBlocks (appendBlocks (blocks ca) (appendBlocks (blocks cb)
    (appendBlocks (blocks cc) (appendBlocks (blocks cd) (blocks ce)))))
  apply TM2PolyTimeOutputEncodingTransport.of_encoded_output_eq result
  intro s
  induction rows s with
  | nil => rfl
  | cons i rest ih =>
    simp only [id_eq] at ih
    simp [List.flatMap_cons,UnaryFieldEncoderMachine.unaryFields_cons,ih,List.append_assoc]

end LeanTrominoes.UnaryColumn
end
