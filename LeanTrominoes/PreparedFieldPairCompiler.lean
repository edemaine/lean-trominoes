/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.BinaryFieldCountPreparation

/-! # Polynomial-time length-delimited pairing of binary field preparations -/
noncomputable section
namespace LeanTrominoes
open Turing Turing.PartrecToTM2 PeriodicCNFFlatEncoding

def preparedFieldPairCompiler {Input Symbol : Type} [Fintype Symbol] [Inhabited Symbol]
    {encoding : Input → List Symbol} {first second : Input → List Nat}
    (cf : TM2ComputableInPolyTime encoding trList first)
    (cs : TM2ComputableInPolyTime encoding trList second) :
    TM2ComputableInPolyTime encoding trList
      (fun x => (first x).length :: (first x ++ second x)) := by
  have header : TM2ComputableInPolyTime trList trList
      (fun values : List Nat => values.length::values) := by
    exact TM2PolyTimeInputEncodingTransport.of_prepare id
      (BinaryFieldCountPreparation.compiler (fun values : List Nat => values))
      (fun values => encodeNatFields_eq_trList values) (fun _ => rfl)
  let prefixed := TM2CompositionMachine.computableInPolyTime cf header
  have left : TM2ComputableInPolyTime encoding id (fun x => trList ((first x).length::first x)) :=
    TM2PolyTimeOutputEncodingTransport.of_encoded_output_eq prefixed (fun _ => rfl)
  have right : TM2ComputableInPolyTime encoding id (fun x => trList (second x)) :=
    TM2PolyTimeOutputEncodingTransport.of_encoded_output_eq cs (fun _ => rfl)
  let pair := TM2ListAppend.computableInPolyTime left right
  exact TM2PolyTimeOutputEncodingTransport.of_encoded_output_eq pair
    (fun x => by simp [trList])

end LeanTrominoes
end
