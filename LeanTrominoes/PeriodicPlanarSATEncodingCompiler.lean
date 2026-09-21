/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.PeriodicPlanarSATFlatEncoding
import LeanTrominoes.UnaryFieldAggregateCompiler
import LeanTrominoes.UnaryFieldClosure

/-! # Polynomial-time assembly of the native formula-and-drawing encoding

The two field compilers must emit the actual complete component fields.
The assembler computes the drawing delimiter and converts all fields to the
same native binary encoding used by the PSPACE membership theorems.
-/
noncomputable section
namespace LeanTrominoes.PeriodicPlanarSAT.FlatEncoding
open Computability Turing
open UnaryFieldEncoderMachine (unaryFields)
variable {Symbol : Type} [Fintype Symbol] [Inhabited Symbol]

noncomputable def fieldsCompiler {input : List Symbol → Input Nat}
    (formula : TM2ComputableInPolyTime id unaryFields (fun s => PeriodicCNFFlatEncoding.formulaFields (input s).1))
    (drawing : TM2ComputableInPolyTime id unaryFields (fun s => drawingFields (input s).2)) :
    TM2ComputableInPolyTime id unaryFields (fun s => fields (input s)) := by
  let count := TM2CompositionMachine.computableInPolyTime drawing UnaryFieldAggregate.countCompiler
  exact UnaryFieldClosure.appendCompiler id _ _ count
    (UnaryFieldClosure.appendCompiler id _ _ drawing formula)

noncomputable def encodingCompiler {input : List Symbol → Input Nat}
    (formula : TM2ComputableInPolyTime id unaryFields (fun s => PeriodicCNFFlatEncoding.formulaFields (input s).1))
    (drawing : TM2ComputableInPolyTime id unaryFields (fun s => drawingFields (input s).2)) :
    TM2ComputableInPolyTime id finEncoding.encode input := by
  let compiler := TM2CompositionMachine.computableInPolyTime (fieldsCompiler formula drawing)
    UnaryFieldEncoderMachine.computableInPolyTime
  apply TM2PolyTimeOutputEncodingTransport.of_encoded_output_eq compiler
  intro s
  exact (PeriodicCNFFlatEncoding.encodeNatFields_eq_trList (fields (input s))).symm

end LeanTrominoes.PeriodicPlanarSAT.FlatEncoding
end
