/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.FiniteCoordinateEncoding
import LeanTrominoes.GadgetSparseAssignmentTokenCompiler
import LeanTrominoes.GadgetPixelFiniteTokenCompiler
import LeanTrominoes.UnaryFieldPairProjection

/-! # Actual finite-alphabet polynomial-time gadget-region emission

A compiled sparse drawing stream is expanded by the existing verified gadget
machines. The emitted coordinate fields are split into the original finite
region encoding, rather than a periodic-region or prepared-table encoding.
-/
noncomputable section
namespace LeanTrominoes.Gadget.FiniteRegionCompiler
open _root_.Computability Turing
open Tromino.FiniteCoordinateColumns
open UnaryFieldEncoderMachine (unaryFields)
variable {Source InputSymbol : Type} [Fintype InputSymbol] [Inhabited InputSymbol]
  {encodeSource : Source → List InputSymbol}
  {assignments : Source → List (Cell × OrthogonalCellType)}

def pixelPairs (t : Tromino) (source : Source) : List (Nat × Nat) :=
  (sparseExpandedMotif t (assignments source)).map fun cell =>
    (Encodable.encode cell.1,Encodable.encode cell.2)

private def unaryPixels (t : Tromino)
    (emitter : TM2ComputableInPolyTime encodeSource id
      (fun source => GadgetSparseAssignmentTokens.assignmentsTokens (assignments source)))
    (nonnegative : ∀ source assignment, assignment∈assignments source →
      0≤assignment.1.1 ∧ 0≤assignment.1.2) :
    TM2ComputableInPolyTime encodeSource
      (fun pairs => unaryFields (UnaryFieldPairProjection.fields pairs)) (pixelPairs (assignments := assignments) t) := by
  let prepared := GadgetSparseAssignmentTokenCompiler.computableInPolyTimeOfEmitter t emitter
  let expanded := TM2CompositionMachine.computableInPolyTime prepared
    GadgetPixelFiniteTokens.computableInPolyTime
  let finalized := TM2CompositionMachine.computableInPolyTime expanded
    PeriodicCNF.UnaryProgramTokens.unaryEncodeComputableInPolyTime
  apply TM2PolyTimeOutputEncodingTransport.of_identity_output_eq finalized
  intro source
  rw [GadgetSparseExpandedMotifFiniteTokens.expand_preparedSparseExpandedMotif t
    (assignments source) (nonnegative source),CountedUnaryFieldTokens.unaryEncode_countedFieldBlocks]
  simp [pixelPairs,UnaryFieldPairProjection.fields,List.flatMap_map,← List.flatMap_def]
  rfl

private def tagColumn (column : Field) {numbers : Source → List Nat}
    (compiler : TM2ComputableInPolyTime encodeSource unaryFields numbers) :
    TM2ComputableInPolyTime encodeSource id
      (fun source => (unaryFields (numbers source)).map (Token.field column)) := by
  let tagged := TM2PolyTimeInputEncodingTransport.of_prepare unaryFields
    (FiniteBlockTransducer.computableInPolyTime (fun symbol => [Token.field column symbol]))
    (fun _ => rfl) (fun _ => rfl)
  let computed := TM2CompositionMachine.computableInPolyTime compiler tagged
  exact computed.of_eq (fun _ => List.map_eq_flatMap.symm)

/-- Emit the original unary-coordinate region input with a verified machine.
The source compiler supplies drawing records, not already expanded pixels. -/
def computableInPolyTime (t : Tromino)
    (emitter : TM2ComputableInPolyTime encodeSource id
      (fun source => GadgetSparseAssignmentTokens.assignmentsTokens (assignments source)))
    (nonnegative : ∀ source assignment, assignment∈assignments source →
      0≤assignment.1.1 ∧ 0≤assignment.1.2) :
    TM2ComputableInPolyTime encodeSource regionEncoding.encode
      (fun source => sparseExpandedMotif t (assignments source)) := by
  let unary := unaryPixels t emitter nonnegative
  let xs := TM2CompositionMachine.computableInPolyTime unary
    (UnaryFieldPairProjection.computableInPolyTime false)
  let ys := TM2CompositionMachine.computableInPolyTime unary
    (UnaryFieldPairProjection.computableInPolyTime true)
  let appended := TM2ListAppend.computableInPolyTime (tagColumn .regionX xs) (tagColumn .regionY ys)
  apply TM2PolyTimeOutputEncodingTransport.of_identity_output_eq appended
  intro source
  simp [regionEncoding,encodeInput,fields,values,UnaryFieldPairProjection.values,pixelPairs,List.map_map,Function.comp_def]

end LeanTrominoes.Gadget.FiniteRegionCompiler
