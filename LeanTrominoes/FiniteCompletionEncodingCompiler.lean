/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.FinitePrefillRadiusCompiler
import LeanTrominoes.CompletionStripSourcePaletteCompiler
import LeanTrominoes.TM2NativeListAppendClosure

/-! # Original completion encoding from three compiled placement columns -/
noncomputable section
namespace LeanTrominoes.Tromino.FiniteCoordinateColumns
open _root_.Computability Turing UnaryColumn
open UnaryFieldEncoderMachine (unaryFields)
set_option maxHeartbeats 3000000
variable {Symbol : Type} [Fintype Symbol] [Inhabited Symbol]
variable (prefill : List Symbol → List (Placement Unit))
    (cs : Compiler prefill (fun _ p => CompletionStripEncoding.symmetryCode p.symmetry))
    (cx : Compiler prefill (fun _ p => Encodable.encode p.offset.1))
    (cy : Compiler prefill (fun _ p => Encodable.encode p.offset.2))

private def tagColumn (column : Field) {numbers : List Symbol → List Nat}
    (compiler : TM2ComputableInPolyTime id unaryFields numbers) :
    TM2ComputableInPolyTime id id
      (fun s => (unaryFields (numbers s)).map (Token.field column)) := by
  let tagged := TM2PolyTimeInputEncodingTransport.of_prepare unaryFields
    (FiniteBlockTransducer.computableInPolyTime (fun symbol => [Token.field column symbol]))
    (fun _ => rfl) (fun _ => rfl)
  let computed := TM2CompositionMachine.computableInPolyTime compiler tagged
  exact computed.of_eq (fun _ => List.map_eq_flatMap.symm)

/-- The machine emits the exact canonical witness box charged by the original
finite completion encoding, together with the prescribed tiles. -/
def completionEncodingComputableInPolyTime (t : Tromino) :
    TM2ComputableInPolyTime id (completionEncoding t).encode prefill := by
  let r : Compiler (fun _ : List Symbol => [()]) (fun s _ =>
      FiniteWitness.radius (completionFootprints t (prefill s)).toFinset) :=
    prefillRadiusCompiler prefill cs cx cy t
  let n : ScalarCompiler (fun s => 2*FiniteWitness.radius (completionFootprints t (prefill s)).toFinset+1) :=
    (add (scale r 2) (constant r 1)).of_eq (fun s => by simp [Nat.mul_comm])
  let xs := CompletionPattern.Runtime.gridXCompiler n n
  let ys := CompletionPattern.Runtime.gridYCompiler n n
  let bx := signedDifference xs (broadcast xs r)
  let by' := signedDifference ys (broadcast ys r)
  let first := TM2ListAppend.nativeComputableInPolyTime (tagColumn .regionX bx) (tagColumn .regionY by')
  let last := TM2ListAppend.nativeComputableInPolyTime (tagColumn .prefillSymmetry cs)
    (TM2ListAppend.nativeComputableInPolyTime (tagColumn .prefillX cx) (tagColumn .prefillY cy))
  let result := TM2ListAppend.nativeComputableInPolyTime first last
  apply TM2PolyTimeOutputEncodingTransport.of_identity_output_eq result
  intro s
  simp [completionEncoding,completionView,encodeInput,fields,values,FiniteWitness.boxList,
    CompletionPattern.Runtime.gridSites,List.map_flatMap,List.map_map,List.flatMap_map,List.flatMap_assoc,Function.comp_def,List.append_assoc] <;> simp only [← List.map_eq_flatMap] <;> simp
end LeanTrominoes.Tromino.FiniteCoordinateColumns
