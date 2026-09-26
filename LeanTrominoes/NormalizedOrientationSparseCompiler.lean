/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.NormalizedOrientationFlatEncoding
import LeanTrominoes.CompletionStripSourceColumns
import LeanTrominoes.CompletionStripSourceSparseModel
import LeanTrominoes.UnaryColumnLookupSupport
import LeanTrominoes.UnaryFieldClosure
import LeanTrominoes.ListRangeGetD

/-! # Native compilation of the complete normalized orientation cell table -/
noncomputable section
namespace LeanTrominoes.Gadget.NormalizedOrientation
open PeriodicOrthogonalDrawing FlatEncoding Turing UnaryColumn
open CompletionPattern.Runtime
set_option maxHeartbeats 600000
set_option maxRecDepth 3000
set_option synthInstance.maxSize 2048

private theorem getAt_nat (d : PeriodicOrthogonalDrawing) (x y : Nat)
    (hx : x < d.horizontalPeriod) (hy : y < d.verticalPeriod) :
    d.getAt ((x:Int),(y:Int)) = d.cellTypes.getD (y*d.horizontalPeriod+x) .blank := by
  have ex : (x:Int) % (d.horizontalPeriod:Int) = x := Int.emod_eq_of_lt (by omega) (by exact_mod_cast hx)
  have ey : (y:Int) % (d.verticalPeriod:Int) = y := Int.emod_eq_of_lt (by omega) (by exact_mod_cast hy)
  change d.cellTypes.getD (((y:Int) % (d.verticalPeriod:Int)).toNat*d.horizontalPeriod+
    ((x:Int) % (d.horizontalPeriod:Int)).toNat) .blank = _
  rw [ex,ey]
  simp

private theorem table_at (d : PeriodicOrthogonalDrawing) (n : Nat)
    (hn : n < d.horizontalPeriod*d.verticalPeriod) :
    d.getAt (((n%d.horizontalPeriod:Nat):Int),((n/d.horizontalPeriod:Nat):Int)) =
      d.cellTypes.getD n .blank := by
  have positive : 0 < d.horizontalPeriod := by simp [horizontalPeriod]
  rw [getAt_nat d _ _ (Nat.mod_lt _ positive) (by
    apply (Nat.div_lt_iff_lt_mul positive).2
    simpa [Nat.mul_comm] using hn)]
  congr 1
  simpa [Nat.mul_comm] using Nat.div_add_mod n d.horizontalPeriod

private theorem model_entry {d : PeriodicOrthogonalDrawing} {entries : List DrawingEntry}
    (model : SparseModel d entries) (e : DrawingEntry) (he : e ∈ entries) :
    cellCode e.2 = cellCode (d.cellTypes.getD (e.1.2.toNat*d.horizontalPeriod+e.1.1.toNat) .blank) := by
  have bounds := model.bounds e he
  rw [← getAt_nat d _ _ (by omega) (by omega)]
  have ex : (e.1.1.toNat:Int) = e.1.1 := by omega
  have ey : (e.1.2.toNat:Int) = e.1.2 := by omega
  rw [ex,ey,model.consistent e he]

private theorem model_missing {d : PeriodicOrthogonalDrawing} {entries : List DrawingEntry}
    (model : SparseModel d entries) (n : Nat) (hn : n < d.horizontalPeriod*d.verticalPeriod)
    (missing : ¬ ∃ e ∈ entries, e.1.2.toNat*d.horizontalPeriod+e.1.1.toNat = n) :
    cellCode (d.cellTypes.getD n .blank) = 0 := by
  have positive : 0 < d.horizontalPeriod := by simp [horizontalPeriod]
  have hx := Nat.mod_lt n positive
  have hy : n/d.horizontalPeriod < d.verticalPeriod := by
    apply (Nat.div_lt_iff_lt_mul positive).2
    simpa [Nat.mul_comm] using hn
  rw [← table_at d n hn,model.lookup _ ⟨by dsimp only; positivity,
    by dsimp only; exact_mod_cast hx,by dsimp only; positivity,by dsimp only; exact_mod_cast hy⟩]
  have absent : entries.lookup (((n%d.horizontalPeriod:Nat):Int),((n/d.horizontalPeriod:Nat):Int)) = none := by
    rw [List.lookup_eq_none_iff]
    intro e he
    rw [bne_iff_ne]
    intro eq
    apply missing
    refine ⟨e,he,?_⟩
    have ex := congrArg Prod.fst eq
    have ey := congrArg Prod.snd eq
    dsimp only at ex ey
    rw [← ex,← ey]
    simp only [Int.toNat_natCast]
    simpa [Nat.mul_comm] using Nat.div_add_mod n d.horizontalPeriod
  rw [absent]
  rfl

private def assembleFields {Symbol : Type} [Fintype Symbol] [Inhabited Symbol]
    {drawing : List Symbol → PeriodicOrthogonalDrawing}
    (width : ScalarCompiler (fun s => (drawing s).horizontalPeriod))
    (height : ScalarCompiler (fun s => (drawing s).verticalPeriod))
    (cells : TM2ComputableInPolyTime id UnaryFieldEncoderMachine.unaryFields
      (fun s => (drawing s).cellTypes.map cellCode)) :
    TM2ComputableInPolyTime id UnaryFieldEncoderMachine.unaryFields (fun s => FlatEncoding.fields (drawing s)) := by
  let physical := UnaryFieldClosure.appendCompiler id _ _ width
    (UnaryFieldClosure.appendCompiler id _ _ height cells)
  apply TM2ComputableInPolyTime.of_eq physical
  intro s
  rfl

private def assembleEncoding {Symbol : Type} [Fintype Symbol] [Inhabited Symbol]
    {drawing : List Symbol → PeriodicOrthogonalDrawing}
    (compiler : TM2ComputableInPolyTime id UnaryFieldEncoderMachine.unaryFields
      (fun s => FlatEncoding.fields (drawing s))) :
    TM2ComputableInPolyTime id FlatEncoding.finEncoding.encode drawing := by
  let physical := TM2CompositionMachine.computableInPolyTime compiler UnaryFieldEncoderMachine.computableInPolyTime
  apply TM2PolyTimeOutputEncodingTransport.of_encoded_output_eq physical
  intro s
  exact (PeriodicCNFFlatEncoding.encodeNatFields_eq_trList (FlatEncoding.fields (drawing s))).symm

variable {Input : Type} {encoding : _root_.Computability.FinEncoding Input} {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language) [Inhabited encoding.Γ]

def sourceCellCountCompiler : ScalarCompiler (fun s =>
    (sourceDrawing decider s).horizontalPeriod*(sourceDrawing decider s).verticalPeriod) := by
  let width : Compiler (fun _ : List encoding.Γ => [()])
    (fun s _ => (sourceDrawing decider s).horizontalPeriod) := sourceWidthCompiler decider
  exact multiplyScalar width (sourceHeightCompiler decider)

def sourceCellTableCompiler : TM2ComputableInPolyTime id UnaryFieldEncoderMachine.unaryFields
    (fun s => (sourceDrawing decider s).cellTypes.map cellCode) := by
  let indices := naturalRange (sourceCellCountCompiler decider)
  let keys := add (multiplyScalar (sourceYCompiler decider) (sourceWidthCompiler decider)) (sourceXCompiler decider)
  let values : Compiler (sourceRows decider) (fun _ e => cellCode e.2) :=
    TM2CompositionMachine.computableInPolyTime (sourceRecordCompiler decider)
      (GadgetSparseAssignmentColumns.typeCompiler cellCode)
  let physical := keyedSupported indices keys values
    (fun s n => cellCode ((sourceDrawing decider s).cellTypes.getD n .blank))
    (fun s e he => model_entry (source_sparseModel decider s) e he)
    (fun s n hn missing => model_missing (source_sparseModel decider s) n (List.mem_range.mp hn) missing)
  apply TM2ComputableInPolyTime.of_eq physical
  intro s
  have well := PeriodicCNFStripReduction.compiledStripDrawing_isWellFormed
    (PeriodicCNF.PolySpaceCompiler.formulaOfSymbols decider s)
  have len : (sourceDrawing decider s).cellTypes.length =
      (sourceDrawing decider s).horizontalPeriod*(sourceDrawing decider s).verticalPeriod := well.1
  change (List.range ((sourceDrawing decider s).horizontalPeriod*(sourceDrawing decider s).verticalPeriod)).map
    (fun n => cellCode ((sourceDrawing decider s).cellTypes.getD n .blank)) = _
  rw [← len]
  simpa only [List.map_map,Function.comp_def] using congrArg (List.map cellCode)
    (List.map_range_getD (sourceDrawing decider s).cellTypes .blank)

def sourceFieldsCompiler : TM2ComputableInPolyTime id UnaryFieldEncoderMachine.unaryFields
    (fun s => FlatEncoding.fields (sourceDrawing decider s)) :=
  assembleFields (drawing := sourceDrawing decider) (sourceWidthCompiler decider) (sourceHeightCompiler decider) (sourceCellTableCompiler decider)

def sourceEncodingCompiler : TM2ComputableInPolyTime id finEncoding.encode (sourceDrawing decider) :=
  assembleEncoding (drawing := sourceDrawing decider) (sourceFieldsCompiler decider)

end LeanTrominoes.Gadget.NormalizedOrientation
end
