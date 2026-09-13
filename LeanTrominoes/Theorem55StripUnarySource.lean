/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.PeriodicStripFlatEncoding
import LeanTrominoes.Theorem55StripCompiler
import LeanTrominoes.UnaryFieldScalarMultiply
import LeanTrominoes.UnaryFieldHalveCompiler
import LeanTrominoes.UnaryFieldConstantScaleCompiler

/-! # Unary source fields and dimensions for the strip hardness compiler -/

noncomputable section
namespace LeanTrominoes.Theorem55StripUnary
open Computability Turing
open UnaryFieldEncoderMachine (unaryFields)
open PeriodicStripFlatEncoding (stripFields cellFields)

def encode (source : PeriodicStrip) := unaryFields (stripFields source)
abbrev Compiler (f : PeriodicStrip → List Nat) := TM2ComputableInPolyTime encode unaryFields f

def inputCompiler : Compiler stripFields :=
  TM2PolyTimeOutputEncodingTransport.of_encoded_output_eq (idComputableInPolyTime encode) (fun _ => rfl)

def constantCompiler (values : List Nat) : Compiler (fun _ => values) :=
  TM2ConstantValueCompiler.computableInPolyTime encode unaryFields values

def gatherCompiler (queries : PeriodicStrip → List Nat) (queryCompiler : Compiler queries)
    (valid : ∀ source q, q ∈ queries source → q < (stripFields source).length) :
    Compiler (fun source => (queries source).map (fun q => (stripFields source).getD q 0)) :=
  TM2PolyTimeOutputEncodingTransport.of_encoded_output_eq
    (UnaryIndexedValueLookup.valuesComputableInPolyTime encode queries stripFields queryCompiler inputCompiler)
    (fun source => congrArg unaryFields
      (UnaryIndexedValueLookup.values_eq_map_getD_of_forall_lt _ _ (valid source)))

def headerCompiler (i : Nat) (hi : i < 3) : Compiler (fun source => [(stripFields source).getD i 0]) := by
  let compiler := gatherCompiler (fun _ => [i]) (constantCompiler [i]) (by
    intro source q hq
    simp only [List.mem_singleton] at hq
    subst q
    rw [PeriodicStripFlatEncoding.stripFields_length]
    omega)
  exact compiler

def widthCompiler : Compiler (fun source => [source.width]) := by
  simpa [stripFields] using headerCompiler 0 (by omega)
def periodCompiler : Compiler (fun source => [source.period]) := by
  simpa [stripFields] using headerCompiler 1 (by omega)
def countCompiler : Compiler (fun source => [source.motif.length]) := by
  simpa [stripFields] using headerCompiler 2 (by omega)

def indexCompiler : Compiler (fun source => List.range source.motif.length) := by
  let compiler := TM2CompositionMachine.computableInPolyTime countCompiler UnaryFieldAggregate.rangeSumCompiler
  exact TM2PolyTimeOutputEncodingTransport.of_encoded_output_eq compiler (fun source => congrArg unaryFields (by simp))

def offsetCompiler (f : PeriodicStrip → List Nat) (compiler : Compiler f) (offset : Nat) :
    Compiler (fun source => (f source).map (·+offset)) :=
  TM2CompositionMachine.computableInPolyTime compiler (UnaryFieldConstantOffsets.computableInPolyTime offset)

def scaleCompiler (f : PeriodicStrip → List Nat) (compiler : Compiler f) (factor : Nat) :
    Compiler (fun source => (f source).map (·*factor)) :=
  TM2CompositionMachine.computableInPolyTime compiler (UnaryFieldConstantScale.computableInPolyTime factor)

def enlargedPeriodCompiler : Compiler (fun source => [Theorem55StripSource.period source]) := by
  let enlargedWidth := offsetCompiler _ widthCompiler 72
  let product := UnaryFieldScalarMultiply.computableInPolyTime encode PeriodicStrip.period _ periodCompiler enlargedWidth
  exact TM2PolyTimeOutputEncodingTransport.of_encoded_output_eq product (fun source => congrArg unaryFields (by
    simp [Theorem55StripSource.period]))

def sideCompiler : Compiler (fun source => [3*Theorem55StripSource.period source]) := by
  let compiler := scaleCompiler _ enlargedPeriodCompiler 3
  exact TM2PolyTimeOutputEncodingTransport.of_encoded_output_eq compiler
    (fun source => congrArg unaryFields (by simp [Nat.mul_comm]))

def axisQueries (axis : Fin 2) (source : PeriodicStrip) : List Nat :=
  (List.range source.motif.length).map (fun i => i*2+(3+axis.val))

def axisQueryCompiler (axis : Fin 2) : Compiler (axisQueries axis) := by
  let scaled := scaleCompiler _ indexCompiler 2
  let offset := offsetCompiler _ scaled (3+axis.val)
  exact TM2PolyTimeOutputEncodingTransport.of_encoded_output_eq offset (fun source => congrArg unaryFields (by
    simp [axisQueries,List.map_map,Function.comp_def]))

def axisCodes (axis : Fin 2) (source : PeriodicStrip) : List Nat :=
  (axisQueries axis source).map (fun i => (stripFields source).getD i 0)

def axisCodeCompiler (axis : Fin 2) : Compiler (axisCodes axis) :=
  gatherCompiler (axisQueries axis) (axisQueryCompiler axis) (by
    intro source q hq
    obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hq
    have hi' := List.mem_range.mp hi
    have ha := axis.isLt
    rw [PeriodicStripFlatEncoding.stripFields_length]
    omega)

def axisCoordinates (axis : Fin 2) (source : PeriodicStrip) : List Nat :=
  (axisCodes axis source).map (·/2)

def axisCoordinateCompiler (axis : Fin 2) : Compiler (axisCoordinates axis) := by
  let compiler := TM2CompositionMachine.computableInPolyTime (axisCodeCompiler axis) UnaryFieldHalve.computableInPolyTime
  exact compiler

end LeanTrominoes.Theorem55StripUnary
