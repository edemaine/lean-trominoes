/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.Theorem55StripUnaryCoordinates
import LeanTrominoes.UnaryPointTableOperations
import LeanTrominoes.UnaryFieldSubtractConstant

/-! # Polynomial-time grid, hole, and lock tables for strip complements -/

noncomputable section
namespace LeanTrominoes.Theorem55StripUnary
open Computability Turing
open UnaryFieldEncoderMachine (unaryFields)

def side (source : PeriodicStrip) : Nat := 3*Theorem55StripSource.period source
/-- Larger than every biased horizontal coordinate of the hole table. -/
def radix (source : PeriodicStrip) : Nat := 3*((source.width+73)*source.period)+3

def radixCompiler : Compiler (fun source => [radix source]) := by
  let width := offsetCompiler _ widthCompiler 73
  let product := UnaryFieldScalarMultiply.computableInPolyTime encode PeriodicStrip.period _ periodCompiler width
  let scaled := scaleCompiler _ product 3
  let shifted := offsetCompiler _ scaled 3
  exact TM2PolyTimeOutputEncodingTransport.of_encoded_output_eq shifted
    (fun s => congrArg unaryFields (by simp [radix,Nat.mul_comm]))

def gridRangeCompiler : Compiler (fun source => List.range (side source)) := by
  let compiler := TM2CompositionMachine.computableInPolyTime sideCompiler UnaryFieldAggregate.rangeSumCompiler
  exact TM2PolyTimeOutputEncodingTransport.of_encoded_output_eq compiler
    (fun s => congrArg unaryFields (by simp [side]))

def gridTable : UnaryPointTable encode :=
  UnaryPointTable.sum (UnaryPointTable.line _ gridRangeCompiler true)
    (UnaryPointTable.line _ gridRangeCompiler false)

def motifTable : UnaryPointTable encode where
  rows := naturalMotif
  xCompiler := TM2PolyTimeOutputEncodingTransport.of_encoded_output_eq (axisCoordinateCompiler 0)
    (fun s => congrArg unaryFields (naturalMotif_x s).symm)
  yCompiler := TM2PolyTimeOutputEncodingTransport.of_encoded_output_eq (axisCoordinateCompiler 1)
    (fun s => congrArg unaryFields (naturalMotif_y s).symm)

def offsets (source : PeriodicStrip) : List Nat :=
  (List.range (source.width+73)).map (·*source.period)

def offsetsCompiler : Compiler offsets := by
  let width := offsetCompiler _ widthCompiler 73
  let ranged := TM2CompositionMachine.computableInPolyTime width UnaryFieldAggregate.rangeSumCompiler
  let product := UnaryFieldScalarMultiply.computableInPolyTime encode PeriodicStrip.period _ periodCompiler ranged
  exact TM2PolyTimeOutputEncodingTransport.of_encoded_output_eq product
    (fun s => congrArg unaryFields (by simp [offsets]))

def repetitionTable : UnaryPointTable encode := UnaryPointTable.line _ offsetsCompiler true

def parentTable : UnaryPointTable encode :=
  repetitionTable.sum (motifTable.affine 1 0 10)

/-- Cross subcells shifted by `(1,1)` to keep every coordinate natural. -/
def crossOffsets : List (Nat×Nat) := [(1,1),(2,1),(0,1),(1,2),(1,0)]
def paddingParents : List (Nat×Nat) := [(14,4),(14,5),(14,6),(15,4),(15,5),(15,6)]

def holeTable : UnaryPointTable encode :=
  ((parentTable.affine 3 0 0).sum (UnaryPointTable.constant encode crossOffsets)).append
    (((UnaryPointTable.constant encode paddingParents).affine 3 0 0).sum
      (UnaryPointTable.constant encode crossOffsets))

def rightLockOffsets : List (Nat×Nat) := [(1,3),(1,4),(2,4),(3,4),(4,4)]

def rightLockBaseCompiler : Compiler (fun source => [side source-4]) := by
  let compiler := TM2CompositionMachine.computableInPolyTime sideCompiler
    (UnaryFieldSubtractConstant.computableInPolyTime 4)
  exact TM2PolyTimeOutputEncodingTransport.of_encoded_output_eq compiler
    (fun s => congrArg unaryFields (by simp [side]))

def rightLockTable : UnaryPointTable encode :=
  (UnaryPointTable.line _ rightLockBaseCompiler true).sum
    (UnaryPointTable.constant encode rightLockOffsets)

def excludedTable : UnaryPointTable encode := holeTable.append rightLockTable

def key (source : PeriodicStrip) (point : Nat×Nat) : Nat := point.1+point.2*radix source

def excludedKeys (source : PeriodicStrip) : List Nat := (excludedTable.rows source).map (key source)

def excludedKeyCompiler : Compiler excludedKeys := excludedTable.keyCompiler radix radixCompiler

def gridPoints (source : PeriodicStrip) : List (Nat×Nat) :=
  (List.range (side source)).flatMap fun x => (List.range (side source)).map fun y => (x,y)

theorem gridTable_rows (source : PeriodicStrip) : gridTable.rows source = gridPoints source := by
  simp [gridTable,UnaryPointTable.sum,UnaryPointTable.sumRows,UnaryPointTable.line,
    gridPoints,List.flatMap_map,List.map_map,Function.comp_def]

end LeanTrominoes.Theorem55StripUnary
