/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.UnaryFieldScalarMultiply
import LeanTrominoes.UnaryFieldConstantScaleCompiler
import LeanTrominoes.UnaryAlignedAddNativeListCompiler
import LeanTrominoes.AlignedUnaryListClosure

/-! # Polynomial-time tables of pairs of unary natural coordinates -/

noncomputable section
namespace LeanTrominoes
open Computability Turing
open UnaryFieldEncoderMachine (unaryFields)

structure UnaryPointTable {Source Symbol : Type} (encode : Source → List Symbol) where
  rows : Source → List (Nat×Nat)
  xCompiler : TM2ComputableInPolyTime encode unaryFields (fun s => (rows s).map Prod.fst)
  yCompiler : TM2ComputableInPolyTime encode unaryFields (fun s => (rows s).map Prod.snd)

namespace UnaryPointTable
variable {Source Symbol : Type} [Fintype Symbol] [Inhabited Symbol]
variable {encode : Source → List Symbol}

def constant (encode : Source → List Symbol) (points : List (Nat×Nat)) : UnaryPointTable encode where
  rows _ := points
  xCompiler := TM2ConstantValueCompiler.computableInPolyTime encode unaryFields (points.map Prod.fst)
  yCompiler := TM2ConstantValueCompiler.computableInPolyTime encode unaryFields (points.map Prod.snd)

def append (a b : UnaryPointTable encode) : UnaryPointTable encode where
  rows s := a.rows s ++ b.rows s
  xCompiler := TM2PolyTimeOutputEncodingTransport.of_encoded_output_eq
    (UnaryFieldClosure.appendCompiler encode _ _ a.xCompiler b.xCompiler)
    (fun s => congrArg unaryFields (List.map_append.symm))
  yCompiler := TM2PolyTimeOutputEncodingTransport.of_encoded_output_eq
    (UnaryFieldClosure.appendCompiler encode _ _ a.yCompiler b.yCompiler)
    (fun s => congrArg unaryFields (List.map_append.symm))

def affine (a : UnaryPointTable encode) (factor dx dy : Nat) : UnaryPointTable encode where
  rows s := (a.rows s).map (fun p => (p.1*factor+dx,p.2*factor+dy))
  xCompiler := by
    let scaled := TM2CompositionMachine.computableInPolyTime a.xCompiler
      (UnaryFieldConstantScale.computableInPolyTime factor)
    let shifted := TM2CompositionMachine.computableInPolyTime scaled
      (UnaryFieldConstantOffsets.computableInPolyTime dx)
    exact TM2PolyTimeOutputEncodingTransport.of_encoded_output_eq shifted
      (fun s => congrArg unaryFields (by simp [UnaryFieldConstantScale.values,UnaryFieldConstantOffsets.values,List.map_map,Function.comp_def]))
  yCompiler := by
    let scaled := TM2CompositionMachine.computableInPolyTime a.yCompiler
      (UnaryFieldConstantScale.computableInPolyTime factor)
    let shifted := TM2CompositionMachine.computableInPolyTime scaled
      (UnaryFieldConstantOffsets.computableInPolyTime dy)
    exact TM2PolyTimeOutputEncodingTransport.of_encoded_output_eq shifted
      (fun s => congrArg unaryFields (by simp [UnaryFieldConstantScale.values,UnaryFieldConstantOffsets.values,List.map_map,Function.comp_def]))

def sumRows (a b : List (Nat×Nat)) : List (Nat×Nat) :=
  a.flatMap fun p => b.map fun q => (p.1+q.1,p.2+q.2)

private def sumColumnCompiler (a b : UnaryPointTable encode) (axis : Bool) :
    TM2ComputableInPolyTime encode unaryFields
      (fun s => (sumRows (a.rows s) (b.rows s)).map (fun p => if axis then p.1 else p.2)) := by
  let f : Nat×Nat → Nat := fun p => if axis then p.1 else p.2
  have ca : TM2ComputableInPolyTime encode unaryFields (fun s => (a.rows s).map f) := by
    cases axis
    · exact a.yCompiler
    · exact a.xCompiler
  have cb : TM2ComputableInPolyTime encode unaryFields (fun s => (b.rows s).map f) := by
    cases axis
    · exact b.yCompiler
    · exact b.xCompiler
  let first := UnaryFieldCartesian.computableInPolyTime encode _ _ ca cb .first
  let second := UnaryFieldCartesian.computableInPolyTime encode _ _ ca cb .second
  let added := AlignedUnaryListClosure.addedComputableInPolyTime encode _ _
    (fun s => by simp) first second
  apply TM2PolyTimeOutputEncodingTransport.of_encoded_output_eq added
  intro s
  congr 1
  have firstEq :
      ((a.rows s).map f).flatMap (fun x => ((b.rows s).map f).map (fun y => UnaryFieldSquareProjection.choose .first x y)) =
        ((a.rows s).flatMap fun x => (b.rows s).map fun y => (x,y)).map (fun p => f p.1) := by
    simp [UnaryFieldSquareProjection.choose,List.map_flatMap,List.flatMap_map,List.map_map,Function.comp_def]
  have secondEq :
      ((a.rows s).map f).flatMap (fun x => ((b.rows s).map f).map (fun y => UnaryFieldSquareProjection.choose .second x y)) =
        ((a.rows s).flatMap fun x => (b.rows s).map fun y => (x,y)).map (fun p => f p.2) := by
    simp [UnaryFieldSquareProjection.choose,List.map_flatMap,List.flatMap_map,List.map_map,Function.comp_def]
  change UnaryAlignedAddMachine.sums _ _ = _
  rw [firstEq,secondEq,UnaryAlignedAddMachine.sums_map]
  cases axis <;> simp [sumRows,f,List.map_flatMap,List.map_map,Function.comp_def]

def sum (a b : UnaryPointTable encode) : UnaryPointTable encode where
  rows s := sumRows (a.rows s) (b.rows s)
  xCompiler := sumColumnCompiler a b true
  yCompiler := sumColumnCompiler a b false

def keyCompiler (a : UnaryPointTable encode) (radix : Source → Nat)
    (radixCompiler : TM2ComputableInPolyTime encode unaryFields (fun s => [radix s])) :
    TM2ComputableInPolyTime encode unaryFields
      (fun s => (a.rows s).map (fun p => p.1+p.2*radix s)) := by
  let scaled := UnaryFieldScalarMultiply.computableInPolyTime encode radix _ radixCompiler a.yCompiler
  let added := AlignedUnaryListClosure.addedComputableInPolyTime encode _ _ (fun s => by simp) a.xCompiler scaled
  apply TM2PolyTimeOutputEncodingTransport.of_encoded_output_eq added
  intro s
  congr 1
  change UnaryAlignedAddMachine.sums _ _ = _
  rw [List.map_map,UnaryAlignedAddMachine.sums_map]
  rfl

end UnaryPointTable
end LeanTrominoes
