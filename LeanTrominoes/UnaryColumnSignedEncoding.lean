/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.UnaryColumnSerialization
import LeanTrominoes.CompletionStripEncoding

/-! # Signed coordinate fields and row counts for completion encoding -/
noncomputable section
namespace LeanTrominoes.UnaryColumn
open Computability Turing
variable {Symbol Index : Type} [Fintype Symbol] [Inhabited Symbol]
  {rows : List Symbol → List Index} {f g : List Symbol → Index → Nat}

theorem encode_difference (positive negative : Nat) :
    Encodable.encode ((positive:Int)-negative) =
      (positive-negative)*2+((negative-positive)*2-1) := by
  generalize eq : (positive:Int)-negative = z
  cases z with
  | ofNat n =>
    have hz : (positive:Int)-negative = (n:Int) := eq
    change 2*n = _
    omega
  | negSucc n =>
    have hz : (positive:Int)-negative = -((n:Int)+1) := eq
    change 2*n+1 = _
    omega

def signedDifference (positive : Compiler rows f) (negative : Compiler rows g) :
    Compiler rows (fun s i => Encodable.encode ((f s i:Int)-g s i)) := by
  let result := add (scale (sub positive negative) 2)
    (sub (scale (sub negative positive) 2) (constant positive 1))
  exact TM2ComputableInPolyTime.of_eq result
    (fun s => List.map_congr_left (fun i _ => (encode_difference _ _).symm))

def countRows (c : Compiler rows f) : ScalarCompiler (fun s => (rows s).length) := by
  let result := TM2CompositionMachine.computableInPolyTime c UnaryFieldAggregate.countCompiler
  exact TM2ComputableInPolyTime.of_eq result (fun s => by simp)

def table {α : Type} (items : List α) (value : α → Nat) :
    Compiler (fun _ : List Symbol => items) (fun _ a => value a) :=
  TM2ConstantValueCompiler.computableInPolyTime id UnaryFieldEncoderMachine.unaryFields (items.map value)
end LeanTrominoes.UnaryColumn
