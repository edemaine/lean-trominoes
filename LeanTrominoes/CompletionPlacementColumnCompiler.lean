/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.UnaryColumnSignedEncoding

/-! # Polynomial-time placement fields from affine coordinate columns -/
noncomputable section
namespace LeanTrominoes.CompletionPattern.Runtime
open Computability Turing UnaryColumn
variable {Symbol Index : Type} [Fintype Symbol] [Inhabited Symbol]
  {rows : List Symbol → List Index} {x y : List Symbol → Index → Nat}
  {placement : List Symbol → Index → Placement Unit}

def placementFieldsCompiler (cx : Compiler rows x) (cy : Compiler rows y)
    (sym : Compiler rows (fun s i => CompletionStripEncoding.symmetryCode (placement s i).symmetry))
    (px : Compiler rows (fun s i => (placement s i).offset.1.toNat))
    (nx : Compiler rows (fun s i => (-(placement s i).offset.1).toNat))
    (py : Compiler rows (fun s i => (placement s i).offset.2.toNat))
    (ny : Compiler rows (fun s i => (-(placement s i).offset.2).toNat)) :
    TM2ComputableInPolyTime id UnaryFieldEncoderMachine.unaryFields
      (fun s => (rows s).flatMap fun i => CompletionStripEncoding.placementFields
        ((placement s i).shift ((x s i:Int),(y s i:Int)))) := by
  let xs := signedDifference (add cx px) nx
  let ys := signedDifference (add cy py) ny
  let result := triple sym xs ys
  apply TM2ComputableInPolyTime.of_eq result
  intro s
  apply congrArg (fun f : Index → List Nat => (rows s).flatMap f)
  funext i
  change [_,Encodable.encode (((x s i+(placement s i).offset.1.toNat:Nat):Int)-(-(placement s i).offset.1).toNat),
    Encodable.encode (((y s i+(placement s i).offset.2.toNat:Nat):Int)-(-(placement s i).offset.2).toNat)] = _
  have hx : (((x s i+(placement s i).offset.1.toNat:Nat):Int)-(-(placement s i).offset.1).toNat) =
      (x s i:Int)+(placement s i).offset.1 := by omega
  have hy : (((y s i+(placement s i).offset.2.toNat:Nat):Int)-(-(placement s i).offset.2).toNat) =
      (y s i:Int)+(placement s i).offset.2 := by omega
  rw [hx,hy]
  rfl
end LeanTrominoes.CompletionPattern.Runtime
