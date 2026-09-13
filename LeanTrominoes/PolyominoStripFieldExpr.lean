/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.PolyominoStripCoordinateExpr
import LeanTrominoes.PolyominoStripArithmeticInput

/-! # Tile-list field access inside compiled placement predicates -/

namespace LeanTrominoes.PolyominoStripWindow.Formula
open BoundedArithmetic BoundedArithmetic.Expr

/-- The initial header starts after `depth` locally bound fields. -/
def cellCount (depth kindField : Nat) : Expr :=
  .ite (var kindField) (var (depth+5)) (var (depth+4))

def cellCode (depth kindField cellField axis : Nat) : Expr :=
  .load ((.literal (depth+6)) + (.ite (var kindField) (2*var (depth+4)) 0) +
    2*var cellField + (.literal axis))

theorem cellCount_eval (cells : Bool → List Cell) (height bound first second : Nat)
    (front : List Nat) (kind : Bool) (kindField : Nat)
    (hk : ((front ++ Arithmetic.input cells height bound first second)[kindField]?.getD 0) = kind.toNat) :
    (cellCount front.length kindField).eval (front ++ Arithmetic.input cells height bound first second) =
      (cells kind).length := by
  have hp := Arithmetic.header_get cells height bound first second front 4 (by decide)
  have hq := Arithmetic.header_get cells height bound first second front 5 (by decide)
  change (if ((front ++ Arithmetic.input cells height bound first second)[kindField]?.getD 0) = 0
    then ((front ++ Arithmetic.input cells height bound first second)[front.length+4]?.getD 0)
    else ((front ++ Arithmetic.input cells height bound first second)[front.length+5]?.getD 0)) = _
  rw [hk,hp,hq]
  cases kind <;> rfl

theorem cellCode_eval (cells : Bool → List Cell) (height bound first second : Nat)
    (front : List Nat) (kind : Bool) (kindField cellField index : Nat) (axis : Fin 2)
    (hk : ((front ++ Arithmetic.input cells height bound first second)[kindField]?.getD 0) = kind.toNat)
    (hj : ((front ++ Arithmetic.input cells height bound first second)[cellField]?.getD 0) = index)
    (hi : index < (cells kind).length) :
    (cellCode front.length kindField cellField axis.val).eval
        (front ++ Arithmetic.input cells height bound first second) =
      (PeriodicStripFlatEncoding.cellFields (cells kind)[index])[axis.val]?.getD 0 := by
  have hp := Arithmetic.header_get cells height bound first second front 4 (by decide)
  change ((front ++ Arithmetic.input cells height bound first second)[front.length+6+
    (if ((front ++ Arithmetic.input cells height bound first second)[kindField]?.getD 0) = 0 then 0
     else 2*((front ++ Arithmetic.input cells height bound first second)[front.length+4]?.getD 0))+
    2*((front ++ Arithmetic.input cells height bound first second)[cellField]?.getD 0)+axis.val]?.getD 0) = _
  rw [hk,hj,hp]
  have field := Arithmetic.cell_field cells height bound first second front kind index axis hi
  cases kind <;> simpa [Arithmetic.cellBase,Nat.add_assoc] using field

theorem cellCount_noPower (depth kindField : Nat) : (cellCount depth kindField).noPower = true := by
  simp [cellCount,Expr.noPower]

theorem cellCode_noPower (depth kindField cellField axis : Nat) :
    (cellCode depth kindField cellField axis).noPower = true := by
  simp [cellCode,Expr.noPower]

end LeanTrominoes.PolyominoStripWindow.Formula
