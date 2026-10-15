/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.SAT.CNF.PeriodicCNFSignedDecoder
import LeanTrominoes.Graphs.Orientation.NormalizedOrientationSyntax

/-! # Boolean addresses in the periodic lift of a normalized drawing -/
namespace LeanTrominoes.Gadget.NormalizedOrientation.AsCNF
open PeriodicOrthogonalDrawing

abbrev Variable := (Nat × Nat) × Side

def address (d : Drawing) (location : Cell) : Nat × Nat :=
  ((d.positionAt location).1.val,(d.positionAt location).2.val)

def quotient (d : Drawing) (location : Cell) : Cell :=
  (location.1 / (d.horizontalPeriod : Int),location.2 / (d.verticalPeriod : Int))

def lift (d : Drawing) (location translate : Cell) : Cell :=
  (location.1 + translate.1 * d.horizontalPeriod,
    location.2 + translate.2 * d.verticalPeriod)

def read (d : Drawing) (location : Cell) (side : Side) (value : Bool) : PeriodicLiteral Variable :=
  ⟨(address d location,side),quotient d location,value⟩

def orientation (d : Drawing) (a : Variable → Cell → Bool) : d.Orientation :=
  fun location side => a (address d location,side) (quotient d location)

def assignment (d : Drawing) (o : d.Orientation) : Variable → Cell → Bool :=
  fun v c => o (lift d ((v.1.1 : Int),(v.1.2 : Int)) c) v.2

theorem address_lift (d : Drawing) (location translate : Cell) :
    address d (lift d location translate) = address d location := by
  apply Prod.ext <;>
    simp [address,lift,positionAt,residue,horizontalPeriod,verticalPeriod,
      Int.add_mul_emod_self_right]

theorem quotient_lift (d : Drawing) (location translate : Cell) :
    quotient d (lift d location translate) = Cell.add (quotient d location) translate := by
  apply Prod.ext
  · exact Int.add_mul_ediv_right _ _ (by simp only [horizontalPeriod,Nat.cast_add,Nat.cast_one]; omega)
  · exact Int.add_mul_ediv_right _ _ (by simp only [verticalPeriod,Nat.cast_add,Nat.cast_one]; omega)

theorem read_holds (d : Drawing) (a : Variable → Cell → Bool)
    (location translate : Cell) (side : Side) (value : Bool) :
    (read d location side value).Holds a translate ↔
      orientation d a (lift d location translate) side = value := by
  have comm : Cell.add translate (quotient d location) =
      Cell.add (quotient d location) translate := by ext <;> simp [Cell.add,add_comm]
  simp only [PeriodicLiteral.Holds,read,orientation,address_lift,quotient_lift,comm]

theorem orientation_assignment (d : Drawing) (o : d.Orientation) :
    orientation d (assignment d o) = o := by
  funext location side
  apply congrArg (fun c => o c side)
  apply Prod.ext <;>
    simp only [lift,address,quotient,positionAt,
      residue_val_int,horizontalPeriod,verticalPeriod]
  · simpa only [horizontalPeriod,Nat.cast_add,Nat.cast_one,mul_comm] using
      Int.emod_add_mul_ediv location.1 (d.horizontalPeriod : Int)
  · simpa only [verticalPeriod,Nat.cast_add,Nat.cast_one,mul_comm] using
      Int.emod_add_mul_ediv location.2 (d.verticalPeriod : Int)

theorem getAt_lift (d : Drawing) (location translate : Cell) :
    d.getAt (lift d location translate) = d.getAt location := by
  have same := address_lift d location translate
  have positions : d.positionAt (lift d location translate) = d.positionAt location := by
    apply Prod.ext <;> apply Fin.ext
    · exact congrArg Prod.fst same
    · exact congrArg Prod.snd same
  exact congrArg d.get positions

theorem neighbor_lift (d : Drawing) (location translate : Cell) (side : Side) :
    latticeNeighbor (lift d location translate) side =
      lift d (latticeNeighbor location side) translate := by
  cases side <;> ext <;> simp [latticeNeighbor,lift] <;> omega

theorem location_decomposition (d : Drawing) (location : Cell) :
    lift d (((address d location).1 : Int),((address d location).2 : Int))
      (quotient d location) = location := by
  apply Prod.ext <;>
    simp only [lift,address,quotient,positionAt,residue_val_int,horizontalPeriod,verticalPeriod]
  · simpa only [horizontalPeriod,Nat.cast_add,Nat.cast_one,mul_comm] using
      Int.emod_add_mul_ediv location.1 (d.horizontalPeriod : Int)
  · simpa only [verticalPeriod,Nat.cast_add,Nat.cast_one,mul_comm] using
      Int.emod_add_mul_ediv location.2 (d.verticalPeriod : Int)

end LeanTrominoes.Gadget.NormalizedOrientation.AsCNF
