/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.FiniteDrawingCompletion
import LeanTrominoes.FiniteSparseCircuitQueryCompiler
import LeanTrominoes.UnaryColumnSignedFloorDivision
import LeanTrominoes.UnaryColumnSignedRemainder
import LeanTrominoes.CompletionStripSourcePaletteCompiler

/-! # Polynomial-time labels for a finite square of completion bricks -/
noncomputable section
namespace LeanTrominoes.CompletionPattern.Runtime.FiniteDrawing
open _root_.Computability Turing UnaryColumn Gadget Gadget.PeriodicOrthogonalDrawing LBricks Circuit
set_option maxHeartbeats 3000000

variable {Symbol : Type} [Fintype Symbol] [Inhabited Symbol]
variable (drawing : List Symbol → PeriodicOrthogonalDrawing)
    (entries : List Symbol → List DrawingEntry)
    (cw : ScalarCompiler (fun s => (drawing s).horizontalPeriod))
    (ch : ScalarCompiler (fun s => (drawing s).verticalPeriod))
    (ex : Compiler entries (fun _ a => a.1.1.toNat))
    (ey : Compiler entries (fun _ a => a.1.2.toNat))
    (ev : Compiler entries (fun _ a => (kindIndex (kindOf a.2)).val))
    (model : ∀ s,SparseModel (drawing s) (entries s))

def radius (s : List Symbol) : Nat := 64*(drawing s).horizontalPeriod+64*(drawing s).verticalPeriod+6

def side (s : List Symbol) : Nat := 2*radius drawing s+1

def palette (s : List Symbol) (c : Cell) : Fin 24 :=
  finiteDrawingPalette (drawing s)
    (squareOfBrick (c.1-radius drawing s,c.2-radius drawing s))

def radiusCompiler : ScalarCompiler (radius drawing) := by
  let width : Compiler (fun _ : List Symbol => [()]) (fun s _ => (drawing s).horizontalPeriod) := cw
  let height : Compiler (fun _ : List Symbol => [()]) (fun s _ => (drawing s).verticalPeriod) := ch
  exact (add (scale (add width height) 64) (constant width 6)).of_eq
    (fun s => by simp [radius,Nat.add_mul,Nat.mul_add,Nat.mul_comm])

def sideCompiler : ScalarCompiler (side drawing) := by
  let base : Compiler (fun _ : List Symbol => [()]) (fun s _ => radius drawing s) := radiusCompiler drawing cw ch
  exact (add (scale base 2) (constant base 1)).of_eq (fun s => by simp [side,Nat.mul_comm])

def xCompiler : Compiler (fun s => gridSites (side drawing s) (side drawing s)) (fun _ p => p.1) :=
  gridXCompiler (sideCompiler drawing cw ch) (sideCompiler drawing cw ch)
def yCompiler : Compiler (fun s => gridSites (side drawing s) (side drawing s)) (fun _ p => p.2) :=
  gridYCompiler (sideCompiler drawing cw ch) (sideCompiler drawing cw ch)

private def location (s : List Symbol) (p : Nat×Nat) : Cell :=
  ((p.1:Int)-radius drawing s,((p.2+p.1:Nat):Int)-((radius drawing s*2:Nat):Int))

/-- Signed floor division, sparse support lookup, and a fixed 64-square
circuit table give the exact finite physical-brick palette. -/
def paletteCompiler : Compiler (fun s => gridSites (side drawing s) (side drawing s))
    (fun s p => (palette drawing s ((p.1:Int),(p.2:Int))).val) := by
  let x := xCompiler drawing cw ch
  let y := yCompiler drawing cw ch
  let r := radiusCompiler drawing cw ch
  let rx := broadcast x r
  let twiceR := scale rx 2
  let width : Compiler (fun _ : List Symbol => [()]) (fun s _ => (drawing s).horizontalPeriod) := cw
  let c64 : ScalarCompiler (fun _ : List Symbol => 64) := constant width 64
  let qx := signedFloorDivide x rx c64 (fun _ => by decide)
  let qy := signedFloorDivide (add y x) twiceR c64 (fun _ => by decide)
  let kind := queryKindCompiler (query := fun s p => macroIndex (location drawing s p)) qx qy ex ey ev model
  let lx := signedRemainder x rx c64 (fun _ => by decide)
  let ly := signedRemainder (add y x) twiceR c64 (fun _ => by decide)
  let label := localLabelCompiler lx ly kind
  apply label.of_eq
  intro s
  apply List.map_congr_left
  intro p _
  simp only [localLabel,palette,finiteDrawingPalette,macroPalette,macroIndex,macroLocal,
    squareOfBrick,location,Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat,index_kind]
  have xeq : ((p.1:Int)-radius drawing s)%64 =
      ((((p.1:Int)-radius drawing s)%64).toNat:Int) := by
    rw [Int.toNat_of_nonneg (Int.emod_nonneg _ (by decide))]
  have yeq : ((p.2:Int)+(p.1:Int)-2*radius drawing s)%64 =
      ((((p.2:Int)+(p.1:Int)-2*radius drawing s)%64).toNat:Int) := by
    rw [Int.toNat_of_nonneg (Int.emod_nonneg _ (by decide))]
  have equal : (p.2:Int)-radius drawing s+((p.1:Int)-radius drawing s)=
      (p.2:Int)+(p.1:Int)-2*radius drawing s := by ring
  rw [equal]
  rw [show (radius drawing s:Int)*2=2*(radius drawing s:Int) by omega]
  have bx : (((p.1:Int)-radius drawing s)%64).toNat<64 := by omega
  have by' : (((p.2:Int)+(p.1:Int)-2*radius drawing s)%64).toNat<64 := by omega
  simp only [Nat.mod_eq_of_lt bx,Nat.mod_eq_of_lt by',← xeq,← yeq]
end LeanTrominoes.CompletionPattern.Runtime.FiniteDrawing
