/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.CompletionStripSourcePaletteCompiler

/-! # Polynomial-time palettes for arbitrary bounded drawing compilers -/
noncomputable section
namespace LeanTrominoes.CompletionPattern.Runtime.GenericDrawing
open Computability Turing UnaryColumn
set_option maxHeartbeats 3000000
set_option maxRecDepth 100000

variable {Symbol : Type} [Fintype Symbol] [Inhabited Symbol]
  (drawing : List Symbol → Gadget.PeriodicOrthogonalDrawing)
  (entries : List Symbol → List DrawingEntry)
  (cw : ScalarCompiler (fun s => (drawing s).horizontalPeriod))
  (ch : ScalarCompiler (fun s => (drawing s).verticalPeriod))
  (ex : Compiler entries (fun _ a => a.1.1.toNat))
  (ey : Compiler entries (fun _ a => a.1.2.toNat))
  (ev : Compiler entries (fun _ a => (kindIndex (LBricks.kindOf a.2)).val))
  (model : ∀ s, SparseModel (drawing s) (entries s))

abbrev brickSites (s : List Symbol) :=
  gridSites (StripOrientation.period (drawing s)) (StripOrientation.count (drawing s))

def brickPeriodCompiler : ScalarCompiler (fun s => StripOrientation.period (drawing s)) := by
  let base : Compiler (fun _ : List Symbol => [()])
    (fun s _ => (drawing s).horizontalPeriod) := cw
  exact TM2ComputableInPolyTime.of_eq (scale base 128) (fun s => by simp [StripOrientation.period,Nat.mul_comm])

def brickCountCompiler : ScalarCompiler (fun s => StripOrientation.count (drawing s)) := by
  let base : Compiler (fun _ : List Symbol => [()])
    (fun s _ => (drawing s).verticalPeriod) := ch
  exact TM2ComputableInPolyTime.of_eq (scale (add base (constant base 1)) 256)
    (fun s => by simp [StripOrientation.count,Nat.mul_comm])

def brickXCompiler : Compiler (brickSites drawing) (fun _ p => p.1) :=
  gridXCompiler (brickPeriodCompiler drawing cw) (brickCountCompiler drawing ch)
def brickYCompiler : Compiler (brickSites drawing) (fun _ p => p.2) :=
  gridYCompiler (brickPeriodCompiler drawing cw) (brickCountCompiler drawing ch)

def queryBoundCompiler : ScalarCompiler (fun s =>
    StripOrientation.period (drawing s)+StripOrientation.count (drawing s)+1) := by
  let cp : Compiler (fun _ : List Symbol => [()])
    (fun s _ => StripOrientation.period (drawing s)) := brickPeriodCompiler drawing cw
  let ch : Compiler (fun _ : List Symbol => [()])
    (fun s _ => StripOrientation.count (drawing s)) := brickCountCompiler drawing ch
  exact add (add cp ch) (constant cp 1)

def queryKindCompiler : Compiler (brickSites drawing)
    (fun s p => (queryKind (drawing s) p).val) := by
  let qx := divPowTwo (DiagonalRouting.sourceXCompiler (brickXCompiler drawing cw ch) (brickYCompiler drawing cw ch)) 6
  let qy := divPowTwo (DiagonalRouting.sourceYCompiler (brickXCompiler drawing cw ch) (brickYCompiler drawing cw ch)) 6
  exact wrappedSparseQueryCompiler qx qy (ex) (ey)
    (ev) (cw) (queryBoundCompiler drawing cw ch)
    (model) (by
      intro s p hp
      have bounds := gridSites_bounds hp
      dsimp [DiagonalRouting.natSourceX]
      split_ifs <;> omega)

def sourcePaletteCompiler : Compiler (brickSites drawing)
    (fun s p => (StripOrientation.palette (drawing s) ((p.1:Int),(p.2:Int))).val) := by
  let result := natPaletteCompiler (brickXCompiler drawing cw ch) (brickYCompiler drawing cw ch) (queryKindCompiler drawing entries cw ch ex ey ev model)
  apply TM2ComputableInPolyTime.of_eq result
  intro s
  apply List.map_congr_left
  intro p _
  dsimp only
  have correct := natPalette_correct (drawing s) p.1 p.2
  have queryEq : queryKind (drawing s) p = kindIndex (LBricks.stripKinds (drawing s)
      (LBricks.Circuit.macroIndex (DiagonalRouting.natSourceX p.1 p.2,DiagonalRouting.natSourceY p.1 p.2))) := by
    simp [queryKind,LBricks.Circuit.macroIndex]
  rw [queryEq,correct]
end LeanTrominoes.CompletionPattern.Runtime.GenericDrawing
