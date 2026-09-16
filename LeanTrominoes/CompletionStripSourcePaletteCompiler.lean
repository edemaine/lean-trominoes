/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.CompletionStripSourceColumns
import LeanTrominoes.CompletionStripSourceSparseModel
import LeanTrominoes.CompletionSparseQueryCompiler

/-! # The actual polynomial-time finite brick palette of a PSPACE source -/
noncomputable section
namespace LeanTrominoes.CompletionPattern.Runtime
open Computability Turing UnaryColumn
set_option maxHeartbeats 3000000
set_option maxRecDepth 100000

def gridSites (width height : Nat) : List (Nat×Nat) :=
  (List.range width).flatMap fun (x : Nat) => (List.range height).map fun (y : Nat) => (x,y)

theorem gridSites_bounds {w h : Nat} {p : Nat×Nat} (hp : p ∈ gridSites w h) : p.1 < w ∧ p.2 < h := by
  obtain ⟨x,hx,hp⟩ := List.mem_flatMap.mp hp
  obtain ⟨y,hy,rfl⟩ := List.mem_map.mp hp
  exact ⟨List.mem_range.mp hx,List.mem_range.mp hy⟩

def gridXCompiler {Symbol : Type} [Fintype Symbol] [Inhabited Symbol]
    {width height : List Symbol → Nat} (cw : ScalarCompiler width) (ch : ScalarCompiler height) :
    Compiler (fun s => gridSites (width s) (height s)) (fun _ p => p.1) := by
  exact cartesianLeft (naturalRange cw) (naturalRange ch)

def gridYCompiler {Symbol : Type} [Fintype Symbol] [Inhabited Symbol]
    {width height : List Symbol → Nat} (cw : ScalarCompiler width) (ch : ScalarCompiler height) :
    Compiler (fun s => gridSites (width s) (height s)) (fun _ p => p.2) := by
  exact cartesianRight (naturalRange cw) (naturalRange ch)

variable {Input : Type} {encoding : _root_.Computability.FinEncoding Input}
  {language : Input → Prop} (decider : Complexity.DeciderInPolySpace encoding language)
  [Inhabited encoding.Γ]

abbrev brickSites (s : List encoding.Γ) :=
  gridSites (StripOrientation.period (sourceDrawing decider s)) (StripOrientation.count (sourceDrawing decider s))

def brickPeriodCompiler : ScalarCompiler (fun s => StripOrientation.period (sourceDrawing decider s)) := by
  let base : Compiler (fun _ : List encoding.Γ => [()])
    (fun s _ => (sourceDrawing decider s).horizontalPeriod) := sourceWidthCompiler decider
  exact TM2ComputableInPolyTime.of_eq (scale base 128) (fun s => by simp [StripOrientation.period,Nat.mul_comm])

def brickCountCompiler : ScalarCompiler (fun s => StripOrientation.count (sourceDrawing decider s)) := by
  let base : Compiler (fun _ : List encoding.Γ => [()])
    (fun s _ => (sourceDrawing decider s).verticalPeriod) := sourceHeightCompiler decider
  exact TM2ComputableInPolyTime.of_eq (scale (add base (constant base 1)) 256)
    (fun s => by simp [StripOrientation.count,Nat.mul_comm])

def brickXCompiler : Compiler (brickSites decider) (fun _ p => p.1) :=
  gridXCompiler (brickPeriodCompiler decider) (brickCountCompiler decider)
def brickYCompiler : Compiler (brickSites decider) (fun _ p => p.2) :=
  gridYCompiler (brickPeriodCompiler decider) (brickCountCompiler decider)

def queryBoundCompiler : ScalarCompiler (fun s =>
    StripOrientation.period (sourceDrawing decider s)+StripOrientation.count (sourceDrawing decider s)+1) := by
  let cp : Compiler (fun _ : List encoding.Γ => [()])
    (fun s _ => StripOrientation.period (sourceDrawing decider s)) := brickPeriodCompiler decider
  let ch : Compiler (fun _ : List encoding.Γ => [()])
    (fun s _ => StripOrientation.count (sourceDrawing decider s)) := brickCountCompiler decider
  exact add (add cp ch) (constant cp 1)

def queryKind (d : Gadget.PeriodicOrthogonalDrawing) (p : Nat×Nat) : Fin 9 :=
  kindIndex (LBricks.stripKinds d
    (((DiagonalRouting.natSourceX p.1 p.2/64:Nat):Int),((DiagonalRouting.natSourceY p.1 p.2/64:Nat):Int)))

def queryKindCompiler : Compiler (brickSites decider)
    (fun s p => (queryKind (sourceDrawing decider s) p).val) := by
  let qx := divPowTwo (DiagonalRouting.sourceXCompiler (brickXCompiler decider) (brickYCompiler decider)) 6
  let qy := divPowTwo (DiagonalRouting.sourceYCompiler (brickXCompiler decider) (brickYCompiler decider)) 6
  exact wrappedSparseQueryCompiler qx qy (sourceXCompiler decider) (sourceYCompiler decider)
    (sourceKindCompiler decider) (sourceWidthCompiler decider) (queryBoundCompiler decider)
    (source_sparseModel decider) (by
      intro s p hp
      have bounds := gridSites_bounds hp
      dsimp [DiagonalRouting.natSourceX]
      split_ifs <;> omega)

def sourcePaletteCompiler : Compiler (brickSites decider)
    (fun s p => (StripOrientation.palette (sourceDrawing decider s) ((p.1:Int),(p.2:Int))).val) := by
  let result := natPaletteCompiler (brickXCompiler decider) (brickYCompiler decider) (queryKindCompiler decider)
  apply TM2ComputableInPolyTime.of_eq result
  intro s
  apply List.map_congr_left
  intro p _
  dsimp only
  have correct := natPalette_correct (sourceDrawing decider s) p.1 p.2
  have queryEq : queryKind (sourceDrawing decider s) p = kindIndex (LBricks.stripKinds (sourceDrawing decider s)
      (LBricks.Circuit.macroIndex (DiagonalRouting.natSourceX p.1 p.2,DiagonalRouting.natSourceY p.1 p.2))) := by
    simp [queryKind,LBricks.Circuit.macroIndex]
  rw [queryEq,correct]
end LeanTrominoes.CompletionPattern.Runtime
