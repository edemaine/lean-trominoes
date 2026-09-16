/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.CompletionStripBandFieldsCompiler
import LeanTrominoes.CompletionStripCapFieldsCompiler

/-! # The complete polynomial-time strip-completion reduction machine -/
noncomputable section
namespace LeanTrominoes.CompletionPattern.Runtime
open Computability Turing UnaryColumn
set_option maxHeartbeats 500000
set_option maxRecDepth 3000

variable {Symbol : Type} [Fintype Symbol] [Inhabited Symbol]
  {period count : List Symbol → Nat} {palette : List Symbol → Cell → Fin 24}

def bandListCompiler (t : Tromino)
    (cx : Compiler (fun s => gridSites (period s) (count s)) (fun _ p => p.1))
    (cy : Compiler (fun s => gridSites (period s) (count s)) (fun _ p => p.2))
    (cp : Compiler (fun s => gridSites (period s) (count s))
      (fun s p => (palette s ((p.1:Int),(p.2:Int))).val)) :
    PlacementListCompiler (fun s => (selectedRows t (period s) (count s) (palette s)).map
      (fun r => (rowPlacement t r).shift (0,2))) where
  fields := TM2ComputableInPolyTime.of_eq (bandFieldsCompiler t cx cy cp)
    (fun s => by simp [List.flatMap_map])
  count := TM2ComputableInPolyTime.of_eq (countRows (selectedSiteColumn t cp cx))
    (fun s => by simp)

def drawingBand (drawing : List Symbol → Gadget.PeriodicOrthogonalDrawing) (t : Tromino) (s : List Symbol) : List (Placement Unit) :=
  match t with
  | .L => (LBricks.bandMotif (StripOrientation.period (drawing s))
      (StripOrientation.count (drawing s)) (StripOrientation.palette (drawing s))).map
        (fun p => p.shift (0,2))
  | .I => (IBricks.bandMotif (StripOrientation.period (drawing s))
      (StripOrientation.count (drawing s)) (StripOrientation.palette (drawing s))).map
        (fun p => p.shift (0,2))

variable {drawing : List Symbol → Gadget.PeriodicOrthogonalDrawing}
  (periodMachine : ScalarCompiler (fun s => StripOrientation.period (drawing s)))
  (countMachine : ScalarCompiler (fun s => StripOrientation.count (drawing s)))
  (paletteMachine : Compiler
    (fun s => gridSites (StripOrientation.period (drawing s)) (StripOrientation.count (drawing s)))
    (fun s p => (StripOrientation.palette (drawing s) ((p.1:Int),(p.2:Int))).val))

def drawingBandCompiler (t : Tromino) : PlacementListCompiler (drawingBand drawing t) := by
  let result := bandListCompiler t (gridXCompiler periodMachine countMachine) (gridYCompiler periodMachine countMachine) paletteMachine
  apply result.ofEq
  intro s
  cases t
  · simpa only [List.map_map,Function.comp_def,drawingBand] using congrArg (fun ps : List (Placement Unit) => ps.map (fun p => p.shift (0,2)))
      (selected_placements_I (StripOrientation.period (drawing s))
        (StripOrientation.count (drawing s)) (StripOrientation.palette (drawing s)))
  · simpa only [List.map_map,Function.comp_def,drawingBand] using congrArg (fun ps : List (Placement Unit) => ps.map (fun p => p.shift (0,2)))
      (selected_placements_L (StripOrientation.period (drawing s))
        (StripOrientation.count (drawing s)) (StripOrientation.palette (drawing s)))

def drawingMotifCompiler (t : Tromino) :
    PlacementListCompiler (fun s => (StripOrientation.compile t (drawing s)).motif) := by
  let period := periodMachine
  let count : Compiler (fun _ : List Symbol => [()])
    (fun s _ => StripOrientation.count (drawing s)) := countMachine
  let bottomHeight : ScalarCompiler (fun s => StripOrientation.count (drawing s)*brickHeight t+2) :=
    add (scale count (brickHeight t)) (constant count 2)
  let zero : ScalarCompiler (fun _ : List Symbol => 0) :=
    TM2ConstantValueCompiler.computableInPolyTime id UnaryFieldEncoderMachine.unaryFields [0]
  let top := capListCompiler t true period zero
  let bottom := capListCompiler t false period bottomHeight
  let result := (drawingBandCompiler periodMachine countMachine paletteMachine t).append (top.append bottom)
  apply result.ofEq
  intro s
  cases t <;> simp [StripOrientation.compile,LBricks.compileStrip,IBricks.compileStrip,drawingBand,
    brickHeight,Placement.shift,Cell.add,Int.mul_comm]

def targetHeightCompiler (t : Tromino) :
    ScalarCompiler (fun s => (StripOrientation.compile t (drawing s)).height) := by
  let count : Compiler (fun _ : List Symbol => [()])
    (fun s _ => StripOrientation.count (drawing s)) := countMachine
  let result := add (scale count (brickHeight t)) (constant count 5)
  apply TM2ComputableInPolyTime.of_eq result
  intro s
  cases t <;> simp [StripOrientation.compile,LBricks.compileStrip,IBricks.compileStrip,brickHeight,Nat.mul_comm]

def targetPeriodCompiler (t : Tromino) :
    ScalarCompiler (fun s => (StripOrientation.compile t (drawing s)).period) := by
  let period : Compiler (fun _ : List Symbol => [()])
    (fun s _ => StripOrientation.period (drawing s)) := periodMachine
  let result := scale period (brickWidth t)
  apply TM2ComputableInPolyTime.of_eq result
  intro s
  cases t <;> simp [StripOrientation.compile,LBricks.compileStrip,IBricks.compileStrip,brickWidth,Nat.mul_comm]

/-- Actual finite-machine certificate at the target's explicit unary encoding. -/
def sourceCompletionCompiler {Input : Type} {encoding : _root_.Computability.FinEncoding Input}
    {language : Input → Prop} (decider : Complexity.DeciderInPolySpace encoding language)
    [Inhabited encoding.Γ] (t : Tromino) :
    TM2ComputableInPolyTime id CompletionStripEncoding.finEncoding.encode
      (fun s => StripOrientation.compile t (sourceDrawing decider s)) :=
  prefillEncodingCompiler
    (targetHeightCompiler (brickCountCompiler decider) t)
    (targetPeriodCompiler (brickPeriodCompiler decider) t)
    (drawingMotifCompiler (brickPeriodCompiler decider) (brickCountCompiler decider)
      (sourcePaletteCompiler decider) t)
end LeanTrominoes.CompletionPattern.Runtime
