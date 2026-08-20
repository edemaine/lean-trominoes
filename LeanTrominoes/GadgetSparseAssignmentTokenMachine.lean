/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.GadgetSparseAssignmentTokens

/-! # Finite machine expanding sparse assignment records

The two unary coordinates of a sparse assignment are retained on work tapes.
For each of the finitely many pixels in the selected Figure 11/12 cell, the
machine copies both coordinates into the prepared output and appends the two
bounded local offsets.  This file contains only the finite machine and its
configuration vocabulary; execution and time proofs are split into leaves.
-/

namespace LeanTrominoes

open Computability StateTransition Turing

noncomputable section

namespace GadgetSparseAssignmentTokenMachine

open Gadget

abbrev InputToken := GadgetSparseAssignmentTokens.Token
abbrev OutputToken := GadgetPixelFiniteTokens.Token
abbrev LocalPixel := Fin 6 × Fin 6

/-- An extra cursor value is reserved for the end of every `6 × 6` mask. -/
abbrev PixelIndex := Fin 37

def firstPixelIndex : PixelIndex := ⟨0, by decide⟩

/-- The bounded local pixel at one finite cursor position. -/
def pixelAt? (tromino : Tromino) (cellType : OrthogonalCellType)
    (index : PixelIndex) : Option LocalPixel :=
  ((orthogonalCellPixels tromino cellType).map
      GadgetExpandedMotifFiniteTokens.boundedPixel)[index.val]?

/-- Move to the next cursor, except after the reserved final position. -/
def nextPixelIndex (index : PixelIndex) : Option PixelIndex :=
  if nextInRange : index.val + 1 < 37 then
    some ⟨index.val + 1, nextInRange⟩
  else
    none

inductive ResetTarget
  | scan
  | reverseOutput
  deriving DecidableEq, Fintype

inductive Stack
  | input
  | horizontal
  | vertical
  | scratch
  | outputReverse
  | output
  deriving DecidableEq, Fintype

inductive Label
  | scanHorizontal
  | scanVertical
  | beginPixels (cellType : OrthogonalCellType)
  | pixelStart (cellType : OrthogonalCellType) (index : PixelIndex)
  | copyHorizontal (cellType : OrthogonalCellType) (index : PixelIndex)
      (pixel : LocalPixel)
  | restoreHorizontal (cellType : OrthogonalCellType) (index : PixelIndex)
      (pixel : LocalPixel)
  | copyVertical (cellType : OrthogonalCellType) (index : PixelIndex)
      (pixel : LocalPixel)
  | restoreVertical (cellType : OrthogonalCellType) (index : PixelIndex)
      (pixel : LocalPixel)
  | clearHorizontal (target : ResetTarget)
  | clearVertical (target : ResetTarget)
  | reverseOutput
  deriving Fintype

/-- A transition temporarily holds an input symbol, a work-tape unit, or an
output symbol. -/
abbrev State := Option (InputToken ⊕ (Unit ⊕ OutputToken))

abbrev Alphabet : Stack → Type
  | .input => InputToken
  | .horizontal | .vertical | .scratch => Unit
  | .outputReverse | .output => OutputToken

def inputFromState : State → InputToken
  | some (.inl token) => token
  | _ => default

def outputFromState : State → OutputToken
  | some (.inr (.inr token)) => token
  | _ => default

def isCoordinateUnitState : State → Bool
  | some (.inl .coordinateUnit) => true
  | _ => false

def isFieldEndState : State → Bool
  | some (.inl .fieldEnd) => true
  | _ => false

def cellTypeFromState : State → OrthogonalCellType
  | some (.inl (.cellType cellType)) => cellType
  | _ => .blank

def afterClear : ResetTarget → Label
  | .scan => .scanHorizontal
  | .reverseOutput => .reverseOutput

/-- Copy a unary record into the fixed prepared blocks of all selected local
pixels.  Output is accumulated in reverse and reversed once at the end. -/
def program (tromino : Tromino) : Label → TM2.Stmt Alphabet Label State
  | .scanHorizontal =>
      .pop .input (fun _ token => token.map Sum.inl)
        (.branch Option.isNone
          (.goto fun _ => .clearHorizontal .reverseOutput)
          (.branch isCoordinateUnitState
            (.push .horizontal (fun _ => ())
              (.load (fun _ => none) (.goto fun _ => .scanHorizontal)))
            (.branch isFieldEndState
              (.load (fun _ => none) (.goto fun _ => .scanVertical))
              (.load (fun _ => none)
                (.goto fun _ => .clearHorizontal .scan)))))
  | .scanVertical =>
      .pop .input (fun _ token => token.map Sum.inl)
        (.branch Option.isNone
          (.goto fun _ => .clearHorizontal .reverseOutput)
          (.branch isCoordinateUnitState
            (.push .vertical (fun _ => ())
              (.load (fun _ => none) (.goto fun _ => .scanVertical)))
            (.branch isFieldEndState
              (.load (fun _ => none)
                (.goto fun _ => .clearHorizontal .scan))
              (.goto fun state =>
                .beginPixels (cellTypeFromState state)))))
  | .beginPixels cellType =>
      .load (fun _ => none)
        (.goto fun _ => .pixelStart cellType firstPixelIndex)
  | .pixelStart cellType index =>
      match pixelAt? tromino cellType index with
      | none => .goto fun _ => .clearHorizontal .scan
      | some pixel =>
          .push .outputReverse (fun _ => .cellMarker)
            (.goto fun _ => .copyHorizontal cellType index pixel)
  | .copyHorizontal cellType index pixel =>
      .pop .horizontal
        (fun _ unit => unit.map fun _ => Sum.inr (Sum.inl ()))
        (.branch Option.isNone
          (.push .outputReverse (fun _ => .localOffset pixel.1)
            (.push .outputReverse (fun _ => .fieldEnd)
              (.goto fun _ => .restoreHorizontal cellType index pixel)))
          (.push .scratch (fun _ => ())
            (.push .outputReverse (fun _ => .coordinateUnit)
              (.load (fun _ => none)
                (.goto fun _ => .copyHorizontal cellType index pixel)))))
  | .restoreHorizontal cellType index pixel =>
      .pop .scratch
        (fun _ unit => unit.map fun _ => Sum.inr (Sum.inl ()))
        (.branch Option.isNone
          (.goto fun _ => .copyVertical cellType index pixel)
          (.push .horizontal (fun _ => ())
            (.load (fun _ => none)
              (.goto fun _ => .restoreHorizontal cellType index pixel))))
  | .copyVertical cellType index pixel =>
      .pop .vertical
        (fun _ unit => unit.map fun _ => Sum.inr (Sum.inl ()))
        (.branch Option.isNone
          (.push .outputReverse (fun _ => .localOffset pixel.2)
            (.push .outputReverse (fun _ => .fieldEnd)
              (.goto fun _ => .restoreVertical cellType index pixel)))
          (.push .scratch (fun _ => ())
            (.push .outputReverse (fun _ => .coordinateUnit)
              (.load (fun _ => none)
                (.goto fun _ => .copyVertical cellType index pixel)))))
  | .restoreVertical cellType index pixel =>
      .pop .scratch
        (fun _ unit => unit.map fun _ => Sum.inr (Sum.inl ()))
        (.branch Option.isNone
          (match nextPixelIndex index with
          | some next => .goto fun _ => .pixelStart cellType next
          | none => .goto fun _ => .clearHorizontal .scan)
          (.push .vertical (fun _ => ())
            (.load (fun _ => none)
              (.goto fun _ => .restoreVertical cellType index pixel))))
  | .clearHorizontal target =>
      .pop .horizontal
        (fun _ unit => unit.map fun _ => Sum.inr (Sum.inl ()))
        (.branch Option.isNone
          (.goto fun _ => .clearVertical target)
          (.load (fun _ => none) (.goto fun _ => .clearHorizontal target)))
  | .clearVertical target =>
      .pop .vertical
        (fun _ unit => unit.map fun _ => Sum.inr (Sum.inl ()))
        (.branch Option.isNone
          (.goto fun _ => afterClear target)
          (.load (fun _ => none) (.goto fun _ => .clearVertical target)))
  | .reverseOutput =>
      .pop .outputReverse
        (fun _ token => token.map fun value => Sum.inr (Sum.inr value))
        (.branch Option.isNone
          .halt
          (.push .output outputFromState
            (.load (fun _ => none) (.goto fun _ => .reverseOutput))))

abbrev machine (tromino : Tromino) : FinTM2 where
  K := Stack
  k₀ := .input
  k₁ := .output
  Γ := Alphabet
  Λ := Label
  main := .scanHorizontal
  σ := State
  initialState := none
  m := program tromino

structure TapeData where
  input : List InputToken
  horizontal : List Unit
  vertical : List Unit
  scratch : List Unit
  outputReverse : List OutputToken
  output : List OutputToken

def tapes (data : TapeData) : ∀ stack, List (Alphabet stack)
  | .input => data.input
  | .horizontal => data.horizontal
  | .vertical => data.vertical
  | .scratch => data.scratch
  | .outputReverse => data.outputReverse
  | .output => data.output

def cfg (label : Label) (state : State) (data : TapeData) :
    TM2.Cfg Alphabet Label State :=
  ⟨some label, state, tapes data⟩

def scanHorizontalCfg (data : TapeData) := cfg .scanHorizontal none data
def scanVerticalCfg (data : TapeData) := cfg .scanVertical none data
def beginPixelsCfg (cellType : OrthogonalCellType) (state : State)
    (data : TapeData) := cfg (.beginPixels cellType) state data
def pixelStartCfg (cellType : OrthogonalCellType) (index : PixelIndex)
    (data : TapeData) := cfg (.pixelStart cellType index) none data
def copyHorizontalCfg (cellType : OrthogonalCellType) (index : PixelIndex)
    (pixel : LocalPixel) (data : TapeData) :=
  cfg (.copyHorizontal cellType index pixel) none data
def restoreHorizontalCfg (cellType : OrthogonalCellType) (index : PixelIndex)
    (pixel : LocalPixel) (data : TapeData) :=
  cfg (.restoreHorizontal cellType index pixel) none data
def copyVerticalCfg (cellType : OrthogonalCellType) (index : PixelIndex)
    (pixel : LocalPixel) (data : TapeData) :=
  cfg (.copyVertical cellType index pixel) none data
def restoreVerticalCfg (cellType : OrthogonalCellType) (index : PixelIndex)
    (pixel : LocalPixel) (data : TapeData) :=
  cfg (.restoreVertical cellType index pixel) none data
def clearHorizontalCfg (target : ResetTarget) (data : TapeData) :=
  cfg (.clearHorizontal target) none data
def clearVerticalCfg (target : ResetTarget) (data : TapeData) :=
  cfg (.clearVertical target) none data
def reverseOutputCfg (data : TapeData) := cfg .reverseOutput none data

def haltDataCfg (data : TapeData) : TM2.Cfg Alphabet Label State :=
  ⟨none, none, tapes data⟩

def haltCfg (output : List OutputToken) : TM2.Cfg Alphabet Label State :=
  haltDataCfg ⟨[], [], [], [], [], output⟩

end GadgetSparseAssignmentTokenMachine
end
end LeanTrominoes
