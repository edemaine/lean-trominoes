/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.GadgetPixelFiniteTokens
import LeanTrominoes.UnaryPolynomialPaddingMachine

/-! # Prepared strip-header data from a unary period scale -/

noncomputable section

namespace LeanTrominoes
namespace GadgetPreparedHeaderEmitter

open GadgetPixelFiniteTokens

abbrev SentinelSymbol := Unit ⊕ Unit
abbrev PeriodSymbol := SentinelSymbol ⊕ Unit
abbrev EndSymbol := PeriodSymbol ⊕ Unit

def selectNone {Source : Type} (_ : Source) : Bool := false

def selectGrid : SentinelSymbol → Bool
  | .inl _ => true
  | .inr _ => false

/-- Retain the unary scale and append one distinguished boundary symbol. -/
def addSentinel (grid : List Unit) : List SentinelSymbol :=
  UnaryPolynomialPaddingMachine.paddedOutput selectNone [1] grid

/-- Retain the boundary-marked scale and append `factor * grid.length`
distinguished horizontal-period symbols. -/
def addPeriod (factor : Nat) (word : List SentinelSymbol) :
    List PeriodSymbol :=
  UnaryPolynomialPaddingMachine.paddedOutput selectGrid [0, factor] word

/-- Append one final distinguished symbol after the horizontal-period run. -/
def addEnd (word : List PeriodSymbol) : List EndSymbol :=
  UnaryPolynomialPaddingMachine.paddedOutput selectNone [1] word

/-- Interpret the four symbol kinds as vertical units, the field boundary,
horizontal units, and the final field boundary. -/
def block (factor : Nat) : EndSymbol → List GadgetPixelFiniteTokens.Token
  | .inl (.inl (.inl _)) =>
      List.replicate (3 * factor) .headerUnit
  | .inl (.inl (.inr _)) => [.headerUnit, .fieldEnd]
  | .inl (.inr _) => [.headerUnit]
  | .inr _ => [.fieldEnd]

/-- The complete prepared header emitted from a unary underlying scale. -/
def preparedHeader (factor : Nat) (grid : List Unit) :
    List GadgetPixelFiniteTokens.Token :=
  (addEnd (addPeriod factor (addSentinel grid))).flatMap (block factor)

@[simp] theorem addSentinel_eq (grid : List Unit) :
    addSentinel grid =
      grid.map (fun item => (Sum.inl item : SentinelSymbol)) ++
        [.inr ()] := by
  simp [addSentinel, UnaryPolynomialPaddingMachine.paddedOutput,
    UnaryPolynomialPaddingMachine.evalCoefficients]

@[simp] theorem selectedCount_selectGrid_addSentinel (grid : List Unit) :
    UnaryPolynomialPaddingMachine.selectedCount selectGrid
        (addSentinel grid) = grid.length := by
  rw [addSentinel_eq]
  induction grid with
  | nil => simp [UnaryPolynomialPaddingMachine.selectedCount, selectGrid]
  | cons item grid induction =>
      simp [selectGrid, induction]
      omega

@[simp] theorem addPeriod_addSentinel_eq (factor : Nat)
    (grid : List Unit) :
    addPeriod factor (addSentinel grid) =
      (addSentinel grid).map
          (fun symbol => (Sum.inl symbol : PeriodSymbol)) ++
        List.replicate (factor * grid.length) (.inr ()) := by
  unfold addPeriod UnaryPolynomialPaddingMachine.paddedOutput
  rw [selectedCount_selectGrid_addSentinel]
  simp [UnaryPolynomialPaddingMachine.evalCoefficients]

@[simp] theorem addEnd_eq (word : List PeriodSymbol) :
    addEnd word =
      word.map (fun symbol => (Sum.inl symbol : EndSymbol)) ++
        [.inr ()] := by
  simp [addEnd, UnaryPolynomialPaddingMachine.paddedOutput,
    UnaryPolynomialPaddingMachine.evalCoefficients]

end GadgetPreparedHeaderEmitter
end LeanTrominoes
