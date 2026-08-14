/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFPolySpaceProgramSpec
import LeanTrominoes.PeriodicCNFPolySpaceSourcePreparation
import LeanTrominoes.PeriodicCNFUnaryProgramTokens

/-!
# Four-block unary input layout for the compact request emitter

Once runtime atom fields are emitted in unary, the request printer no longer
needs the three redundant canonical-binary width blocks.  The existing source
preprocessor already produces exactly the four required finite blocks:
original source symbols, unary stack width, unary reset-clock width, and the
unary first-fresh-atom boundary.

This file names that smaller layout and proves exact recovery of every
semantic input to the finite counter-driven emitter.
-/

noncomputable section

namespace LeanTrominoes

open Computability Turing

namespace PeriodicCNF
namespace PolySpaceUnaryPreparedLayout

open PolySpaceSourcePreparation

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

noncomputable local instance (stack : decider.tm.K) :
    Fintype (decider.tm.Γ stack) := decider.stackAlphabetFinite stack

abbrev Symbol (encoding : _root_.Computability.FinEncoding Input) :=
  FreshUnarySymbol (Option encoding.Γ)

def embedSource (symbol : encoding.Γ) : Symbol encoding :=
  .inl (.inl (.inl (some symbol)))

def embedSpace : Symbol encoding :=
  .inl (.inl (.inr ()))

def embedClock : Symbol encoding :=
  .inl (.inr ())

def embedFresh : Symbol encoding :=
  .inr ()

/-- Exact four-block word consumed by the unary request emitter. -/
def layout (symbols : List encoding.Γ) (space clockWidth fresh : Nat) :
    List (Symbol encoding) :=
  symbols.map embedSource ++
    List.replicate space embedSpace ++
    List.replicate clockWidth embedClock ++
    List.replicate fresh embedFresh

/-- The smaller printer input is the already verified unary prefix of source
preparation. -/
def preparedSources (symbols : List encoding.Γ) : List (Symbol encoding) :=
  PolySpaceSourcePreparation.freshPaddedSources decider symbols

@[simp]
theorem preparedSources_eq_layout (symbols : List encoding.Γ) :
    preparedSources decider symbols =
      layout symbols
        (PolySpaceCompiler.spaceOfSymbols decider symbols)
        (PolySpaceCompiler.clockBitsOfSymbols decider symbols)
        (BoundedMachineAtom.atomCount (tm := decider.tm)
          (space := PolySpaceCompiler.spaceOfSymbols decider symbols)
          (clockBits :=
            PolySpaceCompiler.clockBitsOfSymbols decider symbols)) := by
  unfold preparedSources
  rw [PolySpaceSourcePreparation.freshPaddedSources_eq]
  simp [layout, embedSource, embedSpace, embedClock, embedFresh,
    PolySpaceSourcePreparation.optionSources, List.map_map,
    Function.comp_def, List.append_assoc]

def sourceSymbol : Symbol encoding → Option encoding.Γ
  | .inl (.inl (.inl (some symbol))) => some symbol
  | _ => none

def sourceSymbols (word : List (Symbol encoding)) : List encoding.Γ :=
  word.filterMap sourceSymbol

def isSpace : Symbol encoding → Bool
  | .inl (.inl (.inr _)) => true
  | _ => false

def isClock : Symbol encoding → Bool
  | .inl (.inr _) => true
  | _ => false

def isFresh : Symbol encoding → Bool
  | .inr _ => true
  | _ => false

def space (word : List (Symbol encoding)) : Nat :=
  UnaryPolynomialPaddingMachine.selectedCount isSpace word

def clockWidth (word : List (Symbol encoding)) : Nat :=
  UnaryPolynomialPaddingMachine.selectedCount isClock word

def fresh (word : List (Symbol encoding)) : Nat :=
  UnaryPolynomialPaddingMachine.selectedCount isFresh word

theorem selectedCount_append {Source : Type} (selected : Source → Bool)
    (first second : List Source) :
    UnaryPolynomialPaddingMachine.selectedCount selected (first ++ second) =
      UnaryPolynomialPaddingMachine.selectedCount selected first +
        UnaryPolynomialPaddingMachine.selectedCount selected second := by
  induction first with
  | nil => simp [UnaryPolynomialPaddingMachine.selectedCount]
  | cons source first induction =>
      simp only [List.cons_append,
        UnaryPolynomialPaddingMachine.selectedCount_cons, induction]
      omega

theorem selectedCount_eq_zero_of {Source : Type}
    (selected : Source → Bool) (word : List Source)
    (noneSelected : ∀ source ∈ word, selected source = false) :
    UnaryPolynomialPaddingMachine.selectedCount selected word = 0 := by
  induction word with
  | nil => rfl
  | cons source word induction =>
      have sourceFalse := noneSelected source (by simp)
      rw [UnaryPolynomialPaddingMachine.selectedCount_cons, sourceFalse]
      simp only [Bool.false_eq_true, if_false, Nat.zero_add]
      change UnaryPolynomialPaddingMachine.selectedCount selected word = 0
      exact induction fun item membership =>
        noneSelected item (by simp [membership])

theorem selectedCount_replicate_true {Source : Type}
    (selected : Source → Bool) (source : Source)
    (selectedSource : selected source = true) (count : Nat) :
    UnaryPolynomialPaddingMachine.selectedCount selected
      (List.replicate count source) = count := by
  induction count with
  | zero => rfl
  | succ count induction =>
      rw [List.replicate_succ,
        UnaryPolynomialPaddingMachine.selectedCount_cons,
        if_pos selectedSource, induction]
      omega

@[simp]
theorem sourceSymbols_layout (symbols : List encoding.Γ)
    (spaceValue clockValue freshValue : Nat) :
    sourceSymbols
      (layout symbols spaceValue clockValue freshValue) = symbols := by
  simp [sourceSymbols, layout, sourceSymbol, embedSource, embedSpace,
    embedClock, embedFresh]

@[simp]
theorem space_layout (symbols : List encoding.Γ)
    (spaceValue clockValue freshValue : Nat) :
    space (layout symbols spaceValue clockValue freshValue) = spaceValue := by
  simp [space, layout, selectedCount_append, isSpace, embedSource,
    embedSpace, embedClock, embedFresh, selectedCount_replicate_true,
    selectedCount_eq_zero_of]

@[simp]
theorem clockWidth_layout (symbols : List encoding.Γ)
    (spaceValue clockValue freshValue : Nat) :
    clockWidth (layout symbols spaceValue clockValue freshValue) =
      clockValue := by
  simp [clockWidth, layout, selectedCount_append, isClock, embedSource,
    embedSpace, embedClock, embedFresh, selectedCount_replicate_true,
    selectedCount_eq_zero_of]

@[simp]
theorem fresh_layout (symbols : List encoding.Γ)
    (spaceValue clockValue freshValue : Nat) :
    fresh (layout symbols spaceValue clockValue freshValue) = freshValue := by
  simp [fresh, layout, selectedCount_append, isFresh, embedSource,
    embedSpace, embedClock, embedFresh, selectedCount_replicate_true,
    selectedCount_eq_zero_of]

@[simp]
theorem sourceSymbols_preparedSources (symbols : List encoding.Γ) :
    sourceSymbols (preparedSources decider symbols) = symbols := by
  rw [preparedSources_eq_layout]
  simp

@[simp]
theorem space_preparedSources (symbols : List encoding.Γ) :
    space (preparedSources decider symbols) =
      PolySpaceCompiler.spaceOfSymbols decider symbols := by
  rw [preparedSources_eq_layout]
  simp

@[simp]
theorem clockWidth_preparedSources (symbols : List encoding.Γ) :
    clockWidth (preparedSources decider symbols) =
      PolySpaceCompiler.clockBitsOfSymbols decider symbols := by
  rw [preparedSources_eq_layout]
  simp

@[simp]
theorem fresh_preparedSources (symbols : List encoding.Γ) :
    fresh (preparedSources decider symbols) =
      PolySpaceProgramSpec.fresh decider symbols := by
  rw [preparedSources_eq_layout]
  simp [PolySpaceProgramSpec.fresh]

/-- Exact finite-token request to be emitted from an arbitrary four-block
word. -/
def tokenRequest (word : List (Symbol encoding)) :
    List UnaryProgramTokens.Token :=
  UnaryProgramTokens.requestSource (fresh word)
    (PolySpaceProgramSpec.program decider (sourceSymbols word))

/-- On every genuine preprocessor output, the four-block specification is the
normalized source request exactly. -/
@[simp]
theorem tokenRequest_preparedSources (symbols : List encoding.Γ) :
    tokenRequest decider (preparedSources decider symbols) =
      UnaryProgramTokens.requestSource
        (PolySpaceProgramSpec.fresh decider symbols)
        (PolySpaceProgramSpec.program decider symbols) := by
  unfold tokenRequest
  rw [sourceSymbols_preparedSources, fresh_preparedSources]

/-- Preparing the four-block unary input is polynomial-time. -/
def preparedComputableInPolyTime :
    @TM2ComputableInPolyTime
      (List encoding.Γ) (List (Symbol encoding))
      encoding.Γ (Symbol encoding) id id (preparedSources decider) :=
  PolySpaceSourcePreparation.freshUnaryComputableInPolyTime decider

end PolySpaceUnaryPreparedLayout
end PeriodicCNF
end LeanTrominoes
