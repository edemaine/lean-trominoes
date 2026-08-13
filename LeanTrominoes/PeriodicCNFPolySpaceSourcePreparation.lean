/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFPolySpaceRequestPadding

/-!
# Direct source preparation for the periodic-CNF request printer

The concrete request printer is fixed for one polynomial-space decider, so it
may retain the source encoding's finite symbols directly.  This avoids
re-decoding native natural fields when emitting the bounded initial
configuration.  The preprocessing pipeline appends exact unary space, clock,
and fresh counters, followed by their canonical native binary encodings.
-/

noncomputable section

namespace LeanTrominoes

open Computability Turing

namespace PeriodicCNF
namespace PolySpaceSourcePreparation

open PolySpaceRequestPadding

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

noncomputable local instance (stack : decider.tm.K) :
    Fintype (decider.tm.Γ stack) := decider.stackAlphabetFinite stack

local instance sumInhabitedLeft {Left Right : Type} [Inhabited Left] :
    Inhabited (Left ⊕ Right) := ⟨Sum.inl default⟩

def selectEverySource {Source : Type} (_ : Source) : Bool := true

/-- Wrap source symbols in an always-inhabited alphabet before invoking the
generic arithmetic padding machines.  This keeps the construction valid even
when the finite source alphabet itself is empty. -/
def optionSources (symbols : List encoding.Γ) : List (Option encoding.Γ) :=
  symbols.map some

@[simp]
theorem optionSources_length (symbols : List encoding.Γ) :
    (optionSources symbols).length = symbols.length := by
  simp [optionSources]

abbrev SpaceUnarySymbol (Source : Type) := Source ⊕ Unit

def selectSourceAfterSpace {Source : Type} : SpaceUnarySymbol Source → Bool
  | .inl _ => true
  | .inr _ => false

abbrev WidthsUnarySymbol (Source : Type) := SpaceUnarySymbol Source ⊕ Unit

def selectSourceAfterWidths {Source : Type} : WidthsUnarySymbol Source → Bool
  | .inl source => selectSourceAfterSpace source
  | .inr _ => false

abbrev FreshUnarySymbol (Source : Type) := WidthsUnarySymbol Source ⊕ Unit

def spacePaddedSources (symbols : List encoding.Γ) :
    List (SpaceUnarySymbol (Option encoding.Γ)) :=
  UnaryPolynomialPaddingMachine.paddedOutput selectEverySource
    (PolySpaceRequestPadding.spaceCoefficients decider) (optionSources symbols)

def widthsPaddedSources (symbols : List encoding.Γ) :
    List (WidthsUnarySymbol (Option encoding.Γ)) :=
  UnaryPolynomialPaddingMachine.paddedOutput selectSourceAfterSpace
    (PolySpaceRequestPadding.clockCoefficients decider)
    (spacePaddedSources decider symbols)

def freshPaddedSources (symbols : List encoding.Γ) :
    List (FreshUnarySymbol (Option encoding.Γ)) :=
  UnaryPolynomialPaddingMachine.paddedOutput selectSourceAfterWidths
    (PolySpaceRequestPadding.freshCoefficients decider)
    (widthsPaddedSources decider symbols)

@[simp]
theorem selectedCount_everySource {Source : Type} (symbols : List Source) :
    UnaryPolynomialPaddingMachine.selectedCount selectEverySource symbols =
      symbols.length := by
  induction symbols with
  | nil => rfl
  | cons symbol symbols induction =>
      simp [UnaryPolynomialPaddingMachine.selectedCount,
        selectEverySource, induction]
      omega

theorem selectedCount_map_of_true {Source Target : Type}
    (selected : Target → Bool) (embed : Source → Target)
    (selectedEmbed : ∀ source, selected (embed source) = true)
    (symbols : List Source) :
    UnaryPolynomialPaddingMachine.selectedCount selected
      (symbols.map embed) = symbols.length := by
  induction symbols with
  | nil => rfl
  | cons symbol symbols induction =>
      simp only [List.map_cons,
        UnaryPolynomialPaddingMachine.selectedCount_cons,
        selectedEmbed, if_pos, List.length_cons]
      omega

@[simp]
theorem spacePaddedSources_eq (symbols : List encoding.Γ) :
    spacePaddedSources decider symbols =
      (optionSources symbols).map Sum.inl ++
        List.replicate (PolySpaceCompiler.spaceOfSymbols decider symbols)
          (Sum.inr ()) := by
  unfold spacePaddedSources UnaryPolynomialPaddingMachine.paddedOutput
  rw [selectedCount_everySource,
    optionSources_length,
    PolySpaceRequestPadding.evalCoefficients_spaceCoefficients,
    ← PolySpaceRequestPadding.spaceOfSymbols_eq_polynomial_eval]

@[simp]
theorem selectedCount_sourceAfterSpace (symbols : List encoding.Γ) :
    UnaryPolynomialPaddingMachine.selectedCount selectSourceAfterSpace
      (spacePaddedSources decider symbols) = symbols.length := by
  rw [spacePaddedSources_eq,
    PolySpaceRequestPadding.selectedCount_append]
  have sourceCount :
      UnaryPolynomialPaddingMachine.selectedCount selectSourceAfterSpace
          ((optionSources symbols).map Sum.inl) = symbols.length := by
    simp only [optionSources, List.map_map]
    exact selectedCount_map_of_true selectSourceAfterSpace
      (fun symbol => Sum.inl (some symbol)) (fun _ => rfl) symbols
  rw [sourceCount,
    PolySpaceRequestPadding.selectedCount_replicate_of_false
      selectSourceAfterSpace (Sum.inr ()) rfl]
  omega

@[simp]
theorem widthsPaddedSources_eq (symbols : List encoding.Γ) :
    widthsPaddedSources decider symbols =
      ((optionSources symbols).map Sum.inl).map Sum.inl ++
        (List.replicate (PolySpaceCompiler.spaceOfSymbols decider symbols)
          (Sum.inr ())).map Sum.inl ++
        List.replicate
          (PolySpaceCompiler.clockBitsOfSymbols decider symbols)
          (Sum.inr ()) := by
  unfold widthsPaddedSources UnaryPolynomialPaddingMachine.paddedOutput
  rw [selectedCount_sourceAfterSpace,
    PolySpaceRequestPadding.evalCoefficients_clockCoefficients,
    ← PolySpaceRequestPadding.clockBitsOfSymbols_eq_polynomial_eval,
    spacePaddedSources_eq, List.map_append]

@[simp]
theorem selectedCount_sourceAfterWidths (symbols : List encoding.Γ) :
    UnaryPolynomialPaddingMachine.selectedCount selectSourceAfterWidths
      (widthsPaddedSources decider symbols) = symbols.length := by
  rw [widthsPaddedSources_eq,
    PolySpaceRequestPadding.selectedCount_append,
    PolySpaceRequestPadding.selectedCount_append]
  have sourceCount :
      UnaryPolynomialPaddingMachine.selectedCount selectSourceAfterWidths
          (((optionSources symbols).map Sum.inl).map Sum.inl) =
            symbols.length := by
    simp only [optionSources, List.map_map]
    exact selectedCount_map_of_true selectSourceAfterWidths
      (fun symbol => Sum.inl (Sum.inl (some symbol))) (fun _ => rfl) symbols
  rw [sourceCount]
  have spaceZero :
      UnaryPolynomialPaddingMachine.selectedCount
          (@selectSourceAfterWidths (Option encoding.Γ))
          ((List.replicate
            (PolySpaceCompiler.spaceOfSymbols decider symbols)
            (Sum.inr () : SpaceUnarySymbol (Option encoding.Γ))).map
              (fun symbol =>
                (Sum.inl symbol : WidthsUnarySymbol (Option encoding.Γ)))) =
        0 := by
    apply PolySpaceRequestPadding.selectedCount_eq_zero_of
    intro symbol membership
    obtain ⟨marker, _, rfl⟩ := List.mem_map.mp membership
    simp_all [selectSourceAfterWidths, selectSourceAfterSpace]
  rw [spaceZero,
    PolySpaceRequestPadding.selectedCount_replicate_of_false
      selectSourceAfterWidths (Sum.inr ()) rfl]
  omega

@[simp]
theorem freshPaddedSources_eq (symbols : List encoding.Γ) :
    freshPaddedSources decider symbols =
      (((optionSources symbols).map Sum.inl).map Sum.inl).map Sum.inl ++
        ((List.replicate
          (PolySpaceCompiler.spaceOfSymbols decider symbols)
          (Sum.inr ())).map Sum.inl).map Sum.inl ++
        (List.replicate
          (PolySpaceCompiler.clockBitsOfSymbols decider symbols)
          (Sum.inr ())).map Sum.inl ++
        List.replicate
          (BoundedMachineAtom.atomCount (tm := decider.tm)
            (space := PolySpaceCompiler.spaceOfSymbols decider symbols)
            (clockBits := PolySpaceCompiler.clockBitsOfSymbols decider symbols))
          (Sum.inr ()) := by
  unfold freshPaddedSources UnaryPolynomialPaddingMachine.paddedOutput
  rw [selectedCount_sourceAfterWidths,
    PolySpaceRequestPadding.evalCoefficients_freshCoefficients,
    ← PolySpaceRequestPadding.atomCountOfSymbols_eq_polynomial_eval,
    widthsPaddedSources_eq, List.map_append, List.map_append]

/-- Replacing each finite source symbol by its `some` wrapper is linear-time. -/
def optionSourcesComputableInPolyTime :
    @TM2ComputableInPolyTime
      (List encoding.Γ) (List (Option encoding.Γ))
      encoding.Γ (Option encoding.Γ) id id optionSources := by
  let certificate := FiniteBlockTransducer.computableInPolyTime
    (fun symbol : encoding.Γ => [some symbol])
  refine
    { tm := certificate.tm
      inputAlphabet := certificate.inputAlphabet
      outputAlphabet := certificate.outputAlphabet
      time := certificate.time
      outputsFun := ?_ }
  intro symbols
  have flatMapEq :
      symbols.flatMap (fun symbol => [some symbol]) = optionSources symbols := by
    induction symbols with
    | nil => rfl
    | cons symbol symbols induction =>
        simp [optionSources, induction]
  rw [← flatMapEq]
  exact certificate.outputsFun symbols

def appendSpaceUnaryComputableInPolyTime :
    @TM2ComputableInPolyTime
      (List (Option encoding.Γ))
      (List (SpaceUnarySymbol (Option encoding.Γ)))
      (Option encoding.Γ) (SpaceUnarySymbol (Option encoding.Γ)) id id
      (UnaryPolynomialPaddingMachine.paddedOutput selectEverySource
        (PolySpaceRequestPadding.spaceCoefficients decider)) :=
  UnaryPolynomialPaddingMachine.computableInPolyTime selectEverySource
    (PolySpaceRequestPadding.spaceCoefficients decider)

def spaceUnaryComputableInPolyTime :
    @TM2ComputableInPolyTime
      (List encoding.Γ) (List (SpaceUnarySymbol (Option encoding.Γ)))
      encoding.Γ (SpaceUnarySymbol (Option encoding.Γ)) id id
      (spacePaddedSources decider) := by
  let composed := TM2CompositionMachine.computableInPolyTime
    optionSourcesComputableInPolyTime
    (appendSpaceUnaryComputableInPolyTime decider)
  unfold spacePaddedSources
  exact composed

def appendClockUnaryComputableInPolyTime :
    @TM2ComputableInPolyTime
      (List (SpaceUnarySymbol (Option encoding.Γ)))
      (List (WidthsUnarySymbol (Option encoding.Γ)))
      (SpaceUnarySymbol (Option encoding.Γ))
      (WidthsUnarySymbol (Option encoding.Γ)) id id
      (UnaryPolynomialPaddingMachine.paddedOutput selectSourceAfterSpace
        (PolySpaceRequestPadding.clockCoefficients decider)) :=
  UnaryPolynomialPaddingMachine.computableInPolyTime selectSourceAfterSpace
    (PolySpaceRequestPadding.clockCoefficients decider)

def appendFreshUnaryComputableInPolyTime :
    @TM2ComputableInPolyTime
      (List (WidthsUnarySymbol (Option encoding.Γ)))
      (List (FreshUnarySymbol (Option encoding.Γ)))
      (WidthsUnarySymbol (Option encoding.Γ))
      (FreshUnarySymbol (Option encoding.Γ)) id id
      (UnaryPolynomialPaddingMachine.paddedOutput selectSourceAfterWidths
        (PolySpaceRequestPadding.freshCoefficients decider)) :=
  UnaryPolynomialPaddingMachine.computableInPolyTime selectSourceAfterWidths
    (PolySpaceRequestPadding.freshCoefficients decider)

def freshUnaryComputableInPolyTime :
    @TM2ComputableInPolyTime
      (List encoding.Γ) (List (FreshUnarySymbol (Option encoding.Γ)))
      encoding.Γ (FreshUnarySymbol (Option encoding.Γ)) id id
      (freshPaddedSources decider) := by
  let widths := TM2CompositionMachine.computableInPolyTime
    (spaceUnaryComputableInPolyTime decider)
    (appendClockUnaryComputableInPolyTime decider)
  let composed := TM2CompositionMachine.computableInPolyTime widths
    (appendFreshUnaryComputableInPolyTime decider)
  unfold freshPaddedSources widthsPaddedSources
  exact composed

def isSpaceMarker {Source : Type} : FreshUnarySymbol Source → Bool
  | .inl (.inl (.inr _)) => true
  | _ => false

def isClockMarker {Source : Type} : FreshUnarySymbol Source → Bool
  | .inl (.inr _) => true
  | _ => false

def isFreshMarker {Source : Type} : FreshUnarySymbol Source → Bool
  | .inr _ => true
  | _ => false

abbrev SpaceBinarySymbol (Source : Type) :=
  FreshUnarySymbol Source ⊕ PartrecToTM2.Γ'

def isClockAfterSpace {Source : Type} : SpaceBinarySymbol Source → Bool
  | .inl source => isClockMarker source
  | .inr _ => false

abbrev WidthsBinarySymbol (Source : Type) :=
  SpaceBinarySymbol Source ⊕ PartrecToTM2.Γ'

def isFreshAfterSpace {Source : Type} : SpaceBinarySymbol Source → Bool
  | .inl source => isFreshMarker source
  | .inr _ => false

def isFreshAfterWidths {Source : Type} : WidthsBinarySymbol Source → Bool
  | .inl source => isFreshAfterSpace source
  | .inr _ => false

abbrev PreparedSymbol (Source : Type) :=
  WidthsBinarySymbol Source ⊕ PartrecToTM2.Γ'

def spaceBinarySources (symbols : List encoding.Γ) :
    List (SpaceBinarySymbol (Option encoding.Γ)) :=
  BinaryCountPaddingMachine.paddedOutput isSpaceMarker
    (freshPaddedSources decider symbols)

def widthsBinarySources (symbols : List encoding.Γ) :
    List (WidthsBinarySymbol (Option encoding.Γ)) :=
  BinaryCountPaddingMachine.paddedOutput isClockAfterSpace
    (spaceBinarySources decider symbols)

def preparedSources (symbols : List encoding.Γ) :
    List (PreparedSymbol (Option encoding.Γ)) :=
  BinaryCountPaddingMachine.paddedOutput isFreshAfterWidths
    (widthsBinarySources decider symbols)

theorem count_eq_of_layout
    (symbols : List encoding.Γ) :
    BinaryCountPaddingMachine.selectedCount isSpaceMarker
        (freshPaddedSources decider symbols) =
        PolySpaceCompiler.spaceOfSymbols decider symbols ∧
      BinaryCountPaddingMachine.selectedCount isClockMarker
        (freshPaddedSources decider symbols) =
        PolySpaceCompiler.clockBitsOfSymbols decider symbols ∧
      BinaryCountPaddingMachine.selectedCount isFreshMarker
        (freshPaddedSources decider symbols) =
        BoundedMachineAtom.atomCount (tm := decider.tm)
          (space := PolySpaceCompiler.spaceOfSymbols decider symbols)
          (clockBits := PolySpaceCompiler.clockBitsOfSymbols decider symbols) := by
  rw [freshPaddedSources_eq]
  constructor
  · simp [PolySpaceRequestPadding.binarySelectedCount_append,
      PolySpaceRequestPadding.binarySelectedCount_eq_zero_of,
      PolySpaceRequestPadding.binarySelectedCount_replicate_true,
      isSpaceMarker]
  constructor
  · simp [PolySpaceRequestPadding.binarySelectedCount_append,
      PolySpaceRequestPadding.binarySelectedCount_eq_zero_of,
      PolySpaceRequestPadding.binarySelectedCount_replicate_true,
      isClockMarker]
  · simp [PolySpaceRequestPadding.binarySelectedCount_append,
      PolySpaceRequestPadding.binarySelectedCount_eq_zero_of,
      PolySpaceRequestPadding.binarySelectedCount_replicate_true,
      isFreshMarker]

def appendSpaceBinaryComputableInPolyTime :
    @TM2ComputableInPolyTime
      (List (FreshUnarySymbol (Option encoding.Γ)))
      (List (SpaceBinarySymbol (Option encoding.Γ)))
      (FreshUnarySymbol (Option encoding.Γ))
      (SpaceBinarySymbol (Option encoding.Γ)) id id
      (BinaryCountPaddingMachine.paddedOutput isSpaceMarker) :=
  BinaryCountPaddingMachine.computableInPolyTime isSpaceMarker

def appendClockBinaryComputableInPolyTime :
    @TM2ComputableInPolyTime
      (List (SpaceBinarySymbol (Option encoding.Γ)))
      (List (WidthsBinarySymbol (Option encoding.Γ)))
      (SpaceBinarySymbol (Option encoding.Γ))
      (WidthsBinarySymbol (Option encoding.Γ)) id id
      (BinaryCountPaddingMachine.paddedOutput isClockAfterSpace) :=
  BinaryCountPaddingMachine.computableInPolyTime isClockAfterSpace

def appendFreshBinaryComputableInPolyTime :
    @TM2ComputableInPolyTime
      (List (WidthsBinarySymbol (Option encoding.Γ)))
      (List (PreparedSymbol (Option encoding.Γ)))
      (WidthsBinarySymbol (Option encoding.Γ))
      (PreparedSymbol (Option encoding.Γ)) id id
      (BinaryCountPaddingMachine.paddedOutput isFreshAfterWidths) :=
  BinaryCountPaddingMachine.computableInPolyTime isFreshAfterWidths

/-- Direct finite-source arithmetic preprocessing is polynomial-time. -/
def preparedComputableInPolyTime :
    @TM2ComputableInPolyTime
      (List encoding.Γ) (List (PreparedSymbol (Option encoding.Γ)))
      encoding.Γ (PreparedSymbol (Option encoding.Γ)) id id
      (preparedSources decider) := by
  let space := TM2CompositionMachine.computableInPolyTime
    (freshUnaryComputableInPolyTime decider)
    appendSpaceBinaryComputableInPolyTime
  let clock := TM2CompositionMachine.computableInPolyTime space
    appendClockBinaryComputableInPolyTime
  let composed := TM2CompositionMachine.computableInPolyTime clock
    appendFreshBinaryComputableInPolyTime
  unfold preparedSources widthsBinarySources spaceBinarySources
  exact composed

end PolySpaceSourcePreparation
end PeriodicCNF
end LeanTrominoes
