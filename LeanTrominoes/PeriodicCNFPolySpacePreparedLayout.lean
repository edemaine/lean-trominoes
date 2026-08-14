/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFProgramTokens
import LeanTrominoes.PeriodicCNFPolySpaceProgramSpec
import LeanTrominoes.PeriodicCNFPolySpaceSourcePreparation

/-!
# Exact finite input layout for the compact request printer

The arithmetic preprocessing pipeline uses nested sum alphabets to retain the
original finite source and distinguish six appended blocks.  This file names
the seven resulting embeddings, proves the complete flattened layout, and
provides projections recovering every semantic component.  These are the
input invariants used by the finite counter-driven instruction emitter.
-/

noncomputable section

namespace LeanTrominoes

open Computability Turing

namespace PeriodicCNF
namespace PolySpacePreparedLayout

open PolySpaceSourcePreparation

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

noncomputable local instance (stack : decider.tm.K) :
    Fintype (decider.tm.Γ stack) := decider.stackAlphabetFinite stack

abbrev Symbol (encoding : _root_.Computability.FinEncoding Input) :=
  PreparedSymbol (Option encoding.Γ)

def embedUnary {Source : Type} :
    FreshUnarySymbol Source → PreparedSymbol Source :=
  fun symbol => .inl (.inl (.inl symbol))

def embedSource {Source : Type} (source : Source) : PreparedSymbol Source :=
  embedUnary (.inl (.inl (.inl source)))

def embedSpaceMarker {Source : Type} : PreparedSymbol Source :=
  embedUnary (.inl (.inl (.inr ())))

def embedClockMarker {Source : Type} : PreparedSymbol Source :=
  embedUnary (.inl (.inr ()))

def embedFreshMarker {Source : Type} : PreparedSymbol Source :=
  embedUnary (.inr ())

def embedSpaceBit {Source : Type}
    (symbol : PartrecToTM2.Γ') : PreparedSymbol Source :=
  .inl (.inl (.inr symbol))

def embedClockBit {Source : Type}
    (symbol : PartrecToTM2.Γ') : PreparedSymbol Source :=
  .inl (.inr symbol)

def embedFreshBit {Source : Type}
    (symbol : PartrecToTM2.Γ') : PreparedSymbol Source :=
  .inr symbol

/-- The intended seven-block prepared word, with all sum embeddings hidden
behind descriptive names. -/
def layout (symbols : List encoding.Γ) (space clockBits fresh : Nat) :
    List (Symbol encoding) :=
  symbols.map (fun symbol => embedSource (some symbol)) ++
    List.replicate space embedSpaceMarker ++
    List.replicate clockBits embedClockMarker ++
    List.replicate fresh embedFreshMarker ++
    (PartrecToTM2.trNat space).map embedSpaceBit ++
    (PartrecToTM2.trNat clockBits).map embedClockBit ++
    (PartrecToTM2.trNat fresh).map embedFreshBit

@[simp]
theorem selectedCount_isClockAfterSpace_spaceBinarySources
    (symbols : List encoding.Γ) :
    BinaryCountPaddingMachine.selectedCount isClockAfterSpace
      (spaceBinarySources decider symbols) =
        PolySpaceCompiler.clockBitsOfSymbols decider symbols := by
  unfold spaceBinarySources BinaryCountPaddingMachine.paddedOutput
  rw [PolySpaceRequestPadding.binarySelectedCount_append]
  have retained :
      BinaryCountPaddingMachine.selectedCount isClockAfterSpace
          ((freshPaddedSources decider symbols).map Sum.inl) =
        BinaryCountPaddingMachine.selectedCount isClockMarker
          (freshPaddedSources decider symbols) := by
    induction freshPaddedSources decider symbols with
    | nil => rfl
    | cons symbol rest induction =>
        simp [BinaryCountPaddingMachine.selectedCount,
          isClockAfterSpace, induction]
  have counterZero :
      BinaryCountPaddingMachine.selectedCount isClockAfterSpace
          ((PartrecToTM2.trNat
            (BinaryCountPaddingMachine.selectedCount isSpaceMarker
              (freshPaddedSources decider symbols))).map
                (fun bit =>
                  (Sum.inr bit :
                    SpaceBinarySymbol (Option encoding.Γ)))) = 0 := by
    apply PolySpaceRequestPadding.binarySelectedCount_eq_zero_of
    intro symbol membership
    obtain ⟨bit, _, rfl⟩ := List.mem_map.mp membership
    rfl
  rw [retained, counterZero, Nat.add_zero]
  exact (count_eq_of_layout decider symbols).2.1

@[simp]
theorem selectedCount_isFreshAfterSpace_spaceBinarySources
    (symbols : List encoding.Γ) :
    BinaryCountPaddingMachine.selectedCount isFreshAfterSpace
      (spaceBinarySources decider symbols) =
        BoundedMachineAtom.atomCount (tm := decider.tm)
          (space := PolySpaceCompiler.spaceOfSymbols decider symbols)
          (clockBits :=
            PolySpaceCompiler.clockBitsOfSymbols decider symbols) := by
  unfold spaceBinarySources BinaryCountPaddingMachine.paddedOutput
  rw [PolySpaceRequestPadding.binarySelectedCount_append]
  have retained :
      BinaryCountPaddingMachine.selectedCount isFreshAfterSpace
          ((freshPaddedSources decider symbols).map Sum.inl) =
        BinaryCountPaddingMachine.selectedCount isFreshMarker
          (freshPaddedSources decider symbols) := by
    induction freshPaddedSources decider symbols with
    | nil => rfl
    | cons symbol rest induction =>
        simp [BinaryCountPaddingMachine.selectedCount,
          isFreshAfterSpace, induction]
  have counterZero :
      BinaryCountPaddingMachine.selectedCount isFreshAfterSpace
          ((PartrecToTM2.trNat
            (BinaryCountPaddingMachine.selectedCount isSpaceMarker
              (freshPaddedSources decider symbols))).map
                (fun bit =>
                  (Sum.inr bit :
                    SpaceBinarySymbol (Option encoding.Γ)))) = 0 := by
    apply PolySpaceRequestPadding.binarySelectedCount_eq_zero_of
    intro symbol membership
    obtain ⟨bit, _, rfl⟩ := List.mem_map.mp membership
    rfl
  rw [retained, counterZero, Nat.add_zero]
  exact (count_eq_of_layout decider symbols).2.2

@[simp]
theorem selectedCount_isFreshAfterWidths_widthsBinarySources
    (symbols : List encoding.Γ) :
    BinaryCountPaddingMachine.selectedCount isFreshAfterWidths
      (widthsBinarySources decider symbols) =
        BoundedMachineAtom.atomCount (tm := decider.tm)
          (space := PolySpaceCompiler.spaceOfSymbols decider symbols)
          (clockBits :=
            PolySpaceCompiler.clockBitsOfSymbols decider symbols) := by
  unfold widthsBinarySources BinaryCountPaddingMachine.paddedOutput
  rw [PolySpaceRequestPadding.binarySelectedCount_append]
  have retained :
      BinaryCountPaddingMachine.selectedCount isFreshAfterWidths
          ((spaceBinarySources decider symbols).map Sum.inl) =
        BinaryCountPaddingMachine.selectedCount isFreshAfterSpace
          (spaceBinarySources decider symbols) := by
    induction spaceBinarySources decider symbols with
    | nil => rfl
    | cons symbol rest induction =>
        simp [BinaryCountPaddingMachine.selectedCount,
          isFreshAfterWidths, induction]
  have counterZero :
      BinaryCountPaddingMachine.selectedCount isFreshAfterWidths
          ((PartrecToTM2.trNat
            (BinaryCountPaddingMachine.selectedCount isClockAfterSpace
              (spaceBinarySources decider symbols))).map
                (fun bit =>
                  (Sum.inr bit :
                    WidthsBinarySymbol (Option encoding.Γ)))) = 0 := by
    apply PolySpaceRequestPadding.binarySelectedCount_eq_zero_of
    intro symbol membership
    obtain ⟨bit, _, rfl⟩ := List.mem_map.mp membership
    rfl
  rw [retained, counterZero, Nat.add_zero]
  exact selectedCount_isFreshAfterSpace_spaceBinarySources decider symbols

/-- Exact complete output of direct source preparation. -/
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
  rw [BinaryCountPaddingMachine.paddedOutput,
    selectedCount_isFreshAfterWidths_widthsBinarySources]
  unfold widthsBinarySources
  rw [BinaryCountPaddingMachine.paddedOutput,
    selectedCount_isClockAfterSpace_spaceBinarySources]
  unfold spaceBinarySources
  rw [BinaryCountPaddingMachine.paddedOutput]
  rw [(count_eq_of_layout decider symbols).1,
    freshPaddedSources_eq]
  simp only [List.map_append, List.map_map]
  simp [layout, optionSources, embedSource, embedSpaceMarker,
    embedClockMarker, embedFreshMarker, embedUnary, Function.comp_def,
    List.append_assoc]
  rfl

def sourceSymbol : Symbol encoding → Option encoding.Γ
  | .inl (.inl (.inl (.inl (.inl (.inl (some symbol)))))) =>
      some symbol
  | _ => none

def sourceSymbols (word : List (Symbol encoding)) : List encoding.Γ :=
  word.filterMap sourceSymbol

def spaceBit : Symbol encoding → Option PartrecToTM2.Γ'
  | .inl (.inl (.inr symbol)) => some symbol
  | _ => none

def clockBit : Symbol encoding → Option PartrecToTM2.Γ'
  | .inl (.inr symbol) => some symbol
  | _ => none

def freshBit : Symbol encoding → Option PartrecToTM2.Γ'
  | .inr symbol => some symbol
  | _ => none

def spaceBits (word : List (Symbol encoding)) : List PartrecToTM2.Γ' :=
  word.filterMap spaceBit

def clockBits (word : List (Symbol encoding)) : List PartrecToTM2.Γ' :=
  word.filterMap clockBit

def freshBits (word : List (Symbol encoding)) : List PartrecToTM2.Γ' :=
  word.filterMap freshBit

def isSpaceUnary : Symbol encoding → Bool
  | .inl (.inl (.inl (.inl (.inl (.inr _))))) => true
  | _ => false

def isClockUnary : Symbol encoding → Bool
  | .inl (.inl (.inl (.inl (.inr _)))) => true
  | _ => false

def isFreshUnary : Symbol encoding → Bool
  | .inl (.inl (.inl (.inr _))) => true
  | _ => false

def space (word : List (Symbol encoding)) : Nat :=
  BinaryCountPaddingMachine.selectedCount isSpaceUnary word

def clockWidth (word : List (Symbol encoding)) : Nat :=
  BinaryCountPaddingMachine.selectedCount isClockUnary word

def fresh (word : List (Symbol encoding)) : Nat :=
  BinaryCountPaddingMachine.selectedCount isFreshUnary word

theorem filterMap_append {Source Target : Type}
    (project : Source → Option Target) (first second : List Source) :
    (first ++ second).filterMap project =
      first.filterMap project ++ second.filterMap project := by
  induction first with
  | nil => rfl
  | cons source first induction =>
      cases choice : project source <;> simp [choice, induction]

theorem selectedCount_append {Source : Type} (selected : Source → Bool)
    (first second : List Source) :
    BinaryCountPaddingMachine.selectedCount selected (first ++ second) =
      BinaryCountPaddingMachine.selectedCount selected first +
        BinaryCountPaddingMachine.selectedCount selected second :=
  PolySpaceRequestPadding.binarySelectedCount_append selected first second

@[simp]
theorem sourceSymbols_layout (symbols : List encoding.Γ)
    (space clockBits fresh : Nat) :
    sourceSymbols (layout symbols space clockBits fresh) = symbols := by
  simp [sourceSymbols, layout, sourceSymbol,
    embedSource, embedSpaceMarker, embedClockMarker, embedFreshMarker,
    embedSpaceBit, embedClockBit, embedFreshBit, embedUnary]

@[simp]
theorem space_layout (symbols : List encoding.Γ)
    (spaceValue clockBitsValue freshValue : Nat) :
    space (layout symbols spaceValue clockBitsValue freshValue) =
      spaceValue := by
  simp [space, layout, selectedCount_append, isSpaceUnary,
    embedSource, embedSpaceMarker, embedClockMarker, embedFreshMarker,
    embedSpaceBit, embedClockBit, embedFreshBit, embedUnary,
    PolySpaceRequestPadding.binarySelectedCount_replicate_true,
    PolySpaceRequestPadding.binarySelectedCount_eq_zero_of]

@[simp]
theorem clockWidth_layout (symbols : List encoding.Γ)
    (spaceValue clockBitsValue freshValue : Nat) :
    clockWidth (layout symbols spaceValue clockBitsValue freshValue) =
      clockBitsValue := by
  simp [clockWidth, layout, selectedCount_append, isClockUnary,
    embedSource, embedSpaceMarker, embedClockMarker, embedFreshMarker,
    embedSpaceBit, embedClockBit, embedFreshBit, embedUnary,
    PolySpaceRequestPadding.binarySelectedCount_replicate_true,
    PolySpaceRequestPadding.binarySelectedCount_eq_zero_of]

@[simp]
theorem fresh_layout (symbols : List encoding.Γ)
    (spaceValue clockBitsValue freshValue : Nat) :
    fresh (layout symbols spaceValue clockBitsValue freshValue) =
      freshValue := by
  simp [fresh, layout, selectedCount_append, isFreshUnary,
    embedSource, embedSpaceMarker, embedClockMarker, embedFreshMarker,
    embedSpaceBit, embedClockBit, embedFreshBit, embedUnary,
    PolySpaceRequestPadding.binarySelectedCount_replicate_true,
    PolySpaceRequestPadding.binarySelectedCount_eq_zero_of]

@[simp]
theorem spaceBits_layout (symbols : List encoding.Γ)
    (spaceValue clockBitsValue freshValue : Nat) :
    spaceBits (layout symbols spaceValue clockBitsValue freshValue) =
      PartrecToTM2.trNat spaceValue := by
  simp [spaceBits, layout, spaceBit,
    embedSource, embedSpaceMarker, embedClockMarker, embedFreshMarker,
    embedSpaceBit, embedClockBit, embedFreshBit, embedUnary]

@[simp]
theorem clockBits_layout (symbols : List encoding.Γ)
    (spaceValue clockBitsValue freshValue : Nat) :
    clockBits (layout symbols spaceValue clockBitsValue freshValue) =
      PartrecToTM2.trNat clockBitsValue := by
  simp [clockBits, layout, clockBit,
    embedSource, embedSpaceMarker, embedClockMarker, embedFreshMarker,
    embedSpaceBit, embedClockBit, embedFreshBit, embedUnary]

@[simp]
theorem freshBits_layout (symbols : List encoding.Γ)
    (spaceValue clockBitsValue freshValue : Nat) :
    freshBits (layout symbols spaceValue clockBitsValue freshValue) =
      PartrecToTM2.trNat freshValue := by
  simp [freshBits, layout, freshBit,
    embedSource, embedSpaceMarker, embedClockMarker, embedFreshMarker,
    embedSpaceBit, embedClockBit, embedFreshBit, embedUnary]

/-- Semantic token request read from an arbitrary prepared word.  On the
verified layout, the future machine may use the redundant tagged unary and
binary blocks to implement this function. -/
def tokenRequest (word : List (Symbol encoding)) : List ProgramTokens.Token :=
  ProgramTokens.requestSource (fresh word)
    (PolySpaceProgramSpec.program decider (sourceSymbols word))

/-- The prepared-word token specification is exactly the normalized source
request on every genuine preprocessor output. -/
@[simp]
theorem tokenRequest_preparedSources (symbols : List encoding.Γ) :
    tokenRequest decider (preparedSources decider symbols) =
      ProgramTokens.requestSource (PolySpaceProgramSpec.fresh decider symbols)
        (PolySpaceProgramSpec.program decider symbols) := by
  rw [preparedSources_eq_layout]
  simp [tokenRequest, PolySpaceProgramSpec.fresh]

end PolySpacePreparedLayout
end PeriodicCNF
end LeanTrominoes
