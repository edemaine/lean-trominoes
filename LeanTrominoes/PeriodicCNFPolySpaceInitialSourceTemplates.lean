/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFIndexedTemplateEmitterSpec

/-!
# Indexed source-cell templates for the initial configuration

Each original finite source symbol selects the affine recipe for the
corresponding decoded input-stack cell.  Its selected position is exactly its
source-list index.  Prepared unary markers, earlier emitted tokens, and the
new initial-tail markers are all ignored.
-/

noncomputable section

namespace LeanTrominoes

open Turing

namespace PeriodicCNF
namespace PolySpaceInitialSourceTemplates

open AffineProgramTemplates
open AffineTemplateEmitterMachine
open IndexedTemplateEmitter
open UnaryProgramTokens

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

noncomputable local instance (stack : decider.tm.K) :
    Fintype (decider.tm.Γ stack) := decider.stackAlphabetFinite stack

abbrev Symbol := PolySpaceUnaryPreparedLayout.Symbol encoding
abbrev Workspace := PolySpaceInitialTailPadding.Workspace
  (encoding := encoding)
abbrev TailWorkspace := PolySpaceInitialTailPadding.TailWorkspace
  (encoding := encoding)

def sourceSymbol : TailWorkspace (encoding := encoding) → Option encoding.Γ
  | .inl (.inl symbol) => PolySpaceUnaryPreparedLayout.sourceSymbol symbol
  | _ => none

def sourceProgram (symbol : encoding.Γ) : AffineProgramTemplates.Program :=
  BoundedMachineAffineProgram.nextStackCellIs
    (tm := decider.tm) decider.tm.k₀ 0
    (some (decider.inputAlphabet.invFun symbol))

/-- Data-indexed affine family consumed by the generic source-position
emitter. -/
def family : IndexedTemplateEmitter.Family
    (TailWorkspace (encoding := encoding)) := fun data =>
  (sourceSymbol (encoding := encoding) data).map fun symbol =>
    (sourceProgram decider symbol).recipes

def sourceData (symbol : encoding.Γ) :
    TailWorkspace (encoding := encoding) :=
  .inl (.inl (PolySpaceUnaryPreparedLayout.embedSource symbol))

@[simp]
theorem family_sourceData (symbol : encoding.Γ) :
    family decider (sourceData (encoding := encoding) symbol) =
      some (sourceProgram decider symbol).recipes := by
  rfl

/-- Recursive token word for source cells beginning at an arbitrary position. -/
def sourceTokensAux : Nat → List encoding.Γ → List Token
  | _, [] => []
  | position, symbol :: symbols =>
      ofProgram
          (BoundedMachineFixedConfigurationEmitter.stackCellIs
            (tm := decider.tm) .next decider.tm.k₀ position
            (some (decider.inputAlphabet.invFun symbol))) ++
        sourceTokensAux (position + 1) symbols

theorem emittedAux_sourceData (position : Nat)
    (symbols : List encoding.Γ) :
    emittedAux (family decider) position
        (symbols.map (sourceData (encoding := encoding))) =
      sourceTokensAux decider position symbols := by
  induction symbols generalizing position with
  | nil => rfl
  | cons symbol symbols induction =>
      rw [List.map_cons,
        emittedAux_cons_some (family decider) position _ _
          (sourceProgram decider symbol).recipes (family_sourceData decider symbol)]
      rw [AffineProgramTemplates.Program.positionTokens_recipes]
      unfold sourceProgram
      rw [
        BoundedMachineAffineProgram.evaluate_nextStackCellIs]
      simp only [Nat.add_zero, sourceTokensAux]
      rw [induction]
      rfl

theorem sourceTokensAux_eq_range (position : Nat)
    (symbols : List encoding.Γ) :
    sourceTokensAux decider position symbols =
      (List.range symbols.length).flatMap fun offset =>
        ofProgram
          (BoundedMachineFixedConfigurationEmitter.stackCellIs
            (tm := decider.tm) .next decider.tm.k₀
            (position + offset)
            (symbols[offset]?.map decider.inputAlphabet.invFun)) := by
  induction symbols generalizing position with
  | nil => rfl
  | cons symbol symbols induction =>
      rw [sourceTokensAux, List.length_cons, List.range_succ_eq_map,
        List.flatMap_cons, List.flatMap_map]
      simp only [Nat.add_zero, List.getElem?_cons_zero, Option.map_some]
      rw [induction]
      congr 1
      apply List.flatMap_congr
      intro offset membership
      simp only [List.getElem?_cons_succ]
      have positionEq : position + 1 + offset =
          position + (offset + 1) := by omega
      rw [positionEq]

@[simp]
theorem sourceTokensAux_zero_eq (symbols : List encoding.Γ) :
    sourceTokensAux decider 0 symbols =
      PolySpaceInitialEmitter.sourcePrefixTokens decider symbols := by
  rw [sourceTokensAux_eq_range]
  unfold PolySpaceInitialEmitter.sourcePrefixTokens
  simp

/-- All nonsource data retained after the initial source prefix. -/
def ignoredSuffix (symbols : List encoding.Γ) (tokens : List Token) :
    List (TailWorkspace (encoding := encoding)) :=
  (List.replicate (PolySpaceCompiler.spaceOfSymbols decider symbols)
      PolySpaceUnaryPreparedLayout.embedSpace).map
      (fun symbol =>
        (Sum.inl (Sum.inl symbol) : TailWorkspace (encoding := encoding))) ++
    (List.replicate (PolySpaceCompiler.clockBitsOfSymbols decider symbols)
      PolySpaceUnaryPreparedLayout.embedClock).map
      (fun symbol =>
        (Sum.inl (Sum.inl symbol) : TailWorkspace (encoding := encoding))) ++
    (List.replicate (PolySpaceProgramSpec.fresh decider symbols)
      PolySpaceUnaryPreparedLayout.embedFresh).map
      (fun symbol =>
        (Sum.inl (Sum.inl symbol) : TailWorkspace (encoding := encoding))) ++
    tokens.map (fun token =>
      (Sum.inl (Sum.inr token) : TailWorkspace (encoding := encoding))) ++
    List.replicate (PolySpaceInitialTailPadding.tailCount decider symbols)
      (Sum.inr ())

theorem paddedWorkspace_eq_source_append_ignored
    (symbols : List encoding.Γ) (tokens : List Token) :
    PolySpaceInitialTailPadding.paddedWorkspace decider
        (AffineEmitterPipeline.embedData
            (PolySpaceUnaryPreparedLayout.preparedSources decider symbols) ++
          tokens.map fun token =>
            (Sum.inr token : Workspace (encoding := encoding))) =
      symbols.map (sourceData (encoding := encoding)) ++
        ignoredSuffix decider symbols tokens := by
  rw [PolySpaceInitialTailPadding.paddedWorkspace_embed_append_tokens,
    PolySpaceUnaryPreparedLayout.preparedSources_eq_layout]
  unfold PolySpaceUnaryPreparedLayout.layout ignoredSuffix
  simp [AffineEmitterPipeline.embedData, List.map_append,
    List.map_map, Function.comp_def, sourceData, List.append_assoc,
    PolySpaceProgramSpec.fresh]

theorem family_none_ignoredSuffix (symbols : List encoding.Γ)
    (tokens : List Token) (data : TailWorkspace (encoding := encoding))
    (membership : data ∈ ignoredSuffix decider symbols tokens) :
    family decider data = none := by
  unfold ignoredSuffix at membership
  simp only [List.mem_append] at membership
  rcases membership with prior | tail
  · rcases prior with earlier | token
    · rcases earlier with firstTwo | fresh
      · rcases firstTwo with space | clock
        · obtain ⟨marker, markerMem, rfl⟩ := List.mem_map.mp space
          have markerEq := List.eq_of_mem_replicate markerMem
          subst marker
          rfl
        · obtain ⟨marker, markerMem, rfl⟩ := List.mem_map.mp clock
          have markerEq := List.eq_of_mem_replicate markerMem
          subst marker
          rfl
      · obtain ⟨marker, markerMem, rfl⟩ := List.mem_map.mp fresh
        have markerEq := List.eq_of_mem_replicate markerMem
        subst marker
        rfl
    · obtain ⟨_, _, rfl⟩ := List.mem_map.mp token
      rfl
  · have dataEq := List.eq_of_mem_replicate tail
    subst data
    rfl

/-- Exact indexed-family output on the tail-padded prepared workspace. -/
theorem emitted_paddedWorkspace (symbols : List encoding.Γ)
    (tokens : List Token) :
    emitted (family decider)
        (PolySpaceInitialTailPadding.paddedWorkspace decider
          (AffineEmitterPipeline.embedData
              (PolySpaceUnaryPreparedLayout.preparedSources decider symbols) ++
            tokens.map fun token =>
              (Sum.inr token : Workspace (encoding := encoding)))) =
      PolySpaceInitialEmitter.sourcePrefixTokens decider symbols := by
  unfold emitted
  rw [paddedWorkspace_eq_source_append_ignored]
  rw [emittedAux_append_none]
  · rw [emittedAux_sourceData, sourceTokensAux_zero_eq]
  · exact family_none_ignoredSuffix decider symbols tokens

end PolySpaceInitialSourceTemplates
end PeriodicCNF
end LeanTrominoes
