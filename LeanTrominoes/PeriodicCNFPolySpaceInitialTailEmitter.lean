/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFPolySpaceInitialTailTemplates
import LeanTrominoes.PeriodicCNFBivariateTemplateEmitterTime

/-!
# Polynomial-time initial input-stack tail emission

Specialize the verified bivariate emitter to the source-count/tail-position
template.  The mixed workspace count proof shows that prepared source symbols
and unary tail markers feed the two counters independently while all earlier
and newly emitted tokens are ignored.
-/

noncomputable section

namespace LeanTrominoes

open Computability Turing

namespace PeriodicCNF
namespace PolySpaceInitialTailEmitter

open AffineEmitterPipeline
open UnaryProgramTokens

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

noncomputable local instance (stack : decider.tm.K) :
    Fintype (decider.tm.Γ stack) := decider.stackAlphabetFinite stack

abbrev Symbol := PolySpaceInitialSourceEmitter.Symbol
  (encoding := encoding)
abbrev InputWorkspace := PolySpaceInitialSourceEmitter.InputWorkspace
  (encoding := encoding)
abbrev Data := PolySpaceInitialSourceEmitter.Data (encoding := encoding)
abbrev Workspace := PolySpaceInitialSourceEmitter.Workspace
  (encoding := encoding)

def runWorkspace (workspace : List (Workspace (encoding := encoding))) :
    List (Workspace (encoding := encoding)) :=
  BivariateTemplateEmitterMachine.appendedOutput
    (PolySpaceInitialTailTemplates.sourceSelected (encoding := encoding))
    (PolySpaceInitialTailTemplates.tailSelected (encoding := encoding))
    (PolySpaceInitialTailTemplates.inputTailProgram decider).recipes []
    workspace

/-- Initial-tail emission itself is one fixed bivariate polynomial-time pass. -/
noncomputable def runWorkspaceComputableInPolyTime :
    @TM2ComputableInPolyTime
      (List (Workspace (encoding := encoding)))
      (List (Workspace (encoding := encoding)))
      (Workspace (encoding := encoding))
      (Workspace (encoding := encoding)) id id
      (runWorkspace decider) :=
  BivariateTemplateEmitterMachine.computableInPolyTime
    (PolySpaceInitialTailTemplates.sourceSelected (encoding := encoding))
    (PolySpaceInitialTailTemplates.tailSelected (encoding := encoding))
    (PolySpaceInitialTailTemplates.inputTailProgram decider).recipes []

theorem selectedCount_append (selected : Data (encoding := encoding) → Bool)
    (first second : List (Workspace (encoding := encoding))) :
    BivariateTemplateEmitterMachine.selectedCount selected (first ++ second) =
      BivariateTemplateEmitterMachine.selectedCount selected first +
        BivariateTemplateEmitterMachine.selectedCount selected second := by
  unfold BivariateTemplateEmitterMachine.selectedCount
  exact AffineEmitterPipeline.unarySelectedCount_append
    (BivariateTemplateEmitterMachine.dataSelected selected) first second

@[simp]
theorem selectedCount_map_tokens
    (selected : Data (encoding := encoding) → Bool) (tokens : List Token) :
    BivariateTemplateEmitterMachine.selectedCount selected
        (tokens.map fun token =>
          (Sum.inr token : Workspace (encoding := encoding))) = 0 := by
  unfold BivariateTemplateEmitterMachine.selectedCount
  induction tokens with
  | nil => rfl
  | cons token tokens induction =>
      simp [BivariateTemplateEmitterMachine.dataSelected, induction]

theorem selectedCount_map_of_false {Source : Type}
    (selected : Data (encoding := encoding) → Bool)
    (embed : Source → Workspace (encoding := encoding))
    (unselected : ∀ source, BivariateTemplateEmitterMachine.dataSelected
      selected (embed source) = false) (source : List Source) :
    BivariateTemplateEmitterMachine.selectedCount selected
      (source.map embed) = 0 := by
  unfold BivariateTemplateEmitterMachine.selectedCount
  induction source with
  | nil => rfl
  | cons item source induction =>
      simp [unselected, induction]

theorem selectedCount_map_of_true {Source : Type}
    (selected : Data (encoding := encoding) → Bool)
    (embed : Source → Workspace (encoding := encoding))
    (selectedEmbed : ∀ source, BivariateTemplateEmitterMachine.dataSelected
      selected (embed source) = true) (source : List Source) :
    BivariateTemplateEmitterMachine.selectedCount selected
      (source.map embed) = source.length := by
  unfold BivariateTemplateEmitterMachine.selectedCount
  exact PolySpaceSourcePreparation.selectedCount_map_of_true
    (BivariateTemplateEmitterMachine.dataSelected selected) embed
      selectedEmbed source

@[simp]
theorem selectedCount_source_prepared (symbols : List encoding.Γ) :
    BivariateTemplateEmitterMachine.selectedCount
        (PolySpaceInitialTailTemplates.sourceSelected (encoding := encoding))
        ((PolySpaceUnaryPreparedLayout.preparedSources decider symbols).map
          (fun symbol =>
            (Sum.inl (Sum.inl symbol) : Workspace (encoding := encoding)))) =
      symbols.length := by
  unfold BivariateTemplateEmitterMachine.selectedCount
  have mapped :
      UnaryPolynomialPaddingMachine.selectedCount
          (BivariateTemplateEmitterMachine.dataSelected
            (PolySpaceInitialTailTemplates.sourceSelected
              (encoding := encoding)))
          ((PolySpaceUnaryPreparedLayout.preparedSources decider symbols).map
            (fun symbol =>
              (Sum.inl (Sum.inl symbol) : Workspace
                (encoding := encoding)))) =
        UnaryPolynomialPaddingMachine.selectedCount
          (PolySpaceInitialTailPadding.isSource (encoding := encoding))
          (PolySpaceUnaryPreparedLayout.preparedSources decider symbols) := by
    induction PolySpaceUnaryPreparedLayout.preparedSources decider symbols with
    | nil => rfl
    | cons symbol symbols induction =>
        simp [UnaryPolynomialPaddingMachine.selectedCount,
          BivariateTemplateEmitterMachine.dataSelected,
          PolySpaceInitialTailTemplates.sourceSelected, induction]
  rw [mapped]
  exact PolySpaceInitialTailPadding.selectedCount_isSource_preparedSources
    decider symbols

@[simp]
theorem selectedCount_tail_prepared (symbols : List encoding.Γ) :
    BivariateTemplateEmitterMachine.selectedCount
        (PolySpaceInitialTailTemplates.tailSelected (encoding := encoding))
        ((PolySpaceUnaryPreparedLayout.preparedSources decider symbols).map
          (fun symbol =>
            (Sum.inl (Sum.inl symbol) : Workspace (encoding := encoding)))) =
      0 := by
  exact selectedCount_map_of_false (encoding := encoding)
    _ _ (fun _ => rfl) _

@[simp]
theorem selectedCount_source_tailMarkers (count : Nat) :
    BivariateTemplateEmitterMachine.selectedCount
        (PolySpaceInitialTailTemplates.sourceSelected (encoding := encoding))
        ((List.replicate count ()).map fun marker =>
          (Sum.inl (Sum.inr marker) : Workspace (encoding := encoding))) =
      0 := by
  exact selectedCount_map_of_false (encoding := encoding)
    _ _ (fun _ => rfl) _

@[simp]
theorem selectedCount_tail_tailMarkers (count : Nat) :
    BivariateTemplateEmitterMachine.selectedCount
        (PolySpaceInitialTailTemplates.tailSelected (encoding := encoding))
        ((List.replicate count ()).map fun marker =>
          (Sum.inl (Sum.inr marker) : Workspace (encoding := encoding))) =
      count := by
  simpa using selectedCount_map_of_true (encoding := encoding)
    (PolySpaceInitialTailTemplates.tailSelected (encoding := encoding))
    (fun marker : Unit =>
      (Sum.inl (Sum.inr marker) : Workspace (encoding := encoding)))
    (fun _ => rfl) (List.replicate count ())

@[simp]
theorem selectedCount_source_afterSource (symbols : List encoding.Γ)
    (tokens : List Token) :
    BivariateTemplateEmitterMachine.selectedCount
        (PolySpaceInitialTailTemplates.sourceSelected (encoding := encoding))
        (PolySpaceInitialSourceEmitter.runWorkspace decider
          (embedData
              (PolySpaceUnaryPreparedLayout.preparedSources decider symbols) ++
            tokens.map fun token =>
              (Sum.inr token : InputWorkspace (encoding := encoding)))) =
      symbols.length := by
  rw [PolySpaceInitialSourceEmitter.runWorkspace_embed_append_tokens]
  simp only [selectedCount_append]
  rw [selectedCount_source_prepared, selectedCount_map_tokens,
    selectedCount_source_tailMarkers, selectedCount_map_tokens]
  simp

@[simp]
theorem selectedCount_tail_afterSource (symbols : List encoding.Γ)
    (tokens : List Token) :
    BivariateTemplateEmitterMachine.selectedCount
        (PolySpaceInitialTailTemplates.tailSelected (encoding := encoding))
        (PolySpaceInitialSourceEmitter.runWorkspace decider
          (embedData
              (PolySpaceUnaryPreparedLayout.preparedSources decider symbols) ++
            tokens.map fun token =>
              (Sum.inr token : InputWorkspace (encoding := encoding)))) =
      PolySpaceInitialTailPadding.tailCount decider symbols := by
  rw [PolySpaceInitialSourceEmitter.runWorkspace_embed_append_tokens]
  simp only [selectedCount_append]
  rw [selectedCount_tail_prepared, selectedCount_map_tokens,
    selectedCount_tail_tailMarkers, selectedCount_map_tokens]
  simp

/-- Exact tail suffix after the already verified padded source-emission pass. -/
theorem runWorkspace_afterSource (symbols : List encoding.Γ)
    (tokens : List Token) :
    runWorkspace decider
        (PolySpaceInitialSourceEmitter.runWorkspace decider
          (embedData
              (PolySpaceUnaryPreparedLayout.preparedSources decider symbols) ++
            tokens.map fun token =>
              (Sum.inr token : InputWorkspace (encoding := encoding)))) =
      PolySpaceInitialSourceEmitter.runWorkspace decider
          (embedData
              (PolySpaceUnaryPreparedLayout.preparedSources decider symbols) ++
            tokens.map fun token =>
              (Sum.inr token : InputWorkspace (encoding := encoding))) ++
        (PolySpaceInitialEmitter.emptyTailTokens decider decider.tm.k₀
          symbols.length
          (PolySpaceInitialTailPadding.tailCount decider symbols)).map
            (fun token =>
              (Sum.inr token : Workspace (encoding := encoding))) := by
  unfold runWorkspace BivariateTemplateEmitterMachine.appendedOutput
  rw [selectedCount_source_afterSource, selectedCount_tail_afterSource,
    PolySpaceInitialTailTemplates.positionRangeTokens_zero_eq]
  simp

/-- Compose padding/source emission and input-tail emission from the original
shared prepared-data/token workspace. -/
def runFromInput (workspace : List (InputWorkspace (encoding := encoding))) :
    List (Workspace (encoding := encoding)) :=
  runWorkspace decider
    (PolySpaceInitialSourceEmitter.runWorkspace decider workspace)

noncomputable def runFromInputComputableInPolyTime :
    @TM2ComputableInPolyTime
      (List (InputWorkspace (encoding := encoding)))
      (List (Workspace (encoding := encoding)))
      (InputWorkspace (encoding := encoding))
      (Workspace (encoding := encoding)) id id
      (runFromInput decider) := by
  let complete := TM2CompositionMachine.computableInPolyTime
    (PolySpaceInitialSourceEmitter.runWorkspaceComputableInPolyTime decider)
    (runWorkspaceComputableInPolyTime decider)
  change @TM2ComputableInPolyTime
    (List (InputWorkspace (encoding := encoding)))
    (List (Workspace (encoding := encoding)))
    (InputWorkspace (encoding := encoding))
    (Workspace (encoding := encoding)) id id
    (fun workspace => runWorkspace decider
      (PolySpaceInitialSourceEmitter.runWorkspace decider workspace))
  exact complete

end PolySpaceInitialTailEmitter
end PeriodicCNF
end LeanTrominoes
