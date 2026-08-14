/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFIndexedTemplateEmitterTime
import LeanTrominoes.PeriodicCNFPolySpaceInitialSourceTemplates
import LeanTrominoes.TM2CompositionMachine

/-!
# Polynomial-time source-prefix emission for the initial configuration

Compose polynomial tail padding with the indexed source-cell emitter.  A final
finite block map flattens the two nested workspace layers: existing program
tokens remain tokens, original prepared symbols and new tail markers remain
selectable data, and the source-dependent cell tests form the new token suffix.
-/

noncomputable section

namespace LeanTrominoes

open Computability Turing

namespace PeriodicCNF
namespace PolySpaceInitialSourceEmitter

open AffineEmitterPipeline
open IndexedTemplateEmitterMachine
open UnaryProgramTokens

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

noncomputable local instance (stack : decider.tm.K) :
    Fintype (decider.tm.Γ stack) := decider.stackAlphabetFinite stack

abbrev Symbol := PolySpaceUnaryPreparedLayout.Symbol encoding
abbrev InputWorkspace := PolySpaceInitialTailPadding.Workspace
  (encoding := encoding)
abbrev TailWorkspace := PolySpaceInitialTailPadding.TailWorkspace
  (encoding := encoding)
abbrev Data := Symbol (encoding := encoding) ⊕ Unit
abbrev Workspace := AffineEmitterPipeline.Workspace
  (Data (encoding := encoding))
abbrev NestedWorkspace := TailWorkspace (encoding := encoding) ⊕ Token

/-- Flatten one retained padded datum or emitted token into the stable workspace
used by the remaining initial-configuration phases. -/
def flattenItem : NestedWorkspace (encoding := encoding) →
    Workspace (encoding := encoding)
  | .inl (.inl (.inl symbol)) => .inl (.inl symbol)
  | .inl (.inl (.inr token)) => .inr token
  | .inl (.inr marker) => .inl (.inr marker)
  | .inr token => .inr token

def flatten (workspace : List (NestedWorkspace (encoding := encoding))) :
    List (Workspace (encoding := encoding)) :=
  workspace.map (flattenItem (encoding := encoding))

/-- Pad the retained workspace, emit every decoded source cell at its indexed
position, and flatten the nested token alphabet. -/
def runWorkspace (workspace : List (InputWorkspace (encoding := encoding))) :
    List (Workspace (encoding := encoding)) :=
  flatten
    (IndexedTemplateEmitterMachine.appendedOutput
      (PolySpaceInitialSourceTemplates.family decider)
      (PolySpaceInitialTailPadding.paddedWorkspace decider workspace))

noncomputable def flattenComputableInPolyTime :
    @TM2ComputableInPolyTime
      (List (NestedWorkspace (encoding := encoding)))
      (List (Workspace (encoding := encoding)))
      (NestedWorkspace (encoding := encoding))
      (Workspace (encoding := encoding)) id id
      (flatten (encoding := encoding)) := by
  let certificate := FiniteBlockTransducer.computableInPolyTime
    (fun item : NestedWorkspace (encoding := encoding) =>
      [flattenItem (encoding := encoding) item])
  refine
    { tm := certificate.tm
      inputAlphabet := certificate.inputAlphabet
      outputAlphabet := certificate.outputAlphabet
      time := certificate.time
      outputsFun := ?_ }
  intro workspace
  have run := certificate.outputsFun workspace
  have outputEq : workspace.flatMap
        (fun item => [flattenItem (encoding := encoding) item]) =
      flatten (encoding := encoding) workspace := by
    rw [AffineEmitterPipeline.flatMap_singleton_eq_map]
    rfl
  rw [outputEq] at run
  exact run

/-- The complete padding/source-emission/flattening pass is polynomial time. -/
noncomputable def runWorkspaceComputableInPolyTime :
    @TM2ComputableInPolyTime
      (List (InputWorkspace (encoding := encoding)))
      (List (Workspace (encoding := encoding)))
      (InputWorkspace (encoding := encoding))
      (Workspace (encoding := encoding)) id id
      (runWorkspace decider) := by
  let paddedAndEmitted := TM2CompositionMachine.computableInPolyTime
    (PolySpaceInitialTailPadding.computableInPolyTime decider)
    (IndexedTemplateEmitterMachine.computableInPolyTime
      (PolySpaceInitialSourceTemplates.family decider))
  let complete := TM2CompositionMachine.computableInPolyTime paddedAndEmitted
    (flattenComputableInPolyTime (encoding := encoding))
  change @TM2ComputableInPolyTime
    (List (InputWorkspace (encoding := encoding)))
    (List (Workspace (encoding := encoding)))
    (InputWorkspace (encoding := encoding))
    (Workspace (encoding := encoding)) id id
    (fun workspace =>
      flatten
        (IndexedTemplateEmitterMachine.appendedOutput
          (PolySpaceInitialSourceTemplates.family decider)
          (PolySpaceInitialTailPadding.paddedWorkspace decider workspace)))
  exact complete

theorem flatten_appendedOutput
    (data : List (TailWorkspace (encoding := encoding))) :
    flatten
        (IndexedTemplateEmitterMachine.appendedOutput
          (PolySpaceInitialSourceTemplates.family decider) data) =
      data.map (fun item =>
        flattenItem (encoding := encoding) (.inl item)) ++
      (IndexedTemplateEmitter.emitted
        (PolySpaceInitialSourceTemplates.family decider) data).map
          (fun token =>
            (Sum.inr token : Workspace (encoding := encoding))) := by
  simp [flatten, IndexedTemplateEmitterMachine.appendedOutput,
    List.map_append, List.map_map, Function.comp_def, flattenItem]

theorem flatten_paddedWorkspace (symbols : List encoding.Γ)
    (tokens : List Token) :
    (PolySpaceInitialTailPadding.paddedWorkspace decider
        (embedData
            (PolySpaceUnaryPreparedLayout.preparedSources decider symbols) ++
          tokens.map fun token =>
            (Sum.inr token : InputWorkspace (encoding := encoding)))).map
        (fun item => flattenItem (encoding := encoding) (.inl item)) =
      (PolySpaceUnaryPreparedLayout.preparedSources decider symbols).map
          (fun symbol =>
            (Sum.inl (Sum.inl symbol) : Workspace (encoding := encoding))) ++
        tokens.map (fun token =>
          (Sum.inr token : Workspace (encoding := encoding))) ++
        (List.replicate
          (PolySpaceInitialTailPadding.tailCount decider symbols) ()).map
          (fun marker =>
            (Sum.inl (Sum.inr marker) : Workspace (encoding := encoding))) := by
  rw [PolySpaceInitialTailPadding.paddedWorkspace_embed_append_tokens]
  simp [embedData, List.map_append, List.map_map, Function.comp_def,
    flattenItem, List.append_assoc]

/-- Exact input-preserving behavior after an arbitrary earlier token prefix. -/
theorem runWorkspace_embed_append_tokens (symbols : List encoding.Γ)
    (tokens : List Token) :
    runWorkspace decider
        (embedData
            (PolySpaceUnaryPreparedLayout.preparedSources decider symbols) ++
          tokens.map fun token =>
            (Sum.inr token : InputWorkspace (encoding := encoding))) =
      (PolySpaceUnaryPreparedLayout.preparedSources decider symbols).map
          (fun symbol =>
            (Sum.inl (Sum.inl symbol) : Workspace (encoding := encoding))) ++
        tokens.map (fun token =>
          (Sum.inr token : Workspace (encoding := encoding))) ++
        (List.replicate
          (PolySpaceInitialTailPadding.tailCount decider symbols) ()).map
          (fun marker =>
            (Sum.inl (Sum.inr marker) : Workspace (encoding := encoding))) ++
        (PolySpaceInitialEmitter.sourcePrefixTokens decider symbols).map
          (fun token =>
            (Sum.inr token : Workspace (encoding := encoding))):= by
  unfold runWorkspace
  rw [flatten_appendedOutput, flatten_paddedWorkspace,
    PolySpaceInitialSourceTemplates.emitted_paddedWorkspace]

end PolySpaceInitialSourceEmitter
end PeriodicCNF
end LeanTrominoes
