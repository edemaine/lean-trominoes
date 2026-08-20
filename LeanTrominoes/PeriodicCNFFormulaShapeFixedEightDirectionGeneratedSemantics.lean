/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFFormulaShapeFixedEightDirectionGeneratedData
import LeanTrominoes.PeriodicCNFFormulaShapeFixedEightDirectionSemantics
import LeanTrominoes.RetainedInputAppendPipeline

/-! # Correctness of two-pass fixed-eight direction descriptors -/

namespace LeanTrominoes
namespace PeriodicCNF
namespace FormulaShapeFixedEightDirection

open AffineTemplateEmitterMachine
open IndexedTemplateEmitter

@[simp] theorem cycleCodes_decode :
    cycleCodes.flatMap decodeCycleCode = cycleClauseDescriptors := by
  native_decide

private theorem positionTokens_map_fixed
    (tokens : List UnaryProgramTokens.Token) (position : Nat) :
    positionTokens (tokens.map Recipe.fixed) position = tokens := by
  unfold positionTokens
  rw [List.flatMap_map]
  simp [Recipe.tokens]

private theorem positionTokens_cycleCodes (position : Nat) :
    positionTokens (cycleCodes.map Recipe.fixed) position = cycleCodes :=
  positionTokens_map_fixed cycleCodes position

private theorem emittedAux_cycleFamily
    (position : Nat)
    (source : List FormulaShapeDirectionOrdering.Token) :
    emittedAux cycleFamily position source =
      (sourceVariableMarkers source).flatMap fun _ => cycleCodes := by
  induction source generalizing position with
  | nil => rfl
  | cons token source induction =>
      cases token with
      | clause profile =>
          rw [emittedAux_cons_none cycleFamily position (.clause profile)
            source (by rfl)]
          simpa [sourceVariableMarkers] using induction position
      | «variable» =>
          rw [emittedAux_cons_some cycleFamily position .variable source
            (cycleCodes.map Recipe.fixed) (by rfl),
            positionTokens_cycleCodes]
          simpa [sourceVariableMarkers] using induction (position + 1)

@[simp] theorem emitted_cycleFamily
    (source : List FormulaShapeDirectionOrdering.Token) :
    emitted cycleFamily source =
      (sourceVariableMarkers source).flatMap fun _ => cycleCodes :=
  emittedAux_cycleFamily 0 source

private theorem positionTokens_variableCodes (position : Nat) :
    positionTokens
        (List.replicate FormulaShapeFixedEight.copiesPerVariable
          (.fixed .freshUnit)) position =
      List.replicate FormulaShapeFixedEight.copiesPerVariable
        UnaryProgramTokens.Token.freshUnit := by
  simpa only [List.map_replicate] using
    positionTokens_map_fixed
      (List.replicate FormulaShapeFixedEight.copiesPerVariable
        UnaryProgramTokens.Token.freshUnit) position

private theorem emittedAux_variableFamily
    (position : Nat) (workspace : List CycleWorkspace) :
    emittedAux variableFamily position workspace =
      (sourceVariableMarkers
        (RetainedInputAppendPipeline.source workspace)).flatMap fun _ =>
          List.replicate FormulaShapeFixedEight.copiesPerVariable
            UnaryProgramTokens.Token.freshUnit := by
  induction workspace generalizing position with
  | nil => rfl
  | cons item workspace induction =>
      cases item with
      | inl token =>
          cases token with
          | clause profile =>
              rw [emittedAux_cons_none variableFamily position
                (.inl (.clause profile)) workspace (by rfl)]
              simpa [RetainedInputAppendPipeline.source,
                sourceVariableMarkers] using induction position
          | «variable» =>
              rw [emittedAux_cons_some variableFamily position
                (.inl .variable) workspace
                (List.replicate FormulaShapeFixedEight.copiesPerVariable
                  (.fixed .freshUnit)) (by rfl),
                positionTokens_variableCodes]
              simpa [RetainedInputAppendPipeline.source,
                sourceVariableMarkers] using induction (position + 1)
      | inr code =>
          rw [emittedAux_cons_none variableFamily position
            (.inr code) workspace (by rfl)]
          simpa [RetainedInputAppendPipeline.source] using induction position

@[simp] theorem emitted_variableFamily
    (workspace : List CycleWorkspace) :
    emitted variableFamily workspace =
      (sourceVariableMarkers
        (RetainedInputAppendPipeline.source workspace)).flatMap fun _ =>
          List.replicate FormulaShapeFixedEight.copiesPerVariable
            UnaryProgramTokens.Token.freshUnit :=
  emittedAux_variableFamily 0 workspace

@[simp] theorem source_firstPass
    (source : List FormulaShapeDirectionOrdering.Token) :
    RetainedInputAppendPipeline.source
        (IndexedTemplateEmitterMachine.appendedOutput cycleFamily source) =
      source := by
  change RetainedInputAppendPipeline.source
      (RetainedInputAppendPipeline.appended
        (emitted cycleFamily) source) = source
  exact RetainedInputAppendPipeline.source_appended _ _

private theorem source_cycleClauseBlock
    (source : List FormulaShapeDirectionOrdering.Token) :
    source.flatMap cycleClauseBlock =
      (sourceVariableMarkers source).flatMap fun _ =>
        cycleClauseDescriptors := by
  induction source with
  | nil => rfl
  | cons token source induction =>
      cases token <;>
        simpa [cycleClauseBlock, sourceVariableMarkers] using induction

private theorem source_copiedVariableBlock
    (source : List FormulaShapeDirectionOrdering.Token) :
    source.flatMap copiedVariableBlock =
      (sourceVariableMarkers source).flatMap fun _ =>
        List.replicate FormulaShapeFixedEight.copiesPerVariable .variable := by
  induction source with
  | nil => rfl
  | cons token source induction =>
      cases token <;>
        simpa [copiedVariableBlock, sourceVariableMarkers] using induction

private theorem decode_sourceItems
    (source : List FormulaShapeDirectionOrdering.Token) :
    ((source.map Sum.inl).map Sum.inl).flatMap decodeGeneratedItem =
      source.flatMap copiedClauseBlock := by
  rw [List.map_map, List.flatMap_map]
  rfl

private theorem decode_cycleEmissions
    (source : List FormulaShapeDirectionOrdering.Token) :
    (((emitted cycleFamily source).map Sum.inr).map Sum.inl).flatMap
        decodeGeneratedItem =
      source.flatMap cycleClauseBlock := by
  rw [List.map_map, List.flatMap_map, emitted_cycleFamily,
    List.flatMap_assoc, source_cycleClauseBlock]
  apply List.flatMap_congr
  intro marker markerMember
  exact cycleCodes_decode

private theorem decode_variableEmissions
    (source : List FormulaShapeDirectionOrdering.Token) :
    ((emitted variableFamily
      (IndexedTemplateEmitterMachine.appendedOutput
        cycleFamily source)).map Sum.inr).flatMap decodeGeneratedItem =
      source.flatMap copiedVariableBlock := by
  rw [List.flatMap_map, emitted_variableFamily, source_firstPass,
    source_copiedVariableBlock, List.flatMap_assoc]
  apply List.flatMap_congr
  intro marker markerMember
  change
    (List.replicate FormulaShapeFixedEight.copiesPerVariable
      UnaryProgramTokens.Token.freshUnit).flatMap
        (fun _ => [FormulaShapeDirectionOrdering.Token.variable]) =
      List.replicate FormulaShapeFixedEight.copiesPerVariable
        FormulaShapeDirectionOrdering.Token.variable
  native_decide

/-- The two retained-input passes and finite decoder produce exactly the
canonical phase-major fixed-eight descriptor specification. -/
@[simp] theorem generatedDescriptors_eq
    (source : List FormulaShapeDirectionOrdering.Token) :
    generatedDescriptors source = descriptors source := by
  unfold generatedDescriptors
  rw [show IndexedTemplateEmitterMachine.appendedOutput variableFamily
      (IndexedTemplateEmitterMachine.appendedOutput cycleFamily source) =
        (IndexedTemplateEmitterMachine.appendedOutput cycleFamily source).map
            Sum.inl ++
          (emitted variableFamily
            (IndexedTemplateEmitterMachine.appendedOutput
              cycleFamily source)).map Sum.inr by rfl,
    List.flatMap_append, decode_variableEmissions]
  rw [show IndexedTemplateEmitterMachine.appendedOutput cycleFamily source =
      source.map Sum.inl ++ (emitted cycleFamily source).map Sum.inr by rfl,
    List.map_append, List.flatMap_append,
    decode_sourceItems, decode_cycleEmissions]
  unfold descriptors
  rfl

end FormulaShapeFixedEightDirection
end PeriodicCNF
end LeanTrominoes
