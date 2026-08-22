/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFSourceOccurrenceRouteEmitterInputCompiler
import LeanTrominoes.PeriodicCNFSourceOccurrenceRouteEmitterSemanticEntryEnumeration
import LeanTrominoes.PeriodicCNFSourceOccurrenceRouteEmitterSemanticFormula
import LeanTrominoes.PeriodicCNFSourceOccurrenceTargetVertexFieldSemantics
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorTokensData

/-! # Exact semantic output of the source-occurrence route emitter -/

namespace LeanTrominoes.PeriodicCNF.SourceOccurrenceRouteEmitter

/-- Recursive formula entries consume exactly the target fields of the
explicit occurrence-route descriptors. -/
theorem formulaEntryTargets_eq_occurrenceTargets
    (source : PeriodicCNF Nat) :
    entryTargets source (formulaEntriesFrom source.clauses 0 0) =
      (PeriodicThreeSATThree.occurrenceRouteDescriptors source).map
        (fun descriptor => descriptor.targetVertexIndex) := by
  rw [formulaEntriesFrom_zero]
  simp [entryTargets,
    PeriodicThreeSATThree.occurrenceRouteDescriptors, List.map_map]

/-- Recursive formula entries emit exactly the counted unary tokens of the
explicit occurrence-route descriptors. -/
theorem formulaEntryTokens_eq_occurrenceRouteDescriptorTokens
    (source : PeriodicCNF Nat) :
    entryTokens source (formulaEntriesFrom source.clauses 0 0) =
      PeriodicOrthocrossing.routeDescriptorTokens
        (PeriodicThreeSATThree.occurrenceRouteDescriptors source) := by
  rw [formulaEntriesFrom_zero]
  simp [entryTokens, PeriodicOrthocrossing.routeDescriptorTokens,
    PeriodicOrthocrossing.routeDescriptorFieldBlocks,
    CountedUnaryFieldTokens.countedFieldBlocks,
    PeriodicThreeSATThree.occurrenceRouteDescriptors, List.map_map,
    List.flatMap_map, Function.comp_def]

/-- On a promised flat source, the certified emitter produces exactly the
counted unary occurrence-prefix route-descriptor stream. -/
theorem emit_sourceInput (source :
    SourceSplitRouteDescriptorTokens.Source) :
    emit (sourceInput source) =
      PeriodicOrthocrossing.routeDescriptorTokens
        (PeriodicThreeSATThree.occurrenceRouteDescriptors
          source.formula) := by
  unfold emit
  rw [sourceInput_occurrences, sourceInput_targets,
    SourceOccurrenceRouteTokens.sourceTokens_eq_formulaTokens,
    SourceOccurrenceRouteTokens.selectedCount_isClause_formulaTokens,
    SourceOccurrenceRouteTokens.selectedCount_isLiteral_formulaTokens,
    SourceOccurrenceTargetVertexIndices.indices_eq_occurrenceRouteDescriptor_targetVertexIndices,
    ← formulaEntryTargets_eq_occurrenceTargets]
  change emitAux source.formula.clauses.length
      (PeriodicCNF.presentationLiteralCount source.formula)
      ⟨0, 0, 0, 0, none,
        entryTargets source.formula
          (formulaEntriesFrom source.formula.clauses 0 0)⟩
      (source.formula.clauses.flatMap
        SourceOccurrenceRouteTokens.clauseTokens) = _
  rw [emitAux_formulaTokens source source.formula.clauses
    (fun _ member => member) 0 0 0 0 none]
  exact formulaEntryTokens_eq_occurrenceRouteDescriptorTokens source.formula

end LeanTrominoes.PeriodicCNF.SourceOccurrenceRouteEmitter
