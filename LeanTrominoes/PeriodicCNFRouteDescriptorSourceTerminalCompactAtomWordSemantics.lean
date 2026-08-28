/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFFormulaShapeRetainedPlanarMetadataRoutedClauseEndpointNormalization
import LeanTrominoes.PeriodicOrthocrossingRetainedCompactAtomWord
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorSourceTerminalCompactWordData

/-! # Semantic source-terminal compact words of CNF descriptors -/

namespace LeanTrominoes
namespace PeriodicCNF

open PeriodicOrthocrossing
open FormulaShapeRetainedPlanarMetadataDirection

/-- One numeric incidence descriptor emits exactly the compact retained-atom
word of its normalized source terminal. -/
theorem numericRouteDescriptor_sourceTerminalCompactWord
    {Variable : Type} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (wellFormed : formula.incidenceGraph.IsWellFormed)
    (sourceWord : Variable → List Bool)
    (taggedIncidence : CNFIncidence Variable × Nat)
    (taggedMember :
      taggedIncidence ∈ formula.incidencesWithMetadata.zipIdx) :
    RouteDescriptorSourceTerminalCompactWords.word
        (taggedIncidence.1.numericRouteDescriptor
          formula taggedIncidence.2) =
      RetainedCompactAtomWords.word sourceWord
        (externalWrappedVariableNormalization formula
          (.carrier (.terminal
            ((⟨taggedIncidence.1, taggedIncidence.2, (0, 0)⟩ :
                CNFRouteOccurrence Variable).sourceTerminal formula)))).1 := by
  let occurrence : CNFRouteOccurrence Variable :=
    ⟨taggedIncidence.1, taggedIncidence.2, (0, 0)⟩
  have normalized :=
    externalWrappedVariableNormalization_sourceTerminal_eq
      formula wellFormed taggedIncidence taggedMember (0, 0)
  change RouteDescriptorSourceTerminalCompactWords.word
      (taggedIncidence.1.numericRouteDescriptor
        formula taggedIncidence.2) =
    RetainedCompactAtomWords.word sourceWord
      (externalWrappedVariableNormalization formula
        (.carrier (.terminal (occurrence.sourceTerminal formula)))).1
  rw [normalized]
  have routeKeyEq := occurrence.sourceTerminal_routeKey formula
  have routeIndexEq :
      (occurrence.sourceTerminal formula).indexed.routeIndex =
        taggedIncidence.2 := by
    exact congrArg Prod.fst routeKeyEq
  dsimp [occurrence] at routeIndexEq
  simp [RouteDescriptorSourceTerminalCompactWords.word,
    RetainedCompactAtomWords.word, RetainedCompactAtomWords.carrierPair,
    RetainedCompactAtomWords.zeroCarrierNode,
    CarrierNodeSourceKeys.pair, CarrierNodeSourceKeys.taggedKey,
    CarrierNodeSourceKeys.segmentEndTag,
    SegmentTerminal.carrierKey,
    PeriodicGridDrawing.SegmentOccurrenceKey,
    routeIndexEq,
    CNFIncidence.numericRouteDescriptor]

end PeriodicCNF
end LeanTrominoes
