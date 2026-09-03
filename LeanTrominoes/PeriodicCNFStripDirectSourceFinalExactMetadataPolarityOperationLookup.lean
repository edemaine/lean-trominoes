/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalExactMetadataPolarityOperationSemantics

/-! # Pointwise lookup of aligned direct and exact polarity operations -/

noncomputable section

namespace LeanTrominoes.PeriodicCNFStripReduction

open PeriodicCNF
open PeriodicOneInThreePolarityNormalizationRouteSubdivision

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

noncomputable local instance directFinalExactMetadataLookupStackFintype
    (stack : decider.tm.K) : Fintype (decider.tm.Γ stack) :=
  decider.stackAlphabetFinite stack

local instance directFinalExactMetadataLookupVariableDecidableEq :
    DecidableEq Variable :=
  directSourceVariableDecidableEq

/-- At every absolute occurrence index, the direct pair and exact metadata
block have the same global source incidence and operation. -/
theorem directFigureNinePolarityRoutePair_getD_sourceIndexedDescriptor_eq_exactMetadata
    (symbols : List encoding.Γ) (index : Nat)
    (indexLt : index <
      (directFigureNinePolarityRoutePairs decider symbols).length) :
    sourceIndexedDescriptorOf
        ((directFigureNinePolarityRoutePairSourceClauseIndices
          decider symbols).getD index 0)
        ((directFigureNinePolarityRoutePairs
          decider symbols).getD index default).1.polarity.indexed =
      ((directSourceFinalExactMetadataRouteBlocks
        decider symbols).getD index
          (.compatible (0, 0))).sourceIndexedDescriptor := by
  have sourceIndexLt : index <
      (directFigureNinePolarityRoutePairSourceClauseIndices
        decider symbols).length := by
    simpa using indexLt
  have exactBlockLt : index <
      (directSourceFinalExactMetadataRouteBlocks
        decider symbols).length := by
    simpa using indexLt
  have pointwise := congrArg (fun values => values[index]?)
    (directFigureNinePolarityRoutePairs_sourceIndexedDescriptor_eq_exactMetadata
      decider symbols)
  simp only [List.getElem?_zipWith, List.getElem?_map,
    List.getElem?_eq_getElem sourceIndexLt,
    List.getElem?_eq_getElem indexLt,
    List.getElem?_eq_getElem exactBlockLt,
    Option.map_some] at pointwise
  rw [List.getD_eq_getElem _ _ sourceIndexLt,
    List.getD_eq_getElem _ _ indexLt,
    List.getD_eq_getElem _ _ exactBlockLt]
  exact Option.some.inj pointwise

end LeanTrominoes.PeriodicCNFStripReduction

end
