/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFSourceCycleLinkRouteEmitterInputCompiler
import LeanTrominoes.PeriodicThreeSATThreeCycleLinkZip
import LeanTrominoes.PeriodicThreeSATThreeExactSize

/-! # Semantics of source cycle-link route-emitter inputs -/

namespace LeanTrominoes.PeriodicCNF.SourceCycleLinkRouteEmitter

@[simp] theorem sourceInput_clauseCount
    (source : SourceSplitRouteDescriptorTokens.Source) :
    (sourceInput source).clauseCount = source.formula.clauses.length := rfl

@[simp] theorem sourceInput_groupSizes
    (source : SourceSplitRouteDescriptorTokens.Source) :
    (sourceInput source).groupSizes =
      (PeriodicThreeSATThree.sourceVariables source.formula).map fun atom =>
        (PeriodicThreeSATThree.occurrenceVariables
          source.formula atom).length := rfl

/-- The sum of the group-size fields is exactly the number of source literal
occurrences. -/
@[simp] theorem sourceInput_literalCount
    (source : SourceSplitRouteDescriptorTokens.Source) :
    (sourceInput source).literalCount =
      PeriodicCNF.presentationLiteralCount source.formula := by
  unfold Input.literalCount
  rw [sourceInput_groupSizes,
    PeriodicThreeSATThree.occurrenceVariables_total_length,
    PeriodicThreeSATThree.taggedLiterals_length]

end LeanTrominoes.PeriodicCNF.SourceCycleLinkRouteEmitter
