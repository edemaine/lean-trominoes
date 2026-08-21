/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFSourceOccurrenceAtomGroupSizeCompiler
import LeanTrominoes.PeriodicCNFSourceOccurrenceAtomLastGroupSizeSemantics

/-! # Semantics of compiled source atom-group sizes -/

namespace LeanTrominoes
namespace PeriodicCNF
namespace SourceOccurrenceAtomGroupSizes

theorem sizes_eq_lastGroupSizes
    (source : SourceSplitRouteDescriptorTokens.Source) :
    sizes source = SourceOccurrenceAtomLastGroupSizes.sizes source := by
  rfl

/-- Compiled group sizes follow the exact source-variable vertex-block order. -/
theorem sizes_eq_sourceVariableCounts
    (source : SourceSplitRouteDescriptorTokens.Source) :
    sizes source =
      (PeriodicThreeSATThree.sourceVariables source.formula).map fun atom =>
        (SourceOccurrenceAtomLastGroupSizes.occurrenceAtoms
          source.formula).count atom := by
  rw [sizes_eq_lastGroupSizes]
  exact SourceOccurrenceAtomLastGroupSizes.sizes_eq_sourceVariableCounts
    source

end SourceOccurrenceAtomGroupSizes
end PeriodicCNF
end LeanTrominoes
