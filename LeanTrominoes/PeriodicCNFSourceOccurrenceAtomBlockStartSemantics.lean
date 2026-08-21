/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFSourceOccurrenceAtomBlockStartCompiler
import LeanTrominoes.PeriodicCNFSourceOccurrenceAtomGroupSizeSemantics
import LeanTrominoes.PeriodicThreeSATThreeExactSize
import LeanTrominoes.PrefixSumsGetElem

/-! # Semantics of compiled source atom-block starts -/

namespace LeanTrominoes
namespace PeriodicCNF
namespace SourceOccurrenceAtomBlockStarts

theorem starts_length_eq_sourceVariables_length
    (source : SourceSplitRouteDescriptorTokens.Source) :
    (starts source).length =
      (PeriodicThreeSATThree.sourceVariables source.formula).length := by
  simp [starts, SourceOccurrenceAtomGroupSizes.sizes_eq_sourceVariableCounts]

theorem starts_getElem_eq_count_sum
    (source : SourceSplitRouteDescriptorTokens.Source)
    (index : Nat)
    (indexLt : index <
      (PeriodicThreeSATThree.sourceVariables source.formula).length) :
    (starts source)[index]'(by
        rw [starts_length_eq_sourceVariables_length]
        exact indexLt) =
      (((PeriodicThreeSATThree.sourceVariables source.formula).take index).map
        fun atom =>
          (SourceOccurrenceAtomLastGroupSizes.occurrenceAtoms
            source.formula).count atom).sum := by
  have sizeIndexLt : index <
      (SourceOccurrenceAtomGroupSizes.sizes source).length := by
    rw [SourceOccurrenceAtomGroupSizes.sizes_eq_sourceVariableCounts]
    simpa using indexLt
  unfold starts
  rw [PrefixSums.starts_getElem
    (SourceOccurrenceAtomGroupSizes.sizes source) index sizeIndexLt]
  rw [SourceOccurrenceAtomGroupSizes.sizes_eq_sourceVariableCounts,
    ← List.map_take]

/-- A block start is the total number of occurrence copies in all preceding
source-variable blocks. -/
theorem starts_getElem_eq_occurrenceVariables_sum
    (source : SourceSplitRouteDescriptorTokens.Source)
    (index : Nat)
    (indexLt : index <
      (PeriodicThreeSATThree.sourceVariables source.formula).length) :
    (starts source)[index]'(by
        rw [starts_length_eq_sourceVariables_length]
        exact indexLt) =
      (((PeriodicThreeSATThree.sourceVariables source.formula).take index).map
        fun atom =>
          (PeriodicThreeSATThree.occurrenceVariables
            source.formula atom).length).sum := by
  rw [starts_getElem_eq_count_sum source index indexLt]
  apply congrArg List.sum
  apply List.map_congr_left
  intro atom atomMem
  symm
  exact PeriodicThreeSATThree.occurrenceVariables_length_eq_count
    source.formula atom

end SourceOccurrenceAtomBlockStarts
end PeriodicCNF
end LeanTrominoes
