/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFFormulaShapeRetainedPlanarMetadataRoutedVariableNumericSiteArmScanData
import LeanTrominoes.PeriodicThreeSATThreeOccurrenceRouteDescriptorAtomLookup
import LeanTrominoes.PeriodicThreeSATThreeSplitOccurrenceDescriptorLookup

/-! # Numeric cycle arm blocks indexed by rotated occurrence atoms -/

namespace LeanTrominoes.PeriodicThreeSATThree

open PeriodicOrthocrossing
open PeriodicCNF.FormulaShapeRetainedPlanarMetadataDirection

/-- At the rotated index of a genuine occurrence atom, the split numeric
cycle-arm lookup equals the semantic block selected by its copied incidence. -/
theorem splitRouteDescriptors_cycleSiteArmBlockAtAtom_eq
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (atom : ThreeOccurrenceVariable Variable)
    (atomMember : atom ∈ rotatedOccurrenceVariables source) :
    routedVariableCycleSiteArmBlocksAtTargetIndex
        (splitRouteDescriptors source)
        ((rotatedOccurrenceVariables source).idxOf atom) =
      routedVariableCycleSiteArmBlocksAtAtom source atom := by
  rcases occurrenceRouteDescriptorAtOccurrenceAtom_eq_some
      source atom atomMember with
    ⟨taggedIncidence, _taggedMember, semanticLookup,
      descriptorLookup⟩
  let descriptor := occurrenceRouteDescriptor source
    taggedIncidence.1 taggedIncidence.2
  have numericLookup :
      occurrenceDescriptorAtTargetIndex
          (splitRouteDescriptors source)
          ((rotatedOccurrenceVariables source).idxOf atom) =
        some descriptor := by
    rw [occurrenceDescriptorAtTargetIndex_splitRouteDescriptors,
      descriptorLookup]
  unfold routedVariableCycleSiteArmBlocksAtTargetIndex
    routedVariableCycleSiteArmBlocksAtAtom
  rw [numericLookup, semanticLookup]
  have descriptorOffset : descriptor.offset =
      (occurrenceIncidence taggedIncidence.1).edge.offset := by
    unfold descriptor occurrenceRouteDescriptor
    rw [CNFIncidence.edge_offset,
      occurrenceIncidence_literal_offset,
      occurrenceIncidence_clause,
      clauseAnchor_occurrenceClause]
  simp only [descriptorOffset]

end LeanTrominoes.PeriodicThreeSATThree
