/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalCanonicalVariableElementCodeSemantics
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalVariableIncidenceElementCodeSelectorSemantics
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalVariableIncidenceExpectedBlockComponents

/-! # Private variable-element multiplicities in incidence blocks -/

noncomputable section

namespace LeanTrominoes.PeriodicCNFStripReduction

open Gadget PlanarThreeDM

/-- Repeat every structural element code according to its variable-local
degree two. -/
def duplicateElementCodes (codes : List Nat) : List Nat :=
  codes.flatMap fun code => [code, code]

/-- All canonical variable-local elements except the red cycle element,
listed color-major and expanded to degree two. -/
def groupedVariableCanonicalPrivateElementCodes
    (pair : GroupedVariableFanSlot) (current : Nat) : List Nat :=
  duplicateElementCodes
    ((directSourceFinalVariableElementCodeBlock .red pair current).drop 1 ++
      directSourceFinalVariableElementCodeBlock .green pair current ++
      directSourceFinalVariableElementCodeBlock .blue pair current)

/-- The audited private selectors of one occurrence are exactly two
references to every non-cycle canonical variable-local element. -/
theorem groupedVariableIncidenceExpectedPrivateElementCodeBlock_eq
    (pair : GroupedVariableFanSlot) (current next parent : Nat) :
    groupedVariableIncidenceExpectedPrivateElementCodeBlock
        pair current next parent =
      groupedVariableCanonicalPrivateElementCodes pair current := by
  cases kindEq : pair.1.kind (groupedVariableFanSiteSlot pair.2) <;>
    simp [groupedVariableIncidenceExpectedPrivateElementCodeBlock,
      VariableIncidenceLocalControl.expectedPrivateSelectors,
      VariableIncidenceLocalControl.current,
      VariableIncidenceLocalControl.ofPair,
      VariableIncidenceLocalControl.slot,
      groupedVariableCanonicalPrivateElementCodes,
      duplicateElementCodes,
      directSourceFinalVariableElementCodeBlock,
      directSourceFinalVariableElementCodeCandidateBlock,
      directSourceFinalVariableElementColorTagBase,
      kindEq]

end LeanTrominoes.PeriodicCNFStripReduction

end
