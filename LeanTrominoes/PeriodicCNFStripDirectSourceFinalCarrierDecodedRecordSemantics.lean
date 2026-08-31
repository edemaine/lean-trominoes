/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalCarrierNormalizedBlockSemantics
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalCarrierSourceInput

/-! # Decoded-record semantics of direct final-carrier blocks -/

noncomputable section

namespace LeanTrominoes.PeriodicCNFStripReduction

open PeriodicEightOccurrenceSplit
open PeriodicOrthocrossing
open PlanarThreeSAT

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

noncomputable local instance directFinalCarrierDecodedRecordStackFintype
    (stack : decider.tm.K) : Fintype (decider.tm.Γ stack) :=
  decider.stackAlphabetFinite stack

attribute [local implicit_reducible]
  directSourceFinalStructuralBaseDecidableEq
attribute [local instance]
  directSourceFinalStructuralBaseDecidableEq

/-- Expanded semantic records of the direct carrier family are exactly the
clockwise decoding of its declarative normalized compiler blocks. -/
theorem directSourceFinalCarrierSourceClauseRecords_eq_decodedRecords
    (symbols : List encoding.Γ) :
    finalCarrierSourceClauseRecordsFrom
        (directThreeCNFSourceFormula decider symbols)
        (finalCarrierStart
          (directThreeCNFSourceFormula decider symbols))
        (finalCarrierPhysicalLinks
          (directThreeCNFSourceFormula decider symbols)) =
      BinaryRouteTailRecordClockwiseRelabel.decodedRecords
        (directSourceFinalCarrierNormalizedFallbackRecordBlocks
          decider symbols) := by
  have indexed :
      ∀ tagged ∈
          ((finalCarrierPhysicalLinks
              (directThreeCNFSourceFormula decider symbols)).product
            [true, false]).zipIdx
            (finalCarrierStart
              (directThreeCNFSourceFormula decider symbols)),
        finalCarrierTaggedLinkIndexed
          (directThreeCNFSourceFormula decider symbols)
          tagged.1 tagged.2 := by
    intro tagged taggedMember
    exact finalCarrierTaggedLinkIndexed_of_physical_mem
      (directThreeCNFSourceFormula decider symbols) tagged taggedMember
  have decoded :
      finalCarrierSourceClauseRecordsFrom
          (directThreeCNFSourceFormula decider symbols)
          (finalCarrierStart
            (directThreeCNFSourceFormula decider symbols))
          (finalCarrierPhysicalLinks
            (directThreeCNFSourceFormula decider symbols)) =
        BinaryRouteTailRecordClockwiseRelabel.decodedRecords
          (finalCarrierNormalizedRecordBlocksFrom
            (directThreeCNFSourceFormula decider symbols)
            (finalCarrierStart
              (directThreeCNFSourceFormula decider symbols))
            (finalCarrierPhysicalLinks
              (directThreeCNFSourceFormula decider symbols))) :=
    finalCarrierSourceClauseRecordsFrom_eq_decodedRecords
      (directThreeCNFSourceFinalCarrierInput decider symbols)
      (finalCarrierPhysicalLinks
        (directThreeCNFSourceFormula decider symbols))
      (finalCarrierStart
        (directThreeCNFSourceFormula decider symbols))
      indexed
  rw [← directSourceFinalCarrierNormalizedFallbackRecordBlocks_eq_semantic
    decider symbols] at decoded
  exact decoded

end LeanTrominoes.PeriodicCNFStripReduction

end
