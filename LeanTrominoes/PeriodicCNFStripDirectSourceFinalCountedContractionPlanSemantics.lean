/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripCountedContractedIncidenceHorizontalEdgeBlockSemantics
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalCanonicalIncidenceDirectionBlockListSemantics
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalCountedContractionSemantics

/-! # Exact contraction plan of the direct final source -/

noncomputable section

namespace LeanTrominoes.PeriodicCNFStripReduction

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

/-- The complete direct incidence body recovered at one stable
element/occurrence-rank key. -/
def directSourceFinalIncidenceBodyAtKey
    (symbols : List encoding.Γ) (key : Nat) : List AxisDirection :=
  FiniteAlphabetKeyedDelimitedBlockLookup.alignedBody
    (CountedContractedIncidence.incidenceBlockKeys
      (directSourceFinalCanonicalIncidenceElementCodes decider symbols))
    (directSourceFinalCanonicalIncidenceBodies decider symbols)
    key

/-- The direct source's compiled query keys are exactly the two- or
three-incidence block attached to every canonical element, in element-major
order. -/
theorem directSourceFinalCountedContraction_queryKeys_eq
    (symbols : List encoding.Γ) :
    CountedContractedIncidence.queryKeys
        (directSourceFinalCanonicalElementCodes decider symbols)
        (directSourceFinalCanonicalElementDegrees decider symbols) =
      (List.zipWith CountedContractedIncidence.queryBlock
        (directSourceFinalCanonicalElementCodes decider symbols)
        (directSourceFinalCanonicalElementDegrees decider symbols)).flatten := by
  exact CountedContractedIncidence.queryKeys_eq_zipWith
    (directSourceFinalCanonicalElementCodes decider symbols)
    (directSourceFinalCanonicalElementDegrees decider symbols)
    (directSourceFinalCountedContraction_elementColumns_length
      decider symbols)
    (directSourceFinalCountedContraction_degrees_valid decider symbols)

/-- The aligned role stream is exactly one through pair for every
degree-two element and three retained roles for every degree-three element. -/
theorem directSourceFinalCountedContraction_roles_eq
    (symbols : List encoding.Γ) :
    CountedContractedIncidence.roles
        (directSourceFinalCanonicalElementDegrees decider symbols) =
      ((directSourceFinalCanonicalElementDegrees decider symbols).map
        CountedContractedIncidence.expectedRoleBlock).flatten := by
  exact CountedContractedIncidence.roles_eq_map
    (directSourceFinalCanonicalElementDegrees decider symbols)
    (directSourceFinalCountedContraction_degrees_valid decider symbols)

/-- The independently compiled incidence identities become precisely their
stable base-three occurrence keys before keyed block selection. -/
theorem directSourceFinalCountedContraction_incidenceBlockKeys_eq
    (symbols : List encoding.Γ) :
    CountedContractedIncidence.incidenceBlockKeys
        (directSourceFinalCanonicalIncidenceElementCodes decider symbols) =
      StableOccurrenceRanks.candidateKeys
        (directSourceFinalCanonicalIncidenceElementCodes decider symbols) := by
  exact CountedContractedIncidence.incidenceBlockKeys_eq_candidateKeys _

/-- Unique-key selection reduces the direct incidence body column to an
ordinary map over the canonical element/rank query stream. -/
theorem directSourceFinalCountedContraction_selectedBodies_eq_queryMap
    (symbols : List encoding.Γ) :
    CountedContractedIncidence.selectedBodies
        (directSourceFinalCanonicalElementCodes decider symbols)
        (directSourceFinalCanonicalElementDegrees decider symbols)
        (directSourceFinalCanonicalIncidenceElementCodes decider symbols)
        (directSourceFinalCanonicalIncidenceBodies decider symbols) =
      (CountedContractedIncidence.queryKeys
        (directSourceFinalCanonicalElementCodes decider symbols)
        (directSourceFinalCanonicalElementDegrees decider symbols)).map
          (directSourceFinalIncidenceBodyAtKey decider symbols) := by
  let incidenceCodes :=
    directSourceFinalCanonicalIncidenceElementCodes decider symbols
  have bodiesAligned :
      (directSourceFinalCanonicalIncidenceBodies decider symbols).length =
        (CountedContractedIncidence.incidenceBlockKeys
          incidenceCodes).length := by
    unfold CountedContractedIncidence.incidenceBlockKeys
    rw [UnaryFieldStableOccurrenceKeys.keys_length,
      directSourceFinalCanonicalIncidenceBodies_length,
      directSourceFinalCanonicalIncidenceElementCodes_length]
  have occurrenceContract :=
    directSourceFinalCountedContraction_occurrenceKeyContract
      decider symbols
  exact CountedContractedIncidence.selectedBodies_eq_map_alignedBody
    (directSourceFinalCanonicalElementCodes decider symbols)
    (directSourceFinalCanonicalElementDegrees decider symbols)
    incidenceCodes
    (directSourceFinalCanonicalIncidenceBodies decider symbols)
    bodiesAligned occurrenceContract.1 occurrenceContract.2

/-- The direct counted-contraction compiler is exactly the established
contracted-direction assembler applied to the uniquely selected incidence
bodies in canonical element/rank order. -/
theorem directSourceFinalCountedContractedDirectionTokens_eq_assembledBodies
    (symbols : List encoding.Γ) :
    directSourceFinalCountedContractedDirectionTokens decider symbols =
      PeriodicThreeDM.ContractedDirectionAssembler.output
        (((CountedContractedIncidence.roles
              (directSourceFinalCanonicalElementDegrees decider symbols)).zip
            (CountedContractedIncidence.selectedBodies
              (directSourceFinalCanonicalElementCodes decider symbols)
              (directSourceFinalCanonicalElementDegrees decider symbols)
              (directSourceFinalCanonicalIncidenceElementCodes
                decider symbols)
              (directSourceFinalCanonicalIncidenceBodies decider symbols))
          ).flatMap fun pair =>
            PeriodicThreeDM.ContractedDirectionAssembler.roleBlock
              pair.1 pair.2) := by
  have bodiesAligned :
      (directSourceFinalCanonicalIncidenceBodies decider symbols).length =
        (CountedContractedIncidence.incidenceBlockKeys
          (directSourceFinalCanonicalIncidenceElementCodes
            decider symbols)).length := by
    unfold CountedContractedIncidence.incidenceBlockKeys
    rw [UnaryFieldStableOccurrenceKeys.keys_length,
      directSourceFinalCanonicalIncidenceBodies_length,
      directSourceFinalCanonicalIncidenceElementCodes_length]
  have occurrenceContract :=
    directSourceFinalCountedContraction_occurrenceKeyContract
      decider symbols
  unfold directSourceFinalCountedContractedDirectionTokens
  rw [directSourceFinalCanonicalIncidenceDirectionTokens_eq_blocks]
  exact CountedContractedIncidence.output_blocks
    (directSourceFinalCanonicalElementCodes decider symbols)
    (directSourceFinalCanonicalElementDegrees decider symbols)
    (directSourceFinalCanonicalIncidenceElementCodes decider symbols)
    (directSourceFinalCanonicalIncidenceBodies decider symbols)
    (directSourceFinalCountedContraction_elementColumns_length
      decider symbols)
    (directSourceFinalCountedContraction_degrees_valid decider symbols)
    bodiesAligned occurrenceContract.1 occurrenceContract.2

/-- Explicit retained/through edge blocks obtained by regrouping the selected
incidence bodies according to the canonical degree column. -/
noncomputable def directSourceFinalCountedContractedEdgeBlocks
    (symbols : List encoding.Γ) :
    List PeriodicThreeDM.ContractedDirectionAssembler.EdgeBlock :=
  CountedContractedIncidence.edgeBlocks
    (directSourceFinalCanonicalElementDegrees decider symbols)
    (CountedContractedIncidence.selectedBodies
      (directSourceFinalCanonicalElementCodes decider symbols)
      (directSourceFinalCanonicalElementDegrees decider symbols)
      (directSourceFinalCanonicalIncidenceElementCodes decider symbols)
      (directSourceFinalCanonicalIncidenceBodies decider symbols))

/-- The compiled counted-contraction stream is exactly one independently
delimited direction word per explicit retained/through edge block. -/
theorem directSourceFinalCountedContractedDirectionTokens_eq_edgeBlocks
    (symbols : List encoding.Γ) :
    directSourceFinalCountedContractedDirectionTokens decider symbols =
      PeriodicThreeDM.ContractedDirectionAssembler.outputTokens
        (directSourceFinalCountedContractedEdgeBlocks decider symbols) := by
  rw [directSourceFinalCountedContractedDirectionTokens_eq_assembledBodies]
  unfold directSourceFinalCountedContractedEdgeBlocks
  apply CountedContractedIncidence.output_roleBodies_eq_edgeBlocks
  · rw [CountedContractedIncidence.selectedBodies_length]
    · exact (CountedContractedIncidence.roles_length_eq_queryKeys
        (directSourceFinalCanonicalElementCodes decider symbols)
        (directSourceFinalCanonicalElementDegrees decider symbols)
        (directSourceFinalCountedContraction_elementColumns_length
          decider symbols)
        (directSourceFinalCountedContraction_degrees_valid
          decider symbols)).symm
    · unfold CountedContractedIncidence.incidenceBlockKeys
      rw [UnaryFieldStableOccurrenceKeys.keys_length,
        directSourceFinalCanonicalIncidenceBodies_length,
        directSourceFinalCanonicalIncidenceElementCodes_length]
    · exact
        (directSourceFinalCountedContraction_occurrenceKeyContract
          decider symbols).1
    · exact
        (directSourceFinalCountedContraction_occurrenceKeyContract
          decider symbols).2
  · exact directSourceFinalCountedContraction_degrees_valid
      decider symbols

/-- Once the compiled degree and selected-body columns are identified with
the actual horizontal problem, the explicit direct blocks are exactly the
assembler edges underlying its canonical compact contracted blocks. -/
theorem directSourceFinalCountedContractedEdgeBlocks_eq_horizontal_of
    (symbols : List encoding.Γ)
    (incidenceBlock : PeriodicThreeDM.IncidenceTag →
      HorizontalTypedIncidenceDirectionBlock)
    (degrees : directSourceFinalCanonicalElementDegrees decider symbols =
      CountedContractedIncidence.horizontalElementDegrees
        (horizontalThreeDMProblemComputed
          (PeriodicCNF.PolySpaceCompiler.formulaOfSymbols decider symbols)))
    (bodies : CountedContractedIncidence.selectedBodies
        (directSourceFinalCanonicalElementCodes decider symbols)
        (directSourceFinalCanonicalElementDegrees decider symbols)
        (directSourceFinalCanonicalIncidenceElementCodes decider symbols)
        (directSourceFinalCanonicalIncidenceBodies decider symbols) =
      CountedContractedIncidence.horizontalIncidenceDirectionBodiesByElement
        (horizontalThreeDMProblemComputed
          (PeriodicCNF.PolySpaceCompiler.formulaOfSymbols decider symbols))
        incidenceBlock)
    (degreeTwoOrThree :
      (horizontalThreeDMProblemComputed
        (PeriodicCNF.PolySpaceCompiler.formulaOfSymbols
          decider symbols)).DegreeTwoOrThree) :
    directSourceFinalCountedContractedEdgeBlocks decider symbols =
      (horizontalContractedDirectionBlocks
        (horizontalThreeDMProblemComputed
          (PeriodicCNF.PolySpaceCompiler.formulaOfSymbols decider symbols))
        incidenceBlock).map fun tagged =>
          HorizontalContractedRoutedRequest.ContractedBlock.assemblerEdge
            tagged.2 := by
  unfold directSourceFinalCountedContractedEdgeBlocks
  rw [bodies, degrees]
  exact
    CountedContractedIncidence.edgeBlocks_horizontalIncidenceDirectionBodiesByElement
      _ incidenceBlock degreeTwoOrThree

end LeanTrominoes.PeriodicCNFStripReduction

end
