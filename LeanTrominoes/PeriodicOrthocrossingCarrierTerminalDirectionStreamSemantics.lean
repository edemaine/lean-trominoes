/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.ListOptionalBlocksFlatten
import LeanTrominoes.PeriodicOrthocrossingCarrierTerminalColumnStreamDefinitions
import LeanTrominoes.PeriodicOrthocrossingCarrierPackedSpanTerminalDirectionMatrixSemantics
import LeanTrominoes.PeriodicOrthocrossingCarrierRankOrderedPackedSpanNumericSemantics

/-! # Global semantics of the retained-carrier terminal-direction column -/

namespace LeanTrominoes.PeriodicOrthocrossing
namespace CarrierRankOrderedPairs

open PeriodicCNF.FormulaShapeRetainedPlanarMetadataDirection
open CarrierPackedSpanTerminalColumns

/-- The packed matrix direction decoder emits exactly the selected carrier
direction-rank column. -/
theorem directionRankStream_packedSpanStream_numericRouteDescriptors
    {Variable : Type} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (wellFormed : formula.incidenceGraph.IsWellFormed)
    (degree : formula.incidenceGraph.DegreeAtMost 3)
    (isLocal : formula.incidenceGraph.IsLocal)
    (forward : formula.IsForwardLocal)
    (nonempty : PeriodicCNF.incidencesWithMetadata formula ≠ []) :
    directionRankStream
        (packedSpanStream (PeriodicCNF.numericRouteDescriptors formula)) =
      UnaryFieldEncoderMachine.unaryFields
        (retainedTerminalDirectionRanks
          (PeriodicCNF.numericRouteDescriptors formula)) := by
  let descriptors := PeriodicCNF.numericRouteDescriptors formula
  let period := routeDescriptorStreamGridSize descriptors
  let datums :=
    (routeDescriptorCarrierRankDatumsAtPeriod period descriptors).dedup
  let entries := CarrierRankGlobal.enumeration datums
  rw [show packedSpanStream descriptors =
      UnaryFieldEncoderMachine.unaryFields
        (packedSpanCodes descriptors) by rfl,
    packedSpanCodes_numericRouteDescriptors
      formula wellFormed degree isLocal forward nonempty,
    directionRankStream_unaryFields]
  unfold retainedTerminalDirectionRanks retainedTerminalDataBlocks
  dsimp only
  refine (decodedPackedSpanDirectionMatrix_eq_canonical entries).trans ?_
  apply congrArg UnaryFieldEncoderMachine.unaryFields
  unfold retainedTerminalDataBlocksFromDatums
  dsimp only
  simpa only [retainedPairTerminalDataBlock] using
    List.matrixOptionalBlocks_project_flatten
      entries.zipIdx entries.zipIdx retainedPredicate
      (fun first second =>
        carrierLensRouteTerminalDataBlock first.1.1.horizontal
          (second.1.1.orderCoordinate -
            first.1.1.orderCoordinate).toNat)
      terminalDataDirectionRanks (by rfl)

end CarrierRankOrderedPairs
end LeanTrominoes.PeriodicOrthocrossing
