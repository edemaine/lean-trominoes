/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingCarrierTerminalColumnStreamDefinitions
import LeanTrominoes.PeriodicOrthocrossingCarrierPackedSpanTerminalRadialMatrixSemantics
import LeanTrominoes.PeriodicOrthocrossingCarrierRankOrderedPackedSpanNumericSemantics

/-! # Global semantics of the retained-carrier terminal-radial column -/

namespace LeanTrominoes.PeriodicOrthocrossing
namespace CarrierRankOrderedPairs

open PeriodicCNF.FormulaShapeRetainedPlanarMetadataDirection
open CarrierPackedSpanTerminalColumns

/-- The packed matrix radial decoder emits exactly the selected carrier
radial-length column. -/
theorem radialLengthStream_packedSpanStream_numericRouteDescriptors
    {Variable : Type} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (wellFormed : formula.incidenceGraph.IsWellFormed)
    (degree : formula.incidenceGraph.DegreeAtMost 3)
    (isLocal : formula.incidenceGraph.IsLocal)
    (forward : formula.IsForwardLocal)
    (nonempty : PeriodicCNF.incidencesWithMetadata formula ≠ []) :
    radialLengthStream
        (packedSpanStream (PeriodicCNF.numericRouteDescriptors formula)) =
      UnaryFieldEncoderMachine.unaryFields
        (retainedTerminalRadialLengths
          (PeriodicCNF.numericRouteDescriptors formula)) := by
  let descriptors := PeriodicCNF.numericRouteDescriptors formula
  let period := routeDescriptorStreamGridSize descriptors
  let datums :=
    (routeDescriptorCarrierRankDatumsAtPeriod period descriptors).dedup
  let entries := CarrierRankGlobal.enumeration datums
  have spanLarge := retainedPredicate_spanLarge_numericRouteDescriptors
    formula wellFormed degree isLocal nonempty
  change ∀ first ∈ entries.zipIdx, ∀ second ∈ entries.zipIdx,
      retainedPredicate first second = true →
        6 < (second.1.1.orderCoordinate -
          first.1.1.orderCoordinate).toNat at spanLarge
  rw [show packedSpanStream descriptors =
      UnaryFieldEncoderMachine.unaryFields
        (packedSpanCodes descriptors) by rfl,
    packedSpanCodes_numericRouteDescriptors
      formula wellFormed degree isLocal forward nonempty,
    radialLengthStream_unaryFields]
  unfold retainedTerminalRadialLengths retainedTerminalDataBlocks
  dsimp only
  exact decodedPackedSpanRadialMatrix_eq_canonical entries spanLarge

end CarrierRankOrderedPairs
end LeanTrominoes.PeriodicOrthocrossing
