/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingCarrierPackedSpanRouteTailRecordMatrixSemantics
import LeanTrominoes.PeriodicOrthocrossingCarrierRankOrderedRetainedPairSpanGeometry
import LeanTrominoes.PeriodicOrthocrossingCarrierRankOrderedRouteTailRecordStreamSemantics

/-! # Numeric semantics of retained carrier Figure 9 record streams -/

namespace LeanTrominoes.PeriodicOrthocrossing
namespace CarrierRankOrderedPairs

/-- On valid numeric routes, the compiled stream is exactly one two-clause
Figure 9 tail-record block per selected carrier pair, in global row-major
order. -/
theorem retainedRouteTailRecordStream_numericRouteDescriptors
    {Variable : Type} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (wellFormed : formula.incidenceGraph.IsWellFormed)
    (degree : formula.incidenceGraph.DegreeAtMost 3)
    (isLocal : formula.incidenceGraph.IsLocal)
    (forward : formula.IsForwardLocal)
    (nonempty : PeriodicCNF.incidencesWithMetadata formula ≠ []) :
    retainedRouteTailRecordStream
        (PeriodicCNF.numericRouteDescriptors formula) =
      let descriptors := PeriodicCNF.numericRouteDescriptors formula
      let period := routeDescriptorStreamGridSize descriptors
      let datums :=
        (routeDescriptorCarrierRankDatumsAtPeriod
          period descriptors).dedup
      let entries := CarrierRankGlobal.enumeration datums
      entries.zipIdx.flatMap fun first =>
        entries.zipIdx.flatMap fun second =>
          if retainedPredicate first second then
            PeriodicCNF.FormulaShapeRetainedPlanarMetadataDirection.carrierLensRouteTailRecordBlock
              first.1.1.horizontal
              (first.1.1.pairNextSlice second.1.1)
              (second.1.1.orderCoordinate -
                first.1.1.orderCoordinate).toNat
          else [] := by
  let descriptors := PeriodicCNF.numericRouteDescriptors formula
  let period := routeDescriptorStreamGridSize descriptors
  let datums :=
    (routeDescriptorCarrierRankDatumsAtPeriod period descriptors).dedup
  let entries := CarrierRankGlobal.enumeration datums
  rw [retainedRouteTailRecordStream_eq_flatMap]
  rw [packedSpanCodes_numericRouteDescriptors
    formula wellFormed degree isLocal forward nonempty]
  change
    (((entries.zipIdx.flatMap fun first =>
      entries.zipIdx.map fun second =>
        if retainedPredicate first second then
          let span := (second.1.1.orderCoordinate -
            first.1.1.orderCoordinate).toNat
          4 * span + 4 +
            2 * BooleanListUnaryFields.bitNat first.1.1.horizontal +
              BooleanListUnaryFields.bitNat
                (first.1.1.pairNextSlice second.1.1)
        else 0).flatMap fun code =>
          CarrierPackedSpanRouteTailRecords.blockOutput
            (UnaryFieldEncoderMachine.unaryField code))) = _
  apply decodedPackedSpanMatrix_eq_canonical entries
  simpa [entries, datums, period, descriptors,
    routeDescriptorCarrierRankDatumsAtPeriod] using
    retainedPredicate_spanLarge_numericRouteDescriptors
      formula wellFormed degree isLocal nonempty

end CarrierRankOrderedPairs
end LeanTrominoes.PeriodicOrthocrossing
