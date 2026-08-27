/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingCarrierRankOrderedRetainedPairSpanGeometry
import LeanTrominoes.PeriodicOrthocrossingCarrierRankOrderedRouteDirectionStreamSemantics
import LeanTrominoes.PeriodicOrthocrossingCarrierTaggedSpanMatrixSemantics

/-! # Numeric semantics of retained carrier route-direction streams -/

namespace LeanTrominoes.PeriodicOrthocrossing
namespace CarrierRankOrderedPairs

/-- On valid numeric routes, the compiled carrier stream is exactly one
canonical four-route block per retained rank pair, in global row-major order. -/
theorem retainedRouteDirectionStream_numericRouteDescriptors
    {Variable : Type} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (wellFormed : formula.incidenceGraph.IsWellFormed)
    (degree : formula.incidenceGraph.DegreeAtMost 3)
    (isLocal : formula.incidenceGraph.IsLocal)
    (forward : formula.IsForwardLocal)
    (nonempty : PeriodicCNF.incidencesWithMetadata formula ≠ []) :
    retainedRouteDirectionStream
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
            CarrierSpanRouteDirections.canonicalBlock
              first.1.1.horizontal
              (second.1.1.orderCoordinate -
                first.1.1.orderCoordinate).toNat
          else [] := by
  let descriptors := PeriodicCNF.numericRouteDescriptors formula
  let period := routeDescriptorStreamGridSize descriptors
  let datums :=
    (routeDescriptorCarrierRankDatumsAtPeriod period descriptors).dedup
  let entries := CarrierRankGlobal.enumeration datums
  rw [retainedRouteDirectionStream_eq_flatMap]
  rw [taggedSpanCodes_numericRouteDescriptors
    formula wellFormed degree isLocal forward nonempty]
  change
    ((entries.zipIdx.flatMap fun first =>
      entries.zipIdx.map fun second =>
        if retainedPredicate first second then
          let span := (second.1.1.orderCoordinate -
            first.1.1.orderCoordinate).toNat
          span + span + 2 +
            BooleanListUnaryFields.bitNat first.1.1.horizontal
        else 0).flatMap fun code =>
          CarrierTaggedSpanRouteDirections.blockOutput
            (UnaryFieldEncoderMachine.unaryField code)) = _
  apply decodedTaggedSpanMatrix_eq_canonical entries
  simpa [entries, datums, period, descriptors,
    routeDescriptorCarrierRankDatumsAtPeriod] using
    retainedPredicate_spanLarge_numericRouteDescriptors
      formula wellFormed degree isLocal nonempty

end CarrierRankOrderedPairs
end LeanTrominoes.PeriodicOrthocrossing
