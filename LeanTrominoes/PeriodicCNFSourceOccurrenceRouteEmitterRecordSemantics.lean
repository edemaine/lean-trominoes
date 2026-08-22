/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFSourceOccurrenceRouteEmitterData
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorUnaryData
import LeanTrominoes.PeriodicThreeSATThreeOccurrenceRouteDescriptorData

/-! # Semantics of one emitted source-occurrence route record -/

namespace LeanTrominoes.PeriodicCNF.SourceOccurrenceRouteEmitter

/-- If the finite literal and anchor bits describe their promised offsets,
the emitted eleven fields are exactly the corresponding occurrence-prefix
route descriptor fields. -/
theorem routeFields_eq_occurrenceRouteDescriptor_unaryFields
    (source : PeriodicCNF Nat) (incidence : CNFIncidence Nat)
    (edgeIndex : Nat) (literalIndex : Fin 3) (anchorNext : Bool)
    (literalForward : incidence.literal.IsForwardLocal)
    (literalIndexEq : literalIndex.val = incidence.literalIndex)
    (anchorEq : PeriodicCNF.clauseAnchor incidence.clause =
      (SourceForwardOffset.coordinate anchorNext, 0)) :
    routeFields source.clauses.length
        (PeriodicCNF.presentationLiteralCount source)
        incidence.clauseIndex edgeIndex literalIndex
        ((PeriodicThreeSATThree.rotatedOccurrenceVariables source).idxOf
          (incidence.literal.atom, incidence.clauseIndex,
            incidence.literalIndex))
        (SourceForwardOffset.isNext incidence.literal) anchorNext =
      (PeriodicThreeSATThree.occurrenceRouteDescriptor
        source incidence edgeIndex).unaryFields := by
  have offsetEq :
      Cell.sub incidence.literal.offset
          (PeriodicCNF.clauseAnchor incidence.clause) =
        SourceForwardOffset.relative
          (SourceForwardOffset.isNext incidence.literal) anchorNext := by
    rw [SourceForwardOffset.offset_eq_of_forward
      incidence.literal literalForward, anchorEq]
    rfl
  unfold routeFields offsetFields
    PeriodicThreeSATThree.occurrenceRouteDescriptor
    PeriodicOrthocrossing.RouteDescriptor.unaryFields
    PeriodicOrthocrossing.signedUnaryFields
  rw [literalIndexEq, offsetEq]
  rfl

/-- Token-level form of the one-record semantic equality. -/
theorem routeTokens_eq_occurrenceRouteDescriptor_countedFieldBlock
    (source : PeriodicCNF Nat) (incidence : CNFIncidence Nat)
    (edgeIndex : Nat) (literalIndex : Fin 3) (anchorNext : Bool)
    (literalForward : incidence.literal.IsForwardLocal)
    (literalIndexEq : literalIndex.val = incidence.literalIndex)
    (anchorEq : PeriodicCNF.clauseAnchor incidence.clause =
      (SourceForwardOffset.coordinate anchorNext, 0)) :
    routeTokens source.clauses.length
        (PeriodicCNF.presentationLiteralCount source)
        incidence.clauseIndex edgeIndex literalIndex
        ((PeriodicThreeSATThree.rotatedOccurrenceVariables source).idxOf
          (incidence.literal.atom, incidence.clauseIndex,
            incidence.literalIndex))
        (SourceForwardOffset.isNext incidence.literal) anchorNext =
      CountedUnaryFieldTokens.countedFieldBlock
        (PeriodicThreeSATThree.occurrenceRouteDescriptor
          source incidence edgeIndex).unaryFields := by
  unfold routeTokens
  rw [routeFields_eq_occurrenceRouteDescriptor_unaryFields source incidence
    edgeIndex literalIndex anchorNext literalForward literalIndexEq anchorEq]

end LeanTrominoes.PeriodicCNF.SourceOccurrenceRouteEmitter
