/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.RetainedAngularFanFinalCarrierIndexedOccurrence

/-! # Span bounds at indexed final retained carriers -/

namespace LeanTrominoes
namespace PeriodicEightOccurrenceSplit

open PeriodicCNF
open PeriodicOrthocrossing
open PeriodicThreeSATThree

attribute [local instance]
  finalCarrierIndexedOccurrenceThreeOccurrenceDecidableEq

/-- The indexed carrier link itself supplies the equality-lens span bound
required to normalize each of its routes. -/
theorem FinalCarrierIndexedOccurrence.spanLarge
    {Variable : Type} [DecidableEq Variable]
    (occurrence : FinalCarrierIndexedOccurrence Variable)
    (nextSlice : Bool) :
    8 ≤ (finalCarrierRouteGeometryAt occurrence.source
      occurrence.taggedLink nextSlice).span := by
  have taggedLinkMember : occurrence.taggedLink ∈
      (retainedDrawingCompleteCarrierLinks
        occurrence.retained.incidenceGraph).product [true, false] := by
    have indexed := occurrence.taggedLinkIndexed.member
    exact List.fst_mem_of_mem_zipIdx indexed
  have linkMember : occurrence.taggedLink.1 ∈
      retainedDrawingCompleteCarrierLinks
        occurrence.retained.incidenceGraph :=
    (List.mem_product.mp taggedLinkMember).1
  have retainedWellFormed : occurrence.retained.incidenceGraph.IsWellFormed :=
    formula_incidenceGraph_isWellFormed occurrence.source
  have retainedDegree : occurrence.retained.incidenceGraph.DegreeAtMost 3 :=
    formula_incidenceGraph_degreeAtMostThree occurrence.sourceWidth
  have retainedLocal : occurrence.retained.incidenceGraph.IsLocal :=
    formula_incidenceGraph_isLocal occurrence.sourceLocal
  have physicalSpan :=
    (retainedDrawingCompleteCarrierLink_lensGeometry
      retainedWellFormed retainedDegree retainedLocal linkMember).spanLarge
  unfold FinalCarrierIndexedOccurrence.retained at physicalSpan
  have decEq :
      (finalCarrierIndexedOccurrenceThreeOccurrenceDecidableEq :
        DecidableEq (ThreeOccurrenceVariable Variable)) =
        drawingOrderedThreeOccurrenceVariableInstDecidableEq :=
    Subsingleton.elim _ _
  rw [decEq] at physicalSpan
  have spanEq := finalCarrierRouteGeometryAt_span_coe_eq
    occurrence.source occurrence.taggedLink nextSlice
  omega

end PeriodicEightOccurrenceSplit
end LeanTrominoes
