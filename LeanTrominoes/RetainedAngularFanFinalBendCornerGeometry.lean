/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFFormulaShapeRetainedPlanarMetadataNormalizedBendRepresentativeDescriptors
import LeanTrominoes.PeriodicOrthocrossingBendCornerDrawingFamily
import LeanTrominoes.PeriodicThreeSATThreeGraph
import LeanTrominoes.RetainedAngularFanFinalBendIndexedOccurrence

/-! # Corner geometry of indexed final retained bends -/

namespace LeanTrominoes
namespace PeriodicEightOccurrenceSplit

open PeriodicCNF
open PeriodicCNF.FormulaShapeRetainedPlanarMetadataDirection
open PeriodicOrthocrossing
open PeriodicThreeSATThree

attribute [local instance]
  finalBendIndexedOccurrenceThreeOccurrenceDecidableEq

/-- Every indexed final bend inherits the genuine nonreversing geometry of
its retained graph route. -/
theorem FinalBendIndexedOccurrence.cornerGeometry
    {Variable : Type} [DecidableEq Variable]
    (occurrence : FinalBendIndexedOccurrence Variable) :
    occurrence.taggedBend.1.CornerGeometry := by
  have indexed := occurrence.taggedBendIndexed
  unfold finalBendTaggedBendIndexed at indexed
  have taggedMember : occurrence.taggedBend ∈
      (baseRouteBends occurrence.retained).product [true, false] :=
    List.fst_mem_of_mem_zipIdx indexed
  have bendMember : occurrence.taggedBend.1 ∈
      baseRouteBends occurrence.retained :=
    (List.mem_product.mp taggedMember).1
  have drawingMember := baseRouteBends_subset_drawing
    occurrence.retained bendMember
  exact drawingRouteBendDedup_cornerGeometry
    (formula_incidenceGraph_isWellFormed occurrence.source)
    (formula_incidenceGraph_degreeAtMostThree occurrence.sourceWidth)
    (formula_incidenceGraph_isLocal occurrence.sourceLocal)
    drawingMember

/-- The incoming and outgoing compass ports of an indexed final bend differ. -/
theorem FinalBendIndexedOccurrence.portsDifferent
    {Variable : Type} [DecidableEq Variable]
    (occurrence : FinalBendIndexedOccurrence Variable) :
    occurrence.taggedBend.1.incomingPort ≠
      occurrence.taggedBend.1.outgoingPort :=
  occurrence.cornerGeometry.portsDifferent

end PeriodicEightOccurrenceSplit
end LeanTrominoes
