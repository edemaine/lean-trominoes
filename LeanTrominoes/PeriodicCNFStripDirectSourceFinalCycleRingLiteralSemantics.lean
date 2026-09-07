/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman
-/
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalCycleRingVertexSlotCompiler

/-! # Cycle slot tables select their actual local ring literals -/

namespace LeanTrominoes.PeriodicCNFStripReduction

open OccurrenceSplitRing
open PeriodicCNF.FormulaShapeDirectionOrdering
open PeriodicCNF.FormulaShapeFigureNinePolarityRouteHeader
open PeriodicCNF.ClauseProfilePolarityRouteOperation
open HorizontalRoutedRouteHeader
open HorizontalRoutedRouteHeaderPresentationAtomScope

/-- Read a cycle vertex from the actual presentation literal selected by an
inherited scope. Unused parent-local entries retain the compiler's zero. -/
def directFinalCycleLiteralSlot (clause : PositionedPeriodicClause RingVertex) :
    AtomScopeControl → DirectFinalCycleRingVertexSlot
  | .inherited slot =>
      ((clause.literals[sourceSlotNat slot]?).map
        (fun literal => directFinalCycleRingVertexSlot literal.atom)).getD default
  | .parentLocal _ => default

/-- The complete fixed slot table agrees, entry by entry, with the actual
literal rows of the local implication-cycle formula. -/
theorem directSourceFinalLocalCycleRingVertexSlots_eq_literal_blocks :
    directSourceFinalLocalCycleRingVertexSlots =
      PeriodicCNF.FormulaShapeFixedEightDirection.localCycleFormula.clauses.zipIdx.flatMap
        (fun tagged =>
          (clauseBlock (DirectedClauseProfile.ofClause cycleRoutes tagged.2 tagged.1)).map
            (directFinalCycleLiteralSlot tagged.1)) := by
  native_decide

/-- Every inherited cycle scope refers to an active literal of that same
local cycle clause, so the optional lookup never uses its fallback. -/
theorem directFinalCycleLiteralSlot_inherited_active :
    ∀ tagged ∈ PeriodicCNF.FormulaShapeFixedEightDirection.localCycleFormula.clauses.zipIdx,
      ∀ slot : SourceLiteralSlot,
        AtomScopeControl.inherited slot ∈
          clauseBlock (DirectedClauseProfile.ofClause cycleRoutes tagged.2 tagged.1) →
        sourceSlotNat slot < tagged.1.literals.length := by
  native_decide

end LeanTrominoes.PeriodicCNFStripReduction
