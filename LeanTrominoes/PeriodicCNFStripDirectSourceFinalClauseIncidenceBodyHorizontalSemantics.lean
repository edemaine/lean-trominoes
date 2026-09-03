/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalCanonicalIncidenceDirectionBlockListSemantics
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalClauseElementDegreeSemantics
import LeanTrominoes.PeriodicCNFStripHorizontalTripleOrderedIncidenceBodySemantics
import LeanTrominoes.PeriodicCNFStripHorizontalThreeDMTripleBlockData

/-! # Direct final clause incidence bodies match the horizontal typed suffix -/

noncomputable section

set_option maxHeartbeats 800000

namespace LeanTrominoes.PeriodicCNFStripReduction

open Gadget PeriodicThreeDM
open PeriodicCNF PeriodicPlanarOneInThreeToThreeDM

attribute [local instance]
  directFinalClauseDegreePatternVariableDecidableEq
  horizontalRoutedRoutesSourceVariableDecidableEq
  horizontalRibbonRoutedVariableDecidableEq
  horizontalThreeDMTripleVariableDecidableEq

/-- The fixed 27 incidence bodies of one clause core, in set-major RGB
order. -/
def horizontalClauseIncidenceBodyBlock : List (List AxisDirection) :=
  allClauseSets.flatMap fun set =>
    incidenceColors.map fun color =>
      HorizontalFiniteIncidenceDirectionQuery.directions
        (.clause set color)

/-- Typed clause triples contribute their incidence bodies in the clause
suffix of the global triple-major presentation. -/
def horizontalTypedClauseIncidenceBodiesInTripleOrder
    (source : PeriodicCNF Nat) : List (List AxisDirection) :=
  (horizontalThreeDMClauseTriplesZippedComputed source).flatMap fun triple =>
    incidenceColors.map fun color =>
      unitSubdivisionDirections
        (horizontalTypedIncidenceRouteComputed ((source, triple), color))

private theorem flatMap_const_eq_of_length
    {First Second Output : Type} (first : List First) (second : List Second)
    (block : List Output) (lengthEq : first.length = second.length) :
    first.flatMap (fun _ => block) = second.flatMap (fun _ => block) := by
  induction first generalizing second with
  | nil =>
      have secondNil : second = [] :=
        List.eq_nil_of_length_eq_zero (by simpa using lengthEq.symm)
      subst second
      rfl
  | cons head first induction =>
      cases second with
      | nil => simp at lengthEq
      | cons other second =>
          simp only [List.flatMap_cons]
          rw [induction second (by simpa using lengthEq)]

/-- The direct fan stream and the actual typed horizontal source contain the
same number of clauses. -/
theorem directSourceFinalClauseFans_length_eq_horizontalTypedClauses
    {Input : Type} {encoding : _root_.Computability.FinEncoding Input}
    {language : Input → Prop}
    (decider : Complexity.DeciderInPolySpace encoding language)
    (symbols : List encoding.Γ) :
    (directSourceFinalClauseFans decider symbols).length =
      (horizontalThreeDMTypedSourceComputed
        (PolySpaceCompiler.formulaOfSymbols decider symbols)).clauses.length := by
  have mapped := congrArg List.length
    (directSourceFinalClauseFans_hasRight_eq_typedClauseTernary
      decider symbols)
  simpa using mapped

/-- Direct clause bodies are one copy of the fixed 27-body block per final
clause fan. -/
theorem directSourceFinalClauseIncidenceBodies_eq_fanBlocks
    {Input : Type} {encoding : _root_.Computability.FinEncoding Input}
    {language : Input → Prop}
    (decider : Complexity.DeciderInPolySpace encoding language)
    (symbols : List encoding.Γ) :
    directSourceFinalClauseIncidenceBodies decider symbols =
      (directSourceFinalClauseFans decider symbols).flatMap
        fun _ => horizontalClauseIncidenceBodyBlock := by
  unfold directSourceFinalClauseIncidenceBodies
    directSourceFinalClauseIncidenceQueries
    finalClauseIncidenceQueryBlock horizontalClauseIncidenceBodyBlock
  rw [List.map_flatMap]
  rfl

private theorem horizontalTypedClauseIncidenceBodyBlock
    (source : PeriodicCNF Nat) (clauseIndex : Nat) :
    (allClauseSets.map
        (Triple.clause (Variable := RoutedVariable) clauseIndex)).flatMap
        (fun triple => incidenceColors.map fun color =>
          unitSubdivisionDirections
            (horizontalTypedIncidenceRouteComputed
              ((source, triple), color))) =
      horizontalClauseIncidenceBodyBlock := by
  rw [List.flatMap_map]
  unfold horizontalClauseIncidenceBodyBlock
  apply List.flatMap_congr
  intro set _setMember
  simp only [horizontalTypedIncidenceRouteComputed]
  apply List.map_congr_left
  intro color _colorMember
  simpa only [HorizontalFiniteIncidenceDirectionQuery.directions,
    horizontalClauseIncidenceDirections] using
    unitSubdivisionDirections_horizontalClauseIncidenceRouteComputed
      (((source, clauseIndex), set), color)

/-- The typed clause suffix is the same fixed block repeated once per typed
clause. -/
theorem horizontalTypedClauseIncidenceBodies_eq_clauseBlocks
    (source : PeriodicCNF Nat) :
    horizontalTypedClauseIncidenceBodiesInTripleOrder source =
      (horizontalThreeDMTypedSourceComputed source).clauses.zipIdx.flatMap
        fun _ => horizontalClauseIncidenceBodyBlock := by
  unfold horizontalTypedClauseIncidenceBodiesInTripleOrder
    horizontalThreeDMClauseTriplesZippedComputed
    horizontalThreeDMTypedSourceComputed
  rw [List.flatMap_assoc]
  apply List.flatMap_congr
  intro taggedClause _taggedClauseMember
  exact horizontalTypedClauseIncidenceBodyBlock
    source taggedClause.2

/-- The direct clause-incidence body suffix is exactly the clause part of the
typed horizontal triple-order route-body presentation. -/
theorem directSourceFinalClauseIncidenceBodies_eq_horizontalTyped
    {Input : Type} {encoding : _root_.Computability.FinEncoding Input}
    {language : Input → Prop}
    (decider : Complexity.DeciderInPolySpace encoding language)
    (symbols : List encoding.Γ) :
    directSourceFinalClauseIncidenceBodies decider symbols =
      horizontalTypedClauseIncidenceBodiesInTripleOrder
        (PolySpaceCompiler.formulaOfSymbols decider symbols) := by
  rw [directSourceFinalClauseIncidenceBodies_eq_fanBlocks,
    horizontalTypedClauseIncidenceBodies_eq_clauseBlocks]
  apply flatMap_const_eq_of_length
  rw [List.length_zipIdx]
  exact directSourceFinalClauseFans_length_eq_horizontalTypedClauses
    decider symbols

end LeanTrominoes.PeriodicCNFStripReduction
