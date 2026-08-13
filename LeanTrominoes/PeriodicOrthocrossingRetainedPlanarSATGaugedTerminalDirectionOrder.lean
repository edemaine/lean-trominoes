/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicEightOccurrenceSplitAngularFanOrder
import LeanTrominoes.PeriodicOrthocrossingRetainedPlanarSATGaugedTerminalDirections
import LeanTrominoes.PositionedPeriodicCNFDeduplicationTerminalPorts

/-!
# Ranked terminal directions in the retained angular occurrence order

The final retained planar-SAT routes have an eleven-direction terminal
vocabulary.  This file connects that geometric certificate to the syntactic
occurrence lists consumed by fixed-eight splitting.

Every genuine occurrence, and hence every entry of an angularly sorted
occurrence list, receives a concrete positive-length terminal
classification.  Increasing angular-list indices have nondecreasing
east-first direction ranks.  This is the order datum needed by the local
adapter from retained source rays to consecutive Figure 7 compass gates.
-/

namespace LeanTrominoes
namespace PeriodicOrthocrossing

set_option maxHeartbeats 800000

open PeriodicEightOccurrenceSplit
open PeriodicThreeSATThree

/-- Membership in an erased positioned occurrence list recovers the
positioned clause and literal at the occurrence's two presentation
indices. -/
private theorem exists_positionedOccurrence_of_mem_occurrenceVariables
    {Variable : Type*} [DecidableEq Variable]
    (source : PositionedPeriodicCNF Variable)
    (atom : Variable)
    (copy : ThreeOccurrenceVariable Variable)
    (copyMember :
      copy ∈ occurrenceVariables source.erase atom) :
    ∃ clause : PositionedPeriodicClause Variable,
      ∃ literal : PeriodicLiteral Variable,
        (clause, copy.2.1) ∈ source.clauses.zipIdx ∧
          (literal, copy.2.2) ∈ clause.literals.zipIdx ∧
          literal.atom = copy.1 := by
  simp only [occurrenceVariables, List.mem_filterMap]
    at copyMember
  rcases copyMember with
    ⟨tagged, taggedMember, selected⟩
  split at selected
  · simp only [Option.some.injEq] at selected
    subst copy
    rcases
        PositionedPeriodicCNF.exists_positionedOccurrence_of_tagged
          source taggedMember with
      ⟨clause, clauseMember, literalMember⟩
    exact
      ⟨clause, tagged.1, clauseMember, literalMember,
        by assumption⟩
  · contradiction

/-- Every genuine occurrence of the final retained source has a terminal
vector in the eleven-direction retained vocabulary. -/
theorem
    retainedDeduplicatedGaugedWrappedDrawingPeriodicPlanarSATOccurrence_terminalRay
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (wellFormed :
      formula.incidenceGraph.IsWellFormed)
    (degree :
      formula.incidenceGraph.DegreeAtMost 3)
    (isLocal :
      formula.incidenceGraph.IsLocal)
    (clausesNonempty :
      ∀ clause ∈ retainedDrawingPlanarSATFormula formula,
        clause.literals ≠ [])
    (atom : WrappedPeriodicPlanarSATVariable Variable)
    (copy :
      ThreeOccurrenceVariable
        (WrappedPeriodicPlanarSATVariable Variable))
    (copyMember :
      copy ∈
        occurrenceVariables
          (retainedDeduplicatedGaugedWrappedDrawingPositionedPeriodicPlanarSATFormula
            formula).erase
          atom) :
    RetainedTerminalRayVector
      (occurrenceTerminalVector
        (retainedDeduplicatedGaugedWrappedDrawingPeriodicPlanarSATIncidenceRoutes
          formula)
        copy) := by
  rcases
      exists_positionedOccurrence_of_mem_occurrenceVariables
        (retainedDeduplicatedGaugedWrappedDrawingPositionedPeriodicPlanarSATFormula
          formula)
        atom copy copyMember with
    ⟨clause, literal, clauseMember, literalMember, _atomEqual⟩
  exact
    retainedDeduplicatedGaugedWrappedDrawingPeriodicPlanarSATIncidenceRoutes_terminalRay
      formula wellFormed degree isLocal clausesNonempty
      clauseMember literalMember

/-- Every genuine final retained occurrence has a concrete direction and
positive primitive-block length. -/
theorem
    retainedDeduplicatedGaugedWrappedDrawingPeriodicPlanarSATOccurrence_exists_terminalDirection
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (wellFormed :
      formula.incidenceGraph.IsWellFormed)
    (degree :
      formula.incidenceGraph.DegreeAtMost 3)
    (isLocal :
      formula.incidenceGraph.IsLocal)
    (clausesNonempty :
      ∀ clause ∈ retainedDrawingPlanarSATFormula formula,
        clause.literals ≠ [])
    (atom : WrappedPeriodicPlanarSATVariable Variable)
    (copy :
      ThreeOccurrenceVariable
        (WrappedPeriodicPlanarSATVariable Variable))
    (copyMember :
      copy ∈
        occurrenceVariables
          (retainedDeduplicatedGaugedWrappedDrawingPositionedPeriodicPlanarSATFormula
            formula).erase
          atom) :
    ∃ direction : RetainedTerminalDirection,
      ∃ length : Nat,
        retainedTerminalDirectionClassify
            (occurrenceTerminalVector
              (retainedDeduplicatedGaugedWrappedDrawingPeriodicPlanarSATIncidenceRoutes
                formula)
              copy) =
          some (direction, length) := by
  have retained :=
    retainedDeduplicatedGaugedWrappedDrawingPeriodicPlanarSATOccurrence_terminalRay
      formula wellFormed degree isLocal clausesNonempty
      atom copy copyMember
  have classifiedSome :
      (retainedTerminalDirectionClassify
        (occurrenceTerminalVector
          (retainedDeduplicatedGaugedWrappedDrawingPeriodicPlanarSATIncidenceRoutes
            formula)
          copy)).isSome := by
    exact
      (retainedTerminalDirectionClassify_isSome_iff _).2
        retained
  rcases Option.isSome_iff_exists.mp classifiedSome with
    ⟨classified, classifiedEq⟩
  exact
    ⟨classified.1, classified.2, classifiedEq⟩

/-- Every indexed entry of a final retained angular occurrence list has a
concrete terminal-direction classification. -/
theorem
    retainedDeduplicatedGaugedWrappedDrawingPeriodicPlanarSATAngularOccurrence_getElem_exists_terminalDirection
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (wellFormed :
      formula.incidenceGraph.IsWellFormed)
    (degree :
      formula.incidenceGraph.DegreeAtMost 3)
    (isLocal :
      formula.incidenceGraph.IsLocal)
    (clausesNonempty :
      ∀ clause ∈ retainedDrawingPlanarSATFormula formula,
        clause.literals ≠ [])
    (atom : WrappedPeriodicPlanarSATVariable Variable)
    (index : Nat)
    (indexLt :
      index <
        (angularOccurrenceVariables
          (retainedDeduplicatedGaugedWrappedDrawingPositionedPeriodicPlanarSATFormula
            formula).erase
          (retainedDeduplicatedGaugedWrappedDrawingPeriodicPlanarSATIncidenceRoutes
            formula)
          atom).length) :
    ∃ direction : RetainedTerminalDirection,
      ∃ length : Nat,
        retainedTerminalDirectionClassify
            (occurrenceTerminalVector
              (retainedDeduplicatedGaugedWrappedDrawingPeriodicPlanarSATIncidenceRoutes
                formula)
              (angularOccurrenceVariables
                (retainedDeduplicatedGaugedWrappedDrawingPositionedPeriodicPlanarSATFormula
                  formula).erase
                (retainedDeduplicatedGaugedWrappedDrawingPeriodicPlanarSATIncidenceRoutes
                  formula)
                atom)[index]) =
          some (direction, length) := by
  let source :=
    (retainedDeduplicatedGaugedWrappedDrawingPositionedPeriodicPlanarSATFormula
      formula).erase
  let routes :=
    retainedDeduplicatedGaugedWrappedDrawingPeriodicPlanarSATIncidenceRoutes
      formula
  have angularMember :
      (angularOccurrenceVariables source routes atom)[index] ∈
        angularOccurrenceVariables source routes atom :=
    List.getElem_mem indexLt
  have occurrenceMember :
      (angularOccurrenceVariables source routes atom)[index] ∈
        occurrenceVariables source atom :=
    (angularOccurrenceVariables_perm
      source routes atom).mem_iff.mp angularMember
  exact
    retainedDeduplicatedGaugedWrappedDrawingPeriodicPlanarSATOccurrence_exists_terminalDirection
      formula wellFormed degree isLocal clausesNonempty
      atom
      (angularOccurrenceVariables source routes atom)[index]
      occurrenceMember

/-- Earlier entries in a final retained angular occurrence list have
nondecreasing ranks in the explicit eleven-direction vocabulary. -/
theorem
    retainedDeduplicatedGaugedWrappedDrawingPeriodicPlanarSATAngularOccurrence_getElem_terminalDirection_rank_le
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (wellFormed :
      formula.incidenceGraph.IsWellFormed)
    (degree :
      formula.incidenceGraph.DegreeAtMost 3)
    (isLocal :
      formula.incidenceGraph.IsLocal)
    (clausesNonempty :
      ∀ clause ∈ retainedDrawingPlanarSATFormula formula,
        clause.literals ≠ [])
    (atom : WrappedPeriodicPlanarSATVariable Variable)
    (first second : Nat)
    (firstLt :
      first <
        (angularOccurrenceVariables
          (retainedDeduplicatedGaugedWrappedDrawingPositionedPeriodicPlanarSATFormula
            formula).erase
          (retainedDeduplicatedGaugedWrappedDrawingPeriodicPlanarSATIncidenceRoutes
            formula)
          atom).length)
    (secondLt :
      second <
        (angularOccurrenceVariables
          (retainedDeduplicatedGaugedWrappedDrawingPositionedPeriodicPlanarSATFormula
            formula).erase
          (retainedDeduplicatedGaugedWrappedDrawingPeriodicPlanarSATIncidenceRoutes
            formula)
          atom).length)
    (before : first < second) :
    ∃ firstDirection secondDirection :
        RetainedTerminalDirection,
      ∃ firstLength secondLength : Nat,
        retainedTerminalDirectionClassify
            (occurrenceTerminalVector
              (retainedDeduplicatedGaugedWrappedDrawingPeriodicPlanarSATIncidenceRoutes
                formula)
              (angularOccurrenceVariables
                (retainedDeduplicatedGaugedWrappedDrawingPositionedPeriodicPlanarSATFormula
                  formula).erase
                (retainedDeduplicatedGaugedWrappedDrawingPeriodicPlanarSATIncidenceRoutes
                  formula)
                atom)[first]) =
            some (firstDirection, firstLength) ∧
          retainedTerminalDirectionClassify
            (occurrenceTerminalVector
              (retainedDeduplicatedGaugedWrappedDrawingPeriodicPlanarSATIncidenceRoutes
                formula)
              (angularOccurrenceVariables
                (retainedDeduplicatedGaugedWrappedDrawingPositionedPeriodicPlanarSATFormula
                  formula).erase
                (retainedDeduplicatedGaugedWrappedDrawingPeriodicPlanarSATIncidenceRoutes
                  formula)
                atom)[second]) =
            some (secondDirection, secondLength) ∧
          firstDirection.angularRank ≤
            secondDirection.angularRank := by
  let source :=
    (retainedDeduplicatedGaugedWrappedDrawingPositionedPeriodicPlanarSATFormula
      formula).erase
  let routes :=
    retainedDeduplicatedGaugedWrappedDrawingPeriodicPlanarSATIncidenceRoutes
      formula
  rcases
      retainedDeduplicatedGaugedWrappedDrawingPeriodicPlanarSATAngularOccurrence_getElem_exists_terminalDirection
        formula wellFormed degree isLocal clausesNonempty
        atom first firstLt with
    ⟨firstDirection, firstLength, firstClassified⟩
  rcases
      retainedDeduplicatedGaugedWrappedDrawingPeriodicPlanarSATAngularOccurrence_getElem_exists_terminalDirection
        formula wellFormed degree isLocal clausesNonempty
        atom second secondLt with
    ⟨secondDirection, secondLength, secondClassified⟩
  have ordered :
      occurrenceAngleLE routes
          (angularOccurrenceVariables source routes atom)[first]
          (angularOccurrenceVariables source routes atom)[second] =
        true :=
    angularOccurrenceVariables_getElem_angleLE
      source routes atom first second firstLt secondLt before
  exact
    ⟨firstDirection, secondDirection,
      firstLength, secondLength,
      firstClassified, secondClassified,
      occurrenceAngleLE_rank_le_of_classified
        routes
        (angularOccurrenceVariables source routes atom)[first]
        (angularOccurrenceVariables source routes atom)[second]
        firstClassified secondClassified ordered⟩

end PeriodicOrthocrossing
end LeanTrominoes
