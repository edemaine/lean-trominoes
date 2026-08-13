/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOneInThree
import LeanTrominoes.PositionedPeriodicCNFVariableGauge

/-!
# Exact-one semantics under variable gauges

Per-variable gauge changes preserve the physical truth value of every
literal occurrence.  The ordinary CNF version is part of the variable-gauge
infrastructure; this file records the corresponding exact-one statement.
-/

namespace LeanTrominoes
namespace PeriodicOneInThree

variable {Variable : Type*}

/-- Gauging a clause and pulling an assignment back leaves its complete
ordered truth-value list unchanged. -/
theorem clauseValues_variableGauge_pull
    (gauge : Variable → Cell)
    (assignment : Variable → Cell → Bool)
    (translate : Cell)
    (clause : PeriodicClause Variable) :
    clauseValues
        (PeriodicCNF.pullVariableGaugeAssignment gauge assignment)
        translate (clause.variableGauge gauge) =
      clauseValues assignment translate clause := by
  unfold clauseValues PeriodicClause.variableGauge
  rw [List.map_map]
  apply List.map_congr_left
  intro literal _literalMember
  rcases translate with ⟨translateX, translateY⟩
  rcases literal with ⟨atom, ⟨offsetX, offsetY⟩, value⟩
  cases gaugeEq : gauge atom with
  | mk gaugeX gaugeY =>
      simp [PeriodicLiteral.variableGauge,
        PeriodicCNF.pullVariableGaugeAssignment,
        Cell.add, Cell.sub, gaugeEq]
      constructor <;> intro holds
      · convert holds using 1 <;> ring
      · convert holds using 1 <;> ring

/-- Pushing an assignment forward gives the same truth-value list as
gauging the clause. -/
theorem clauseValues_push_variableGauge
    (gauge : Variable → Cell)
    (assignment : Variable → Cell → Bool)
    (translate : Cell)
    (clause : PeriodicClause Variable) :
    clauseValues
        (PeriodicCNF.pushVariableGaugeAssignment gauge assignment)
        translate clause =
      clauseValues assignment translate
        (clause.variableGauge gauge) := by
  unfold clauseValues PeriodicClause.variableGauge
  rw [List.map_map]
  apply List.map_congr_left
  intro literal _literalMember
  rcases translate with ⟨translateX, translateY⟩
  rcases literal with ⟨atom, ⟨offsetX, offsetY⟩, value⟩
  cases gaugeEq : gauge atom with
  | mk gaugeX gaugeY =>
      simp [PeriodicLiteral.variableGauge,
        PeriodicCNF.pushVariableGaugeAssignment,
        Cell.add, gaugeEq, add_assoc]

/-- Variable gauging and assignment pullback preserve one exact-one clause. -/
theorem clauseHolds_variableGauge_pull_iff
    (gauge : Variable → Cell)
    (assignment : Variable → Cell → Bool)
    (translate : Cell)
    (clause : PeriodicClause Variable) :
    ClauseHolds
        (PeriodicCNF.pullVariableGaugeAssignment gauge assignment)
        translate (clause.variableGauge gauge) ↔
      ClauseHolds assignment translate clause := by
  unfold ClauseHolds
  rw [clauseValues_variableGauge_pull]

/-- Assignment pushforward is inverse to clause gauging for exact-one
truth. -/
theorem clauseHolds_push_variableGauge_iff
    (gauge : Variable → Cell)
    (assignment : Variable → Cell → Bool)
    (translate : Cell)
    (clause : PeriodicClause Variable) :
    ClauseHolds
        (PeriodicCNF.pushVariableGaugeAssignment gauge assignment)
        translate clause ↔
      ClauseHolds assignment translate
        (clause.variableGauge gauge) := by
  unfold ClauseHolds
  rw [clauseValues_push_variableGauge]

/-- A variable gauge preserves exact-one satisfiability by a corresponding
translation of the plane-wide assignment. -/
theorem variableGauge_satisfiable_iff
    (source : PeriodicCNF Variable)
    (gauge : Variable → Cell) :
    Satisfiable (source.variableGauge gauge) ↔
      Satisfiable source := by
  constructor
  · rintro ⟨assignment, satisfies⟩
    refine
      ⟨PeriodicCNF.pushVariableGaugeAssignment gauge assignment, ?_⟩
    intro translate clause clauseMember
    have gaugedHolds := satisfies translate
      (clause.variableGauge gauge)
      (List.mem_map.mpr ⟨clause, clauseMember, rfl⟩)
    exact
      (clauseHolds_push_variableGauge_iff
        gauge assignment translate clause).mpr gaugedHolds
  · rintro ⟨assignment, satisfies⟩
    refine
      ⟨PeriodicCNF.pullVariableGaugeAssignment gauge assignment, ?_⟩
    intro translate gaugedClause gaugedClauseMember
    rcases List.mem_map.mp gaugedClauseMember with
      ⟨clause, clauseMember, rfl⟩
    exact
      (clauseHolds_variableGauge_pull_iff
        gauge assignment translate clause).mpr
        (satisfies translate clause clauseMember)

end PeriodicOneInThree
end LeanTrominoes
