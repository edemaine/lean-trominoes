/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFOneDimensional
import LeanTrominoes.PositionedPeriodicCNFVariableGauge

/-!
# One-dimensionality through variable gauging

A formula whose clause-anchor normalization is one dimensional has one common
vertical offset in each source clause.  Adding a variable gauge with zero
vertical component on every occurring atom preserves those common offsets,
so anchoring after the gauge again yields a one-dimensional formula.
-/

namespace LeanTrominoes
namespace PeriodicCNF

/-- Clause-anchor normalization preserves the one-dimensional fragment. -/
theorem anchorNormalize_isOneDimensional
    {Variable : Type*}
    {source : PeriodicCNF Variable}
    (horizontal : source.IsOneDimensional) :
    source.anchorNormalize.IsOneDimensional := by
  intro outputClause outputClauseMember outputLiteral outputLiteralMember
  simp only [PeriodicCNF.anchorNormalize, List.mem_map] at outputClauseMember
  obtain ⟨sourceClause, sourceClauseMember, rfl⟩ := outputClauseMember
  simp only [PeriodicClause.anchorNormalize, List.mem_map]
    at outputLiteralMember
  obtain ⟨sourceLiteral, sourceLiteralMember, rfl⟩ := outputLiteralMember
  cases sourceClause with
  | nil => simp at sourceLiteralMember
  | cons first rest =>
      have sourceZero := horizontal (first :: rest) sourceClauseMember
        sourceLiteral sourceLiteralMember
      have firstZero := horizontal (first :: rest) sourceClauseMember
        first (by simp)
      simp [PeriodicLiteral.anchorNormalize, PeriodicCNF.clauseAnchor,
        Cell.sub, sourceZero, firstZero]

/-- A variable gauge that is vertically zero on every occurring atom
preserves a one-dimensional formula. -/
theorem variableGauge_isOneDimensional
    {Variable : Type*}
    (source : PeriodicCNF Variable)
    (gauge : Variable → Cell)
    (horizontal : source.IsOneDimensional)
    (gaugeVertical :
      ∀ atom ∈ source.variableOccurrences, (gauge atom).2 = 0) :
    (source.variableGauge gauge).IsOneDimensional := by
  intro outputClause outputClauseMember outputLiteral outputLiteralMember
  simp only [PeriodicCNF.variableGauge, List.mem_map] at outputClauseMember
  obtain ⟨sourceClause, sourceClauseMember, rfl⟩ := outputClauseMember
  simp only [PeriodicClause.variableGauge, List.mem_map]
    at outputLiteralMember
  obtain ⟨sourceLiteral, sourceLiteralMember, rfl⟩ := outputLiteralMember
  have sourceZero := horizontal sourceClause sourceClauseMember
    sourceLiteral sourceLiteralMember
  have sourceAtomMember :
      sourceLiteral.atom ∈ source.variableOccurrences := by
    unfold PeriodicCNF.variableOccurrences
    apply List.mem_flatMap.mpr
    exact ⟨sourceClause, sourceClauseMember,
      List.mem_map.mpr ⟨sourceLiteral, sourceLiteralMember, rfl⟩⟩
  have gaugeZero := gaugeVertical sourceLiteral.atom sourceAtomMember
  simp [PeriodicLiteral.variableGauge, Cell.add, sourceZero, gaugeZero]

/-- A zero-vertical variable gauge preserves one-dimensionality after clause
anchor normalization. -/
theorem variableGauge_anchorNormalize_isOneDimensional
    {Variable : Type*}
    (source : PeriodicCNF Variable)
    (gauge : Variable → Cell)
    (horizontal : source.anchorNormalize.IsOneDimensional)
    (gaugeVertical :
      ∀ atom ∈ source.variableOccurrences, (gauge atom).2 = 0) :
    (source.variableGauge gauge).anchorNormalize.IsOneDimensional := by
  intro outputClause outputClauseMember outputLiteral outputLiteralMember
  simp only [PeriodicCNF.anchorNormalize, List.mem_map]
    at outputClauseMember
  obtain ⟨gaugedClause, gaugedClauseMember, rfl⟩ := outputClauseMember
  simp only [PeriodicCNF.variableGauge, List.mem_map]
    at gaugedClauseMember
  obtain ⟨sourceClause, sourceClauseMember, rfl⟩ := gaugedClauseMember
  simp only [PeriodicClause.anchorNormalize, List.mem_map]
    at outputLiteralMember
  obtain ⟨gaugedLiteral, gaugedLiteralMember, rfl⟩ :=
    outputLiteralMember
  simp only [PeriodicClause.variableGauge, List.mem_map]
    at gaugedLiteralMember
  obtain ⟨sourceLiteral, sourceLiteralMember, rfl⟩ := gaugedLiteralMember
  cases sourceClause with
  | nil => simp at sourceLiteralMember
  | cons first rest =>
      have normalizedClauseMember :
          PeriodicClause.anchorNormalize (first :: rest) ∈
            source.anchorNormalize.clauses := by
        unfold PeriodicCNF.anchorNormalize
        exact List.mem_map.mpr
          ⟨first :: rest, sourceClauseMember, rfl⟩
      have normalizedLiteralMember :
          sourceLiteral.anchorNormalize
              (PeriodicCNF.clauseAnchor (first :: rest)) ∈
            PeriodicClause.anchorNormalize (first :: rest) := by
        unfold PeriodicClause.anchorNormalize
        exact List.mem_map.mpr
          ⟨sourceLiteral, sourceLiteralMember, rfl⟩
      have normalizedZero := horizontal
        (PeriodicClause.anchorNormalize (first :: rest)) normalizedClauseMember
        (sourceLiteral.anchorNormalize
          (PeriodicCNF.clauseAnchor (first :: rest)))
        normalizedLiteralMember
      have sourceAtomMember :
          sourceLiteral.atom ∈ source.variableOccurrences := by
        unfold PeriodicCNF.variableOccurrences
        apply List.mem_flatMap.mpr
        exact ⟨first :: rest, sourceClauseMember,
          List.mem_map.mpr
            ⟨sourceLiteral, sourceLiteralMember, rfl⟩⟩
      have firstAtomMember : first.atom ∈ source.variableOccurrences := by
        unfold PeriodicCNF.variableOccurrences
        apply List.mem_flatMap.mpr
        exact ⟨first :: rest, sourceClauseMember,
          List.mem_map.mpr ⟨first, by simp, rfl⟩⟩
      have sourceGaugeZero :=
        gaugeVertical sourceLiteral.atom sourceAtomMember
      have firstGaugeZero := gaugeVertical first.atom firstAtomMember
      simpa [PeriodicClause.variableGauge,
        PeriodicLiteral.variableGauge,
        PeriodicLiteral.anchorNormalize,
        PeriodicCNF.clauseAnchor,
        Cell.add, Cell.sub,
        sourceGaugeZero, firstGaugeZero] using normalizedZero

end PeriodicCNF
end LeanTrominoes
