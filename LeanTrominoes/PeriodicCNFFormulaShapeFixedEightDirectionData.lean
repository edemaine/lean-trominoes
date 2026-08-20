/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.OccurrenceSplitRingCycleDrawing
import LeanTrominoes.PeriodicCNFFormulaShapeDirectionOrderingFormulaData
import LeanTrominoes.PeriodicCNFFormulaShapeFixedEightData

/-! # Finite direction descriptors for fixed-eight occurrence splitting -/

namespace LeanTrominoes
namespace PeriodicCNF
namespace FormulaShapeFixedEightDirection

open PlanarThreeSAT
open OccurrenceSplitRing

/-- Regard one finite embedded Figure 7 clause as a zero-offset positioned
periodic clause. -/
def localCycleClause (clause : EmbeddedClause RingVertex) :
    PositionedPeriodicClause RingVertex where
  position := clause.position
  literals := clause.literals.map fun literal =>
    { atom := literal.1
      offset := 0
      value := literal.2 }

/-- The closed nine-clause implication-ring template as a positioned
periodic presentation. -/
def localCycleFormula : PositionedPeriodicCNF RingVertex :=
  ⟨cycleFormula.map localCycleClause⟩

/-- Exact finite clause descriptors of the local Figure 7 implication ring.
The ring's nine output variables are emitted separately. -/
def cycleClauseDescriptors :
    List FormulaShapeDirectionOrdering.Token :=
  localCycleFormula.clauses.zipIdx.map fun taggedClause =>
    .clause
      (FormulaShapeDirectionOrdering.DirectedClauseProfile.ofClause
        cycleRoutes taggedClause.2 taggedClause.1)

/-- Complete canonical local ring descriptor stream, including its nine
distinct-variable markers. -/
def cycleDescriptors :
    List FormulaShapeDirectionOrdering.Token :=
  FormulaShapeDirectionOrdering.ofFormula
    localCycleFormula cycleRoutes

/-- Preserve an incoming retained clause descriptor and discard an incoming
variable marker in the copied-clause phase. -/
def copiedClauseBlock : FormulaShapeDirectionOrdering.Token →
    List FormulaShapeDirectionOrdering.Token
  | token@(.clause _) => [token]
  | .variable => []

/-- Append the same closed implication-ring clause block for each incoming
distinct-variable marker. -/
def cycleClauseBlock : FormulaShapeDirectionOrdering.Token →
    List FormulaShapeDirectionOrdering.Token
  | .clause _ => []
  | .variable => cycleClauseDescriptors

/-- Every incoming distinct variable becomes the nine fixed occurrence
copies (eight compass ports and one separator). -/
def copiedVariableBlock : FormulaShapeDirectionOrdering.Token →
    List FormulaShapeDirectionOrdering.Token
  | .clause _ => []
  | .variable =>
      List.replicate FormulaShapeFixedEight.copiesPerVariable .variable

/-- Canonical fixed-eight descriptor expansion: copied clauses, all ring
clauses, then all output-variable markers. -/
def descriptors (source : List FormulaShapeDirectionOrdering.Token) :
    List FormulaShapeDirectionOrdering.Token :=
  source.flatMap copiedClauseBlock ++
    source.flatMap cycleClauseBlock ++
      source.flatMap copiedVariableBlock

/-- One-pass block form used by the machine.  On canonical descriptor inputs
(all clauses followed by all variable markers), filtering its ordinary shape
recovers the same ordered clauses and variable count as `descriptors`. -/
def streamBlock (token : FormulaShapeDirectionOrdering.Token) :
    List FormulaShapeDirectionOrdering.Token :=
  copiedClauseBlock token ++
    cycleClauseBlock token ++ copiedVariableBlock token

/-- Direct one-pass fixed-eight descriptor output. -/
def streamDescriptors
    (source : List FormulaShapeDirectionOrdering.Token) :
    List FormulaShapeDirectionOrdering.Token :=
  source.flatMap streamBlock

/-- Descriptor streams produced by `ofFormula` have a clause prefix followed
by a suffix of distinct-variable markers. -/
def IsCanonical
    (source : List FormulaShapeDirectionOrdering.Token) : Prop :=
  ∃ (profiles : List
      FormulaShapeDirectionOrdering.DirectedClauseProfile) (count : Nat),
    source = profiles.map FormulaShapeDirectionOrdering.Token.clause ++
      List.replicate count FormulaShapeDirectionOrdering.Token.variable

end FormulaShapeFixedEightDirection
end PeriodicCNF
end LeanTrominoes
