/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripDirectSourceFormulaData
import LeanTrominoes.PeriodicThreeSATThreeExactFormulaVariableEnumeration

/-! # Exact direct source variable-vertex order -/

noncomputable section

namespace LeanTrominoes
namespace PeriodicCNFStripReduction

open PeriodicCNF

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

noncomputable local instance directSourceVariableEnumerationStackFintype
    (stack : decider.tm.K) : Fintype (decider.tm.Γ stack) :=
  decider.stackAlphabetFinite stack

noncomputable local instance directSourceVariableEnumerationDecidableEq :
    DecidableEq Variable :=
  directSourceVariableDecidableEq

/-- Exact source-level presentation of the occurrence-copy vertex prefix. -/
def directRotatedOccurrenceVariables (symbols : List encoding.Γ) :
    List Variable :=
  PeriodicThreeSATThree.rotatedOccurrenceVariables
    (PeriodicThreeCNF.formula
      (PolySpaceCompiler.formulaOfSymbols decider symbols))

/-- The direct guarded source's distinct variables are exactly the positional
copies of the width-three formula's literals, in presentation order. -/
theorem directSourceVariableOccurrences_dedup_eq_rotatedOccurrenceVariables
    (symbols : List encoding.Γ) :
    (PeriodicCNF.variableOccurrences
        (directSourceFormula decider symbols)).dedup =
      directRotatedOccurrenceVariables decider symbols := by
  unfold directRotatedOccurrenceVariables
  unfold directSourceFormula
  rw [sourceFormula_formulaOfSymbols]
  exact
    PeriodicThreeSATThree.formula_variableOccurrences_dedup_eq_rotatedOccurrenceVariables
      _

/-- Consequently the constructed incidence graph lists literal-occurrence
variables first, followed by its clause indices. -/
theorem directSourceIncidenceVertices_eq_rotatedOccurrences_append_clauses
    (symbols : List encoding.Γ) :
    (directSourceFormula decider symbols).incidenceGraph.vertices =
      (directRotatedOccurrenceVariables decider symbols).map
        CNFVertex.variable ++
        (List.range
          (directSourceFormula decider symbols).clauses.length).map
            CNFVertex.clause := by
  unfold PeriodicCNF.incidenceGraph
    PeriodicCNF.incidenceVariableVertices
    PeriodicCNF.incidenceClauseVertices
  rw [directSourceVariableOccurrences_dedup_eq_rotatedOccurrenceVariables]

end PeriodicCNFStripReduction
end LeanTrominoes
