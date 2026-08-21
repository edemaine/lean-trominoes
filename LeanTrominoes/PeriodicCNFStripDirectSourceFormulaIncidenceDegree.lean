/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripDirectSourceFormulaData
import LeanTrominoes.PeriodicGraph

/-! # Incidence degree of the named direct source formula -/

noncomputable section

namespace LeanTrominoes
namespace PeriodicCNFStripReduction

open PeriodicCNF

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

noncomputable local instance directSourceIncidenceDegreeStackFintype
    (stack : decider.tm.K) : Fintype (decider.tm.Γ stack) :=
  decider.stackAlphabetFinite stack

noncomputable local instance directSourceIncidenceDegreeVariableDecidableEq :
    DecidableEq Variable :=
  directSourceVariableDecidableEq

noncomputable local instance directSourceIncidenceDegreeVariableBEq :
    BEq Variable :=
  directSourceVariableBEq

local instance directSourceIncidenceDegreeVariableLawfulBEq :
    LawfulBEq Variable :=
  directSourceVariableLawfulBEq

theorem directSourceFormula_incidenceGraph_degreeAtMost
    (symbols : List encoding.Γ) :
    (directSourceFormula decider symbols).incidenceGraph.DegreeAtMost 3 := by
  unfold directSourceFormula
  exact PeriodicCNF.incidenceGraph_degreeAtMost
    (sourceFormula_widthAtMostThree _)
    (sourceFormula_occurrencesAtMostThree_canonicalBEq _)

end PeriodicCNFStripReduction
end LeanTrominoes
