/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFPlanarRouteOccurrenceFiberSemantics
import LeanTrominoes.PeriodicThreeSATThreeCycleIncidenceSemantics
import LeanTrominoes.PeriodicThreeSATThreeCycleLinkIncidenceSemantics

/-! # Copied-prefix/cycle-suffix split of one variable-site fiber -/

namespace LeanTrominoes.PeriodicThreeSATThree

open PeriodicOrthocrossing

/-- At one split-formula variable site, selected occurrences are the copied
incidence fibers followed by the cycle-link fibers at their shifted global
indices. -/
theorem variableRouteOccurrencesAt_formula_eq_occurrence_append_cycle_fibers
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (site : VariableRouteSite (ThreeOccurrenceVariable Variable)) :
    variableRouteOccurrencesAt (formula source) site =
      ((occurrenceIncidences source).zipIdx.flatMap fun taggedIncidence =>
        translatedIncidenceOccurrencesAt taggedIncidence site) ++
      ((cycleLinkIncidences source).zipIdx
          (PeriodicCNF.presentationLiteralCount source)).flatMap
        fun taggedIncidence =>
          translatedIncidenceOccurrencesAt taggedIncidence site := by
  rw [variableRouteOccurrencesAt_eq_flatMap_fibers]
  rw [formula_incidencesWithMetadata_eq_occurrence_append_cycle]
  rw [← cycleLinkIncidences_eq_cycleIncidences]
  rw [List.zipIdx_append, List.flatMap_append]
  simp only [occurrenceIncidences_length, zero_add]

end LeanTrominoes.PeriodicThreeSATThree
