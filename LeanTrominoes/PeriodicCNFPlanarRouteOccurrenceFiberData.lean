/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFPlanarRoutedVariableSiteOccurrenceData

/-! # Per-incidence routed-occurrence fibers at variable sites -/

namespace LeanTrominoes.PeriodicOrthocrossing

/-- Neighboring translations of one indexed incidence that reach a selected
lifted variable site. -/
def translatedIncidenceOccurrencesAt
    {Variable : Type*} [DecidableEq Variable]
    (taggedIncidence : CNFIncidence Variable × Nat)
    (site : VariableRouteSite Variable) :
    List (CNFRouteOccurrence Variable) :=
  (neighborTranslations.map fun translate =>
    (⟨taggedIncidence.1, taggedIncidence.2, translate⟩ :
      CNFRouteOccurrence Variable)).filter fun occurrence =>
        occurrence.variableOccurrence = site

end LeanTrominoes.PeriodicOrthocrossing
