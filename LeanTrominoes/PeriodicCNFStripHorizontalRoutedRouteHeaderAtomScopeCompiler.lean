/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.FiniteBlockTransducer
import LeanTrominoes.PeriodicCNFStripHorizontalRoutedRouteHeaderAtomScopeData

/-! # Finite atom-scope projection -/

noncomputable section

namespace LeanTrominoes
namespace PeriodicCNFStripReduction
namespace HorizontalRoutedRouteHeaderAtomScope

open Computability Turing

abbrev Input := HorizontalRoutedRouteHeader.OccurrenceData
abbrev Output := HorizontalRoutedRouteHeader.AtomScopeControl

def tokenBlock (occurrence : Input) : List Output :=
  [occurrence.atomScopeControl]

/-- Classify every final occurrence as inherited or parent-local. -/
def output (occurrences : List Input) : List Output :=
  occurrences.flatMap tokenBlock

@[simp] theorem output_eq_map (occurrences : List Input) :
    output occurrences = occurrences.map
      HorizontalRoutedRouteHeader.OccurrenceData.atomScopeControl := by
  induction occurrences with
  | nil => rfl
  | cons occurrence occurrences induction =>
      change occurrences.flatMap tokenBlock =
        occurrences.map
          HorizontalRoutedRouteHeader.OccurrenceData.atomScopeControl at induction
      change occurrence.atomScopeControl ::
          occurrences.flatMap tokenBlock =
        occurrence.atomScopeControl ::
          occurrences.map
            HorizontalRoutedRouteHeader.OccurrenceData.atomScopeControl
      rw [induction]

/-- Atom-scope classification is a fixed finite block transducer. -/
noncomputable def computableInPolyTime :
    TM2ComputableInPolyTime id id output :=
  FiniteBlockTransducer.computableInPolyTime tokenBlock

end HorizontalRoutedRouteHeaderAtomScope
end PeriodicCNFStripReduction
end LeanTrominoes

end
