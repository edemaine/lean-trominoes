/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicThreeSATThreeOccurrenceIncidenceData

/-! # Source hypotheses for final retained-carrier semantics -/

namespace LeanTrominoes
namespace PeriodicEightOccurrenceSplit

open PeriodicCNF
open PeriodicThreeSATThree

/-- The source-locality hypothesis shared by the final retained-carrier
lookup and route theorems. -/
structure FinalCarrierLocalFacts
    {Variable : Type} (source : PeriodicCNF Variable) where
  sourceLocal : source.IsLocal

/-- Add the width-three hypothesis to final-carrier source locality. -/
structure FinalCarrierWidthFacts
    {Variable : Type} (source : PeriodicCNF Variable) where
  localFacts : FinalCarrierLocalFacts source
  sourceWidth : source.WidthAtMost 3

/-- Add nonempty presented clauses to the local width-three hypotheses. -/
structure FinalCarrierNonemptyFacts
    {Variable : Type} (source : PeriodicCNF Variable) where
  widthFacts : FinalCarrierWidthFacts source
  sourceClausesNonempty : ∀ clause ∈ source.clauses, clause ≠ []

/-- Add the positive-offset hypothesis, completing the source facts shared
by final retained-carrier lookup and route theorems. -/
structure FinalCarrierSourceFacts
    {Variable : Type} (source : PeriodicCNF Variable) where
  nonemptyFacts : FinalCarrierNonemptyFacts source
  positiveOffsets : ∀ incidence ∈ occurrenceIncidences source,
    incidence.edge.offset = (0, 0) ∨ incidence.edge.offset = (1, 0)

end PeriodicEightOccurrenceSplit
end LeanTrominoes
