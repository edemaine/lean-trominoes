/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicThreeSATThreeCarrierClauseLookup

/-! # Structural start of the final carrier family -/

namespace LeanTrominoes.PeriodicEightOccurrenceSplit

open PeriodicCNF
open PeriodicCNF.FormulaShapeRetainedPlanarMetadataDirection
open PeriodicThreeSATThree

/-- Crossover-prefix length with the retained-variable equality supplied
explicitly. -/
def finalCarrierStartFamily
    {Variable : Type} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (occurrenceEq : DecidableEq (ThreeOccurrenceVariable Variable)) : Nat :=
  (@crossoverMetadataNormalizedClausesDedup
    (ThreeOccurrenceVariable Variable) occurrenceEq
      (PeriodicThreeSATThree.formula source)).length

/-- Structural crossover-prefix length of the generic final carrier family. -/
def finalCarrierStart
    {Variable : Type} [DecidableEq Variable]
    (source : PeriodicCNF Variable) : Nat :=
  finalCarrierStartFamily source
    fiveFamilyNormalizedThreeOccurrenceDecidableEq

end LeanTrominoes.PeriodicEightOccurrenceSplit
