/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman
-/
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalGroupedVariableIncidenceBodyHorizontalSemantics
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalClauseIncidenceBodyHorizontalSemantics

/-! # Complete canonical incidence bodies agree with horizontal geometry -/

noncomputable section

namespace LeanTrominoes.PeriodicCNFStripReduction

open Gadget PeriodicThreeDM PeriodicPlanarOneInThreeToThreeDM

attribute [local instance]
  sourceVariableDecidableEq
  horizontalRibbonInnerVariableDecidableEq
  horizontalRibbonRoutedVariableDecidableEq

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

/-- The complete compiled variable-prefix and clause-suffix body list is
exactly the actual horizontal typed incidence list. -/
theorem directSourceFinalCanonicalIncidenceBodies_eq_horizontalTyped
    (symbols : List encoding.Γ) :
    directSourceFinalCanonicalIncidenceBodies decider symbols =
      horizontalTypedIncidenceBodiesInTripleOrder
        (PeriodicCNF.PolySpaceCompiler.formulaOfSymbols decider symbols) := by
  unfold directSourceFinalCanonicalIncidenceBodies horizontalTypedIncidenceBodiesInTripleOrder
  rw [directSourceFinalGroupedVariableIncidenceBodies_eq_horizontal,
    directSourceFinalClauseIncidenceBodies_eq_horizontalTyped,
    horizontalThreeDMTypedTriplesComputed_eq_blocks, List.flatMap_append]
  unfold horizontalTypedClauseIncidenceBodiesInTripleOrder horizontalThreeDMVariableTriplesComputed
  rw [horizontalNormalizedRoutedFormulaComputed_eq_semanticData]

/-- The emitted bodies therefore agree with the canonical stable-tag
selector used by contraction, in exactly its incidence-tag order. -/
theorem directSourceFinalCanonicalIncidenceBodies_eq_horizontal
    (symbols : List encoding.Γ) :
    directSourceFinalCanonicalIncidenceBodies decider symbols =
      (horizontalThreeDMProblemComputed
        (PeriodicCNF.PolySpaceCompiler.formulaOfSymbols decider symbols)).incidenceTags.map
        (fun tag => (horizontalCanonicalIncidenceDirectionBlock
          (PeriodicCNF.PolySpaceCompiler.formulaOfSymbols decider symbols) tag).directions) := by
  rw [directSourceFinalCanonicalIncidenceBodies_eq_horizontalTyped,
    horizontalCanonicalIncidenceBodies_eq_typedTripleOrder]

/-- The existing polynomial-time direction-token compiler serializes the
actual canonical horizontal body list with every incidence boundary retained. -/
theorem directSourceFinalCanonicalIncidenceDirectionTokens_eq_horizontal
    (symbols : List encoding.Γ) :
    directSourceFinalCanonicalIncidenceDirectionTokens decider symbols =
      FiniteAlphabetDelimitedBlockJoin.blocks
        ((horizontalThreeDMProblemComputed
          (PeriodicCNF.PolySpaceCompiler.formulaOfSymbols decider symbols)).incidenceTags.map
          (fun tag => (horizontalCanonicalIncidenceDirectionBlock
            (PeriodicCNF.PolySpaceCompiler.formulaOfSymbols decider symbols) tag).directions)) := by
  rw [directSourceFinalCanonicalIncidenceDirectionTokens_eq_blocks,
    directSourceFinalCanonicalIncidenceBodies_eq_horizontal]

end LeanTrominoes.PeriodicCNFStripReduction

end
