/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalCompactAtomWordSeparation
import LeanTrominoes.PeriodicCNFPlanarRetainedCertificate
import LeanTrominoes.PeriodicOrthocrossingRetainedPlanarSATGaugedDegree

/-! # Direct final scaled-source occurrence bound -/

noncomputable section

namespace LeanTrominoes
namespace PeriodicCNFStripReduction

open PeriodicCNF
open PeriodicEightOccurrenceSplit
open PeriodicOrthocrossing

set_option maxHeartbeats 800000

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

local instance directScaledSourceOccurrenceBoundVariableDecidableEq :
    DecidableEq Variable :=
  directSourceVariableDecidableEq

/-- The graph-degree bound supplies the source occurrence hypothesis under
the equality implementation used by the retained construction. -/
private theorem directSourceFormula_occurrencesAtMostThree
    (symbols : List encoding.Γ) :
    @PeriodicCNF.OccurrencesAtMost Variable instBEqOfDecidableEq
      (by infer_instance) 3 (directSourceFormula decider symbols) := by
  exact occurrencesAtMost_of_incidenceGraph_degreeAtMost
    (directSourceFormula_incidenceGraph_degreeAtMost decider symbols)

/-- The named direct source is local. -/
private theorem directSourceFormula_isLocal
    (symbols : List encoding.Γ) :
    (directSourceFormula decider symbols).IsLocal := by
  unfold directSourceFormula
  exact sourceFormula_isLocal _

/-- The named direct source has clauses of width at most three. -/
private theorem directSourceFormula_widthAtMostThree
    (symbols : List encoding.Γ) :
    (directSourceFormula decider symbols).WidthAtMost 3 := by
  unfold directSourceFormula
  exact sourceFormula_widthAtMostThree _

/-- The named direct source has no empty clauses. -/
private theorem directSourceFormula_clausesNonempty
    (symbols : List encoding.Γ) :
    ∀ clause ∈ (directSourceFormula decider symbols).clauses,
      clause ≠ [] := by
  unfold directSourceFormula
  exact sourceFormula_clausesNonempty _

/-- Package the direct source behind the generic retained-planar contract. -/
private theorem directSourceRetainedPlanarSATCertificate
    (symbols : List encoding.Γ) :
    RetainedPlanarSATCertificate
      (directSourceFormula decider symbols) := by
  exact
    @retainedPlanarSATCertificate
      Variable directScaledSourceOccurrenceBoundVariableDecidableEq
      (directSourceFormula decider symbols)
      (directSourceFormula_isLocal decider symbols)
      (directSourceFormula_widthAtMostThree decider symbols)
      (directSourceFormula_occurrencesAtMostThree decider symbols)
      (directSourceFormula_clausesNonempty decider symbols)

/-- Scaling the final coordinated source changes only positions, so erasure
is the retained formula packaged by the planarization certificate. -/
private theorem retainedFinalCoordinatedScaledSource_erase_eq_retainedPlanarSATFormula
    {Original : Type*} [DecidableEq Original]
    (source : PeriodicCNF Original) :
    (retainedFinalCoordinatedScaledSource source).erase =
      retainedPlanarSATFormula source := by
  unfold retainedFinalCoordinatedScaledSource finalCoordinatedSource
    retainedPlanarSATFormula
  exact PositionedPeriodicCNF.erase_scale _ _

/-- The exact source-scaled retained formula used by the direct terminal-rank
compiler inherits the established at-most-eight occurrence bound. -/
theorem directSourceFinalScaledSource_occurrencesAtMostEight
    (symbols : List encoding.Γ) :
    (retainedFinalCoordinatedScaledSource
      (directSourceFormula decider symbols)).erase.OccurrencesAtMost 8 := by
  rw [retainedFinalCoordinatedScaledSource_erase_eq_retainedPlanarSATFormula]
  have canonicalBound :=
    RetainedPlanarSATCertificate.occurrencesAtMostEight
      (directSourceRetainedPlanarSATCertificate decider symbols)
  exact PeriodicCNF.occurrencesAtMost_congr_beq
    _ _ (by infer_instance) (by infer_instance) 8 _
    canonicalBound

end PeriodicCNFStripReduction
end LeanTrominoes

end
