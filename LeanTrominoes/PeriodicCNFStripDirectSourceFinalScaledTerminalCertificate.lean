/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalTerminalCertificate
import LeanTrominoes.RetainedAngularFanFinalCoordinatedOccurrenceStableRank
import LeanTrominoes.RetainedAngularTerminalDataScaling

/-! # Scaled terminal certificate for the direct final source -/

noncomputable section

namespace LeanTrominoes.PeriodicCNFStripReduction

open PeriodicEightOccurrenceSplit
open PeriodicOrthocrossing

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

noncomputable local instance directFinalScaledCertificateStackFintype
    (stack : decider.tm.K) : Fintype (decider.tm.Γ stack) :=
  decider.stackAlphabetFinite stack

local instance directFinalScaledCertificateVariableDecidableEq :
    DecidableEq Variable :=
  directSourceVariableDecidableEq

theorem directSourceFinalScaledOccurrenceTerminalCertificate
    (symbols : List encoding.Γ) :
    RetainedOccurrenceTerminalCertificate
      (retainedFinalCoordinatedScaledSource
        (directSourceFormula decider symbols)).erase
      (retainedFinalCoordinatedScaledSourceRoutes
        (directSourceFormula decider symbols)) := by
  unfold retainedFinalCoordinatedScaledSource
    retainedFinalCoordinatedScaledSourceRoutes
  rw [PositionedPeriodicCNF.erase_scale]
  exact
    (directSourceFinalOccurrenceTerminalCertificate decider symbols).scaleIncidenceRoutes
      retainedAngularFanSourceClearanceFactor_pos

end LeanTrominoes.PeriodicCNFStripReduction

end
