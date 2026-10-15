/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.SAT.CNF.Compiler.PeriodicCNFProgramSource
import LeanTrominoes.Tiling.Tromino.Strip.Direct.Source.Final.Terminal.PeriodicCNFStripDirectSourceFinalTerminalCertificate
import LeanTrominoes.SAT.Planar.OccurrenceSplit.AngularFan.Final.Coordinated.RetainedAngularFanFinalCoordinatedOccurrenceStableRank
import LeanTrominoes.SAT.Planar.OccurrenceSplit.RetainedAngularTerminalDataScaling

/-! # Scaled terminal certificate for the direct final source -/

noncomputable section

namespace LeanTrominoes.PeriodicCNFStripReduction

open PeriodicEightOccurrenceSplit
open PeriodicOrthocrossing

variable {Input : Type}
variable {encoding : _root_.LeanTrominoes.FiniteEncoding Input}
variable {language : Input → Prop}
variable (decider : PeriodicCNF.ProgramSource encoding language)


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
