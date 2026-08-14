/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicPlanarOneInThreeToThreeDMEnumerationComputability
import LeanTrominoes.PeriodicPlanarOneInThreeToThreeDMGlobalPositionData

/-! # Finite local-position tables for assembled red elements -/

noncomputable section

namespace LeanTrominoes
namespace PeriodicPlanarOneInThreeToThreeDM

open Gadget PlanarThreeDM

def cycleLinkPositionTable (slot : OccurrenceSlot) : Cell :=
  variableCycleLinkPosition (occurrenceVariableSiteSlot slot)

def fixedRedInternalRedPositionTable
    (data : (OccurrenceSlot × Bool) × FixedRedInternalRed) : Cell :=
  placeVariableModulePoint
    (occurrenceVariableSiteSlot data.1.1)
    ((FixedRedConnector.boundaryDrawing data.1.2).elementPosition
      (fixedRedInternalRedLocalElement data.2))

def redClauseInternalPosition : Cell :=
  redClauseElementLocalPosition
    (RedElement.clauseInternal (Variable := Unit) 0)

def redClauseTerminalPositionTable
    (group : X3CClauseTerminalGroup) : Cell :=
  redClauseElementLocalPosition
    (RedElement.clauseTerminal (Variable := Unit) 0 group)

theorem cycleLinkPositionTable_primrec :
    Primrec cycleLinkPositionTable :=
  Primrec.dom_finite cycleLinkPositionTable

theorem fixedRedInternalRedPositionTable_primrec :
    Primrec fixedRedInternalRedPositionTable :=
  Primrec.dom_finite fixedRedInternalRedPositionTable

theorem redClauseTerminalPositionTable_primrec :
    Primrec redClauseTerminalPositionTable :=
  Primrec.dom_finite redClauseTerminalPositionTable

end PeriodicPlanarOneInThreeToThreeDM
end LeanTrominoes
