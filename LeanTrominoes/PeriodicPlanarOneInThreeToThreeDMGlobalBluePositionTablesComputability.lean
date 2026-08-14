/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicPlanarOneInThreeToThreeDMGlobalGreenPositionTablesComputability

/-! # Finite local-position tables for assembled blue elements -/

noncomputable section

namespace LeanTrominoes
namespace PeriodicPlanarOneInThreeToThreeDM

open Gadget PlanarThreeDM

def fixedRedInternalBluePositionTable
    (data : (OccurrenceSlot × Bool) × FixedRedInternalBlue) : Cell :=
  placeVariableModulePoint
    (occurrenceVariableSiteSlot data.1.1)
    ((FixedRedConnector.boundaryDrawing data.1.2).elementPosition
      (fixedRedInternalBlueLocalElement data.2))

def blueClauseInternalPosition : Cell :=
  blueClauseElementLocalPosition
    (BlueElement.clauseInternal (Variable := Unit) 0)

def blueClauseTerminalPositionTable
    (group : X3CClauseTerminalGroup) : Cell :=
  blueClauseElementLocalPosition
    (BlueElement.clauseTerminal (Variable := Unit) 0 group)

theorem fixedRedInternalBluePositionTable_primrec :
    Primrec fixedRedInternalBluePositionTable :=
  Primrec.dom_finite fixedRedInternalBluePositionTable

theorem blueClauseTerminalPositionTable_primrec :
    Primrec blueClauseTerminalPositionTable :=
  Primrec.dom_finite blueClauseTerminalPositionTable

end PeriodicPlanarOneInThreeToThreeDM
end LeanTrominoes
