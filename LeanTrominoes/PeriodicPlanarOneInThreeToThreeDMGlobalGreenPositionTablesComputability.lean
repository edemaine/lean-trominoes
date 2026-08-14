/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicPlanarOneInThreeToThreeDMEnumerationComputability
import LeanTrominoes.PeriodicPlanarOneInThreeToThreeDMGlobalPositionData

/-! # Finite local-position tables for assembled green elements -/

noncomputable section

namespace LeanTrominoes
namespace PeriodicPlanarOneInThreeToThreeDM

open Gadget PlanarThreeDM

def ordinaryVariantForConnectorKind :
    VariableConnectorKind → VariableOccurrenceVariant
  | .fixedBlue => .fixedBlue
  | .fixedRed | .fixedGreen => .fixedGreen

/-- The ordinary internal position table is shared by green and blue typed
elements. -/
def ordinaryInternalPositionTable
    (data : ((OccurrenceSlot × VariableConnectorKind) × Bool) ×
      OrdinaryInternal) : Cell :=
  placeVariableModulePoint
    (occurrenceVariableSiteSlot data.1.1.1)
    ((VariableOccurrence.orientedBoundaryDrawing
      (ordinaryVariantForConnectorKind data.1.1.2)
      data.1.2).elementPosition
        (ordinaryInternalLocalElement data.2))

def fixedRedInternalGreenPositionTable
    (data : (OccurrenceSlot × Bool) × FixedRedInternalGreen) : Cell :=
  placeVariableModulePoint
    (occurrenceVariableSiteSlot data.1.1)
    ((FixedRedConnector.boundaryDrawing data.1.2).elementPosition
      (fixedRedInternalGreenLocalElement data.2))

def greenClauseInternalPosition : Cell :=
  greenClauseElementLocalPosition
    (GreenElement.clauseInternal (Variable := Unit) 0)

def greenClauseTerminalPositionTable
    (group : X3CClauseTerminalGroup) : Cell :=
  greenClauseElementLocalPosition
    (GreenElement.clauseTerminal (Variable := Unit) 0 group)

theorem ordinaryInternalPositionTable_primrec :
    Primrec ordinaryInternalPositionTable :=
  Primrec.dom_finite ordinaryInternalPositionTable

theorem fixedRedInternalGreenPositionTable_primrec :
    Primrec fixedRedInternalGreenPositionTable :=
  Primrec.dom_finite fixedRedInternalGreenPositionTable

theorem greenClauseTerminalPositionTable_primrec :
    Primrec greenClauseTerminalPositionTable :=
  Primrec.dom_finite greenClauseTerminalPositionTable

end PeriodicPlanarOneInThreeToThreeDM
end LeanTrominoes
