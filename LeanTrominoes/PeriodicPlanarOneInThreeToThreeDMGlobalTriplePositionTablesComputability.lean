/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicPlanarOneInThreeToThreeDMEnumerationComputability
import LeanTrominoes.PeriodicPlanarOneInThreeToThreeDMGlobalPositionData

/-! # Finite local-position tables for assembled 3DM triples -/

noncomputable section

namespace LeanTrominoes
namespace PeriodicPlanarOneInThreeToThreeDM

open Gadget PlanarThreeDM

/-- Complete variable-site offset of an ordinary triple, parameterized by
the only finite source datum it inspects: occurrence polarity. -/
def ordinaryTripleSitePositionTable
    (data :
      ((OccurrenceSlot × VariableOccurrenceVariant) × Bool) ×
        VariableOccurrenceTriple) : Cell :=
  placeVariableModulePoint
    (occurrenceVariableSiteSlot data.1.1.1)
    ((VariableOccurrence.orientedBoundaryDrawing
      data.1.1.2 data.1.2).triplePosition data.2)

/-- Complete variable-site offset of a fixed-red triple. -/
def fixedRedTripleSitePositionTable
    (data : (OccurrenceSlot × Bool) × FixedRedConnectorTriple) : Cell :=
  placeVariableModulePoint
    (occurrenceVariableSiteSlot data.1.1)
    ((FixedRedConnector.boundaryDrawing data.1.2).triplePosition data.2)

/-- Clause-core offset of one clause triple. -/
def clauseTriplePositionTable (set : X3CClauseSet) : Cell :=
  X3CClauseOrthogonal.setPosition set

theorem ordinaryTripleSitePositionTable_primrec :
    Primrec ordinaryTripleSitePositionTable :=
  Primrec.dom_finite ordinaryTripleSitePositionTable

theorem fixedRedTripleSitePositionTable_primrec :
    Primrec fixedRedTripleSitePositionTable :=
  Primrec.dom_finite fixedRedTripleSitePositionTable

theorem clauseTriplePositionTable_primrec :
    Primrec clauseTriplePositionTable :=
  Primrec.dom_finite clauseTriplePositionTable

end PeriodicPlanarOneInThreeToThreeDM
end LeanTrominoes
