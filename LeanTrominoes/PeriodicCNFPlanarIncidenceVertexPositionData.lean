/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicGraph
import LeanTrominoes.PeriodicOrthocrossingConstruction
import LeanTrominoes.PeriodicOrthocrossingPlanarCrossovers

/-! # Positions of lifted periodic-CNF incidence vertices -/

namespace LeanTrominoes.PeriodicOrthocrossing

/-- Drawing-grid position of a lifted incidence-graph vertex. -/
def liftedIncidenceVertexPosition
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (vertex : CNFVertex Variable) (translate : Cell) : Cell :=
  let graph := PeriodicCNF.incidenceGraph formula
  Cell.add
    (PeriodicGridDrawing.vertexPosition graph (drawing graph) vertex)
    ((drawing graph).periodTranslation translate)

/-- Macro-grid origin surrounding a lifted incidence-graph vertex. -/
def liftedIncidenceVertexMacroOrigin
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (vertex : CNFVertex Variable) (translate : Cell) : Cell :=
  Cell.scale planarMacroScale
    (liftedIncidenceVertexPosition formula vertex translate)

end LeanTrominoes.PeriodicOrthocrossing
