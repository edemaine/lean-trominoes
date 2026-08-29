/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.RetainedAngularOccurrenceTerminalCoordinateComponentData

/-! # Clause presentation of retained terminal-coordinate columns -/

namespace LeanTrominoes
namespace PeriodicEightOccurrenceSplit
namespace TerminalCoordinateComponents

open PeriodicThreeSATThree

/-- The global terminal-coordinate column is the clause-major,
literal-major flattening of the source presentation. -/
theorem coordinates_eq_clauses
    {Variable : Type*}
    (source : PeriodicCNF Variable)
    (routes : PositionedPeriodicCNF.IncidenceRoutes) :
    coordinates source routes =
      source.clauses.zipIdx.flatMap fun taggedClause =>
        taggedClause.1.zipIdx.map fun taggedLiteral =>
          ofLex (retainedOccurrenceTerminalCoordinate routes
            (taggedLiteral.1.atom, taggedClause.2, taggedLiteral.2)) := by
  simp [coordinates, allOccurrenceVariables, taggedLiterals,
    List.map_flatMap, List.map_map,
    Function.comp_def]

end TerminalCoordinateComponents
end PeriodicEightOccurrenceSplit
end LeanTrominoes
