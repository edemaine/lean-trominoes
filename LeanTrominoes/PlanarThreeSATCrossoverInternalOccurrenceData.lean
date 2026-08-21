/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PlanarThreeSATOcurrences

/-! # Fixed witnesses for crossover internal-variable occurrences -/

namespace LeanTrominoes.PlanarThreeSAT

/-- A fixed crossover clause witnessing each internal variable. -/
def crossoverInternalWitnessClause :
    CrossoverInternal → EmbeddedClause CrossoverVariable
  | .aInnerLeft => crossoverClause 2 6
      [(.aLeft, true), (.aInnerLeft, false)]
  | .upperLeft => crossoverClause 3 3
      [(.aInnerLeft, false), (.upperLeft, false), (.bInnerTop, true)]
  | .lowerLeft => crossoverClause 3 9
      [(.aInnerLeft, false), (.lowerLeft, false), (.bInnerBottom, false)]
  | .bInnerTop => crossoverClause 3 3
      [(.aInnerLeft, false), (.upperLeft, false), (.bInnerTop, true)]
  | .center => crossoverClause 5 6
      [(.upperLeft, false), (.lowerLeft, false), (.center, false)]
  | .bInnerBottom => crossoverClause 3 9
      [(.aInnerLeft, false), (.lowerLeft, false), (.bInnerBottom, false)]
  | .upperRight => crossoverClause 6 5
      [(.upperLeft, true), (.upperRight, true)]
  | .lowerRight => crossoverClause 6 7
      [(.lowerLeft, true), (.lowerRight, true)]
  | .aInnerRight => crossoverClause 8 5
      [(.upperRight, true), (.aInnerRight, false)]

end LeanTrominoes.PlanarThreeSAT
