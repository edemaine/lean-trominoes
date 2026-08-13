/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.EmbeddedCNFIncidenceDrawingPlanarity
import LeanTrominoes.PlanarThreeSATTerminalPortCertificates

/-!
# Continuous planarity of the fixed Figure 8 incidence drawings

The terminal-ray layer already packages the direct clause-to-variable
drawings of the two fixed Figure 8 gadgets.  This file records the other
finite fact needed by the global assembly: those straight drawings are
continuously planar.  Keeping these certificates separate from terminal-port
validity lets later proofs transport exactly the geometric property they use.
-/

namespace LeanTrominoes
namespace PlanarThreeSAT

/-- The direct Figure 8(b) crossover incidences have their advertised
clause and variable endpoints. -/
theorem crossoverStraightIncidenceDrawing_routesMatch :
    crossoverStraightIncidenceDrawing.RoutesMatch := by
  exact straightIncidenceDrawing_routesMatch
    crossoverFormula CrossoverVariable.position

/-- The direct Figure 8(b) crossover incidence drawing is continuously
planar. -/
theorem crossoverStraightIncidenceDrawing_isPlanar :
    crossoverStraightIncidenceDrawing.IsPlanar := by
  native_decide

/-- The direct Figure 8(a) duplicator incidences have their advertised
clause and variable endpoints. -/
theorem duplicatorStraightIncidenceDrawing_routesMatch :
    duplicatorStraightIncidenceDrawing.RoutesMatch := by
  exact straightIncidenceDrawing_routesMatch
    duplicatorFormula DuplicatorVariable.position

/-- The direct Figure 8(a) duplicator incidence drawing is continuously
planar. -/
theorem duplicatorStraightIncidenceDrawing_isPlanar :
    duplicatorStraightIncidenceDrawing.IsPlanar := by
  native_decide

end PlanarThreeSAT
end LeanTrominoes
