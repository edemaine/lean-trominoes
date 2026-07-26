import LeanTrominoes.PeriodicEightOccurrenceSplitTerminalPortGeometry
import LeanTrominoes.PlanarThreeSATGadgets

/-!
# Compass-terminal certificates for the fixed planar 3SAT gadgets

Before occurrence splitting, the Figure 8 gadgets may have variables of
degree greater than four and therefore need not admit an orthogonal incidence
drawing.  Their direct clause-to-variable segments nevertheless carry the
rotation system used by the split.

This file packages the finite property that every such direct incidence has
one of the eight permitted terminal directions and verifies it exhaustively
for both fixed Figure 8 templates.  Separation of collinear incidences is
deliberately not required: stable angular sorting assigns those occurrences
adjacent, distinct split ports.
-/

namespace LeanTrominoes
namespace PlanarThreeSAT

open PeriodicEightOccurrenceSplit
open PeriodicThreeSATThree

namespace EmbeddedCNFIncidenceDrawing

/-- Every genuine route has a nonzero terminal ray on an axis or a
45-degree diagonal. -/
def TerminalPortsValid
    {Variable : Type*}
    (drawing : EmbeddedCNFIncidenceDrawing Variable) : Prop :=
  ∀ index : Fin drawing.incidences.length,
    (terminalPort
      (routeTerminalVector
        (drawing.routeAt (drawing.incidenceAt index)))).isSome

instance {Variable : Type*}
    (drawing : EmbeddedCNFIncidenceDrawing Variable) :
    Decidable drawing.TerminalPortsValid := by
  unfold TerminalPortsValid incidenceAt incidences routeAt
  infer_instance

end EmbeddedCNFIncidenceDrawing

/-- Direct terminal rays of the fixed Figure 8(b) crossover. -/
def crossoverStraightIncidenceDrawing :
    EmbeddedCNFIncidenceDrawing CrossoverVariable :=
  straightIncidenceDrawing
    crossoverFormula CrossoverVariable.position

/-- All Figure 8(b) incidences use the eight compass ray classes.  Several
variables intentionally have repeated collinear rays; those are retained as
stable angular ties. -/
theorem crossoverStraightIncidenceDrawing_terminalPortsValid :
    crossoverStraightIncidenceDrawing.TerminalPortsValid := by
  native_decide

/-- Direct terminal rays of the fixed Figure 8(a) duplicator. -/
def duplicatorStraightIncidenceDrawing :
    EmbeddedCNFIncidenceDrawing DuplicatorVariable :=
  straightIncidenceDrawing
    duplicatorFormula DuplicatorVariable.position

/-- All Figure 8(a) incidences use the eight compass ray classes. -/
theorem duplicatorStraightIncidenceDrawing_terminalPortsValid :
    duplicatorStraightIncidenceDrawing.TerminalPortsValid := by
  native_decide

end PlanarThreeSAT
end LeanTrominoes
