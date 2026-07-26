import LeanTrominoes.PeriodicCNFPlanarFormula
import LeanTrominoes.PlanarThreeSATOcurrences

/-!
# Occurrence bounds in the periodic planar-SAT construction

The fixed Figure 8 gadgets have small local occurrence bounds, but the full
planarizer shares carrier variables between crossover, equality-wire, bend,
and vertex components.  This file develops the componentwise accounting
needed to show that the routed periodic source fits the eight ports of
Figure 7.
-/

namespace LeanTrominoes
namespace PeriodicOrthocrossing

open PlanarThreeSAT

/-- The combined site-and-template-variable map used by the carrier-node
crossover family. -/
def carrierNodeScopedCrossoverVariableMap
    (input : CrossingRecord × CrossoverVariable) :
    Sum CarrierNode (CrossingRecord × CrossoverInternal) :=
  scopedCrossoverVariableMap input.1
    (carrierNodeCrossingPorts input.1) input.2

/-- Different crossover sites and different roles name different variables
in the carrier-node crossover family. -/
theorem carrierNodeScopedCrossoverVariableMap_injective :
    Function.Injective carrierNodeScopedCrossoverVariableMap := by
  rintro ⟨firstSite, firstVariable⟩
    ⟨secondSite, secondVariable⟩ equal
  cases firstVariable <;>
    cases secondVariable <;>
      simp [carrierNodeScopedCrossoverVariableMap,
        scopedCrossoverVariableMap,
        carrierNodeCrossingPorts] at equal ⊢
  all_goals exact equal

/-- The complete family of fixed crossover gadgets retains the local
eight-occurrence bound. -/
theorem drawingCarrierNodeCrossoverFormula_occurrencesAtMostEight
    {Vertex : Type*} [DecidableEq Vertex]
    (graph : PeriodicGraph Vertex) :
    FormulaOccurrencesAtMost 8
      (drawingCarrierNodeCrossoverFormula graph) := by
  simpa [drawingCarrierNodeCrossoverFormula,
    crossoverFamily, scopedCrossoverInstance,
    carrierNodeScopedCrossoverVariableMap] using
    instantiateFamily_occurrencesAtMost_of_jointly_injective
      8 (orientedCrossings graph)
      (fun site =>
        scopedCrossoverVariableMap site
          (carrierNodeCrossingPorts site))
      crossingMacroOrigin 1 crossoverFormula
      (orientedCrossings_nodup graph)
      carrierNodeScopedCrossoverVariableMap_injective
      crossoverFormula_occurrencesAtMostEight

end PeriodicOrthocrossing
end LeanTrominoes
