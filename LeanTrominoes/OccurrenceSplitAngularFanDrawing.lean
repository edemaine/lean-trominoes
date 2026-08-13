/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.OccurrenceSplitRingCycleDrawing
import LeanTrominoes.PeriodicEightOccurrenceSplitAngularFanOrder
import Mathlib.Tactic.IntervalCases

/-!
# Certified angular subfans of Figure 7

An occurrence list of length `n ≤ 8` uses the first `n` ports in the
east-first angular enumeration.  The other Figure 7 copies remain in the
implication ring but receive no copied source incidence.

This file extracts exactly that finite local drawing: the selected spokes,
in angular-list order, followed by the complete separator-enhanced implication
ring.  All nine possible sizes are mechanically certified for exact endpoints,
orthogonality, and continuous planarity.
-/

namespace LeanTrominoes
namespace OccurrenceSplitRing

open PlanarThreeSAT
open PeriodicEightOccurrenceSplit

/-- The first `count` east-first compass ports.  Geometric uses impose
`count ≤ 8`; the definition remains total. -/
def angularFanPorts (count : Nat) : List Port :=
  (List.range count).map angularPortOfIndex

/-- Selected old incidences followed by the unchanged implication ring. -/
def angularFanFormula (count : Nat) :
    List (EmbeddedClause RingVertex) :=
  (angularFanPorts count).map spokeClause ++ cycleFormula

/-- Incidence routes parallel to `angularFanFormula`: selected Figure 7
spokes first, then all implication-ring routes. -/
def angularFanRoutes
    (count clauseIndex literalIndex : Nat) : List Cell :=
  if clauseIndex < (angularFanPorts count).length then
    if literalIndex = 0 then
      spokeRoute
        ((angularFanPorts count).getD clauseIndex .east)
    else
      []
  else if
      clauseIndex <
        (angularFanPorts count).length + cycleFormula.length then
    cycleRoutes
      (clauseIndex - (angularFanPorts count).length)
      literalIndex
  else
    []

/-- The local Figure 7 fan with exactly `count` copied source incidences. -/
def angularFanDrawing (count : Nat) :
    EmbeddedCNFIncidenceDrawing RingVertex where
  formula := angularFanFormula count
  variablePosition := ringVariablePosition
  routes := angularFanRoutes count

/-- Every fitting angular fan has exact endpoints, orthogonal routes, and
continuous planarity.  Because Figure 7 has eight slots, this is a finite
certificate over its nine possible fan sizes. -/
theorem angularFanDrawing_isValid
    (count : Nat) (fits : count ≤ 8) :
    (angularFanDrawing count).IsValid := by
  interval_cases count <;> native_decide

theorem angularFanDrawing_routesMatch
    (count : Nat) (fits : count ≤ 8) :
    (angularFanDrawing count).RoutesMatch :=
  (angularFanDrawing_isValid count fits).1

theorem angularFanDrawing_isOrthogonal
    (count : Nat) (fits : count ≤ 8) :
    (angularFanDrawing count).IsOrthogonal :=
  (angularFanDrawing_isValid count fits).2.1

theorem angularFanDrawing_isPlanar
    (count : Nat) (fits : count ≤ 8) :
    (angularFanDrawing count).IsPlanar :=
  (angularFanDrawing_isValid count fits).2.2

end OccurrenceSplitRing
end LeanTrominoes
