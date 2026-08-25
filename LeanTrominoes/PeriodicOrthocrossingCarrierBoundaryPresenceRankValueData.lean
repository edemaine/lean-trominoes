/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingCarrierNodeRankDatumData

/-! # Boundary-presence values of carrier nodes and rank data -/

namespace LeanTrominoes.PeriodicOrthocrossing
namespace CarrierBoundaryPresenceField

/-- Terminal nodes contribute zero and crossing-boundary nodes contribute
one to the boundary-presence rank field. -/
def nodeValue : CarrierNode → Nat
  | .terminal _ => 0
  | .boundary _ => 1

/-- Inactive padded slots contribute zero. -/
def optionalNodeValue : Option CarrierNode → Nat
  | none => 0
  | some node => nodeValue node

/-- The boundary-presence field read from compiler-facing rank data. -/
def rankValue (datum : CarrierNodeRankDatum) : Nat :=
  match datum.boundaryCrossing with
  | none => 0
  | some _ => 1

end CarrierBoundaryPresenceField
end LeanTrominoes.PeriodicOrthocrossing
