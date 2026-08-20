/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicPlanarOneInThreeToThreeDMVariableRibbonFanDataEncoding
import LeanTrominoes.PeriodicPlanarOneInThreeToThreeDMVariableSiteTripleEncoding
import LeanTrominoes.OrthogonalDrawing

/-! # Computability of finite variable-site routes -/

noncomputable section

namespace LeanTrominoes
namespace PeriodicPlanarOneInThreeToThreeDM

open Gadget PlanarThreeDM

/-- Proof-free totalization of the dependent variable-site route table.
Malformed triples use the empty route; every assembled incidence supplies the
matching branch. -/
def variableSiteRouteData
    (data : VariableRibbonFanData)
    (triple : VariableSiteTriple)
    (color : WireColor) : List Cell :=
  if matching : triple.MatchesKind data.count data.kind then
    variableSiteRoute data.count data.kind data.polarity
      ⟨triple, matching⟩ color
  else
    []

/-- On a matching triple, the proof-free route is exactly the dependent route
used by the semantic drawing. -/
theorem variableSiteRouteData_eq
    (data : VariableRibbonFanData)
    (triple : VariableSiteTriple)
    (color : WireColor)
    (matching : triple.MatchesKind data.count data.kind) :
    variableSiteRouteData data triple color =
      variableSiteRoute data.count data.kind data.polarity
        ⟨triple, matching⟩ color := by
  simp [variableSiteRouteData, matching]

/-- The totalized variable-site route is a fixed finite lookup table. -/
theorem variableSiteRouteData_primrec :
    Primrec
      (fun input :
          VariableRibbonFanData × (VariableSiteTriple × WireColor) =>
        variableSiteRouteData input.1 input.2.1 input.2.2) :=
  Computability.finiteDomain_primrec _

end PeriodicPlanarOneInThreeToThreeDM
end LeanTrominoes
