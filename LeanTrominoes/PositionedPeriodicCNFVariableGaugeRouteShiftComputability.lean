/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PositionedPeriodicCNFVariableGaugeDrawing
import LeanTrominoes.PositionedPeriodicCNFVariableGaugeRouteAnchorsComputability

/-! # Variable-gauge canonical route-shift computability -/

noncomputable section

namespace LeanTrominoes
namespace PositionedPeriodicCNF

theorem variableGaugeCanonicalRouteShift_primrec
    {Input Variable : Type*} [Primcodable Input] [Primcodable Variable]
    (gauge : Input → Variable → Cell)
    (clause : Input → PositionedPeriodicClause Variable)
    (gaugePrimrec : Primrec fun input : Input × Variable =>
      gauge input.1 input.2)
    (clausePrimrec : Primrec clause) :
    Primrec fun input =>
      variableGaugeCanonicalRouteShift (gauge input) (clause input) := by
  have anchors := variableGaugeRouteAnchors_primrec gauge clause
    gaugePrimrec clausePrimrec
  exact (Computability.cell_sub_primrec.comp
    (Primrec.fst.comp anchors) (Primrec.snd.comp anchors)).of_eq
      fun _ => rfl

end PositionedPeriodicCNF
end LeanTrominoes
