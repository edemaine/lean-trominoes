/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PositionedPeriodicCNFVariableGaugeRouteShiftComputability

/-! # Variable-gauge physical route-translation computability -/

noncomputable section

namespace LeanTrominoes
namespace PositionedPeriodicCNF

def variableGaugeCanonicalRouteTranslation {Input Variable : Type*}
    (period : Input → Nat)
    (gauge : Input → Variable → Cell)
    (clause : Input → PositionedPeriodicClause Variable)
    (input : Input) : Cell :=
  ({ period := period input
     position := fun _ : Variable => (0, 0) } :
    PeriodicVariablePlacement Variable).translation
      (variableGaugeCanonicalRouteShift (gauge input) (clause input))

theorem variableGaugeCanonicalRouteTranslation_primrec
    {Input Variable : Type*} [Primcodable Input] [Primcodable Variable]
    (period : Input → Nat)
    (gauge : Input → Variable → Cell)
    (clause : Input → PositionedPeriodicClause Variable)
    (periodPrimrec : Primrec period)
    (gaugePrimrec : Primrec fun input : Input × Variable =>
      gauge input.1 input.2)
    (clausePrimrec : Primrec clause) :
    Primrec (variableGaugeCanonicalRouteTranslation
      period gauge clause) := by
  exact (Computability.cell_scale_primrec.comp
    (Computability.int_ofNat_primrec.comp periodPrimrec)
    (variableGaugeCanonicalRouteShift_primrec gauge clause
      gaugePrimrec clausePrimrec)).of_eq fun _ => rfl

end PositionedPeriodicCNF
end LeanTrominoes
