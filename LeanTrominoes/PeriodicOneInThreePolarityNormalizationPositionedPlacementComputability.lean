/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOneInThreePolarityNormalizationPositionedComputability

/-!
# Placement computability for positioned polarity normalization

The companion placement is function-valued, so its executable interface is
certified through its finite period and pointwise position queries.
-/

noncomputable section

namespace LeanTrominoes
namespace PeriodicOneInThreePolarityNormalizationPositioned

/-- The normalized placement retains the source period. -/
theorem placement_period_primrec
    {Input Variable : Type*} [Primcodable Input]
    (sourcePlacement : Input → PeriodicVariablePlacement Variable)
    (periodPrimrec : Primrec fun input =>
      (sourcePlacement input).period) :
    Primrec fun input =>
      (placement (sourcePlacement input)
        { freshVariable := fun _ => (0, 0)
          complementClause := fun _ => (0, 0) }).period := by
  exact periodPrimrec.of_eq fun _ => rfl

/-- Normalized variable positions are primitive recursive from the original
position query and the selected fresh-variable position query. -/
theorem placement_position_primrec
    {Input Variable : Type*} [Primcodable Input] [Primcodable Variable]
    (sourcePlacement : Input → PeriodicVariablePlacement Variable)
    (freshPosition : Input → FreshOccurrence Variable → Cell)
    (sourcePositionPrimrec : Primrec fun input : Input × Variable =>
      (sourcePlacement input.1).position input.2)
    (freshPositionPrimrec :
      Primrec fun input : Input × FreshOccurrence Variable =>
        freshPosition input.1 input.2) :
    Primrec fun input : Input × PolarityNormalizedVariable Variable =>
      (placement (sourcePlacement input.1)
        { freshVariable := freshPosition input.1
          complementClause := fun _ => (0, 0) }).position input.2 := by
  have original : Primrec₂ fun
      (input : Input × PolarityNormalizedVariable Variable)
      (atom : Variable) =>
      (sourcePlacement input.1).position atom := by
    change Primrec fun combined :
        (Input × PolarityNormalizedVariable Variable) × Variable =>
      (sourcePlacement combined.1.1).position combined.2
    exact sourcePositionPrimrec.comp
      (Primrec.pair (Primrec.fst.comp Primrec.fst) Primrec.snd)
  have fresh : Primrec₂ fun
      (input : Input × PolarityNormalizedVariable Variable)
      (occurrence : FreshOccurrence Variable) =>
      freshPosition input.1 occurrence := by
    change Primrec fun combined :
        (Input × PolarityNormalizedVariable Variable) ×
          FreshOccurrence Variable =>
      freshPosition combined.1.1 combined.2
    exact freshPositionPrimrec.comp
      (Primrec.pair (Primrec.fst.comp Primrec.fst) Primrec.snd)
  exact (Primrec.sumCasesOn Primrec.snd original fresh).of_eq
    fun input => by cases input.2 <;> rfl

end PeriodicOneInThreePolarityNormalizationPositioned
end LeanTrominoes
