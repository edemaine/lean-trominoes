/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNF

/-! # Complement raw-route branch-selection computability -/

noncomputable section

namespace LeanTrominoes
namespace PeriodicOneInThreePolarityNormalizationRouteSubdivision

def selectComplementRawRoute {Input : Type*}
    (first second : Input → List Cell) (input : Input × Nat) : List Cell :=
  if input.2 = 0 then first input.1
  else if input.2 = 1 then second input.1
  else []

theorem selectComplementRawRoute_primrec
    {Input : Type*} [Primcodable Input]
    (first second : Input → List Cell)
    (firstPrimrec : Primrec first) (secondPrimrec : Primrec second) :
    Primrec (selectComplementRawRoute first second) := by
  have firstIndex : PrimrecPred fun input : Input × Nat => input.2 = 0 :=
    Primrec.eq.comp Primrec.snd (Primrec.const 0)
  have secondIndex : PrimrecPred fun input : Input × Nat => input.2 = 1 :=
    Primrec.eq.comp Primrec.snd (Primrec.const 1)
  exact (Primrec.ite firstIndex (firstPrimrec.comp Primrec.fst)
    (Primrec.ite secondIndex (secondPrimrec.comp Primrec.fst)
      (Primrec.const []))).of_eq fun _ => rfl

end PeriodicOneInThreePolarityNormalizationRouteSubdivision
end LeanTrominoes
