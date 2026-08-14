/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNF

/-! # Source-side complement refined-route input computability -/

noncomputable section

namespace LeanTrominoes
namespace PeriodicOneInThreePolarityNormalizationRouteSubdivision

def complementSecondSourceRouteInput {Input Metadata Variable : Type*}
    (sourceClauseIndex : Metadata → Nat)
    (input : (Input × Metadata) ×
      (Nat × PeriodicLiteral Variable)) : (Input × Nat) × Nat :=
  ((input.1.1, sourceClauseIndex input.1.2), input.2.1)

theorem complementSecondSourceRouteInput_primrec
    {Input Metadata Variable : Type*}
    [Primcodable Input] [Primcodable Metadata] [Primcodable Variable]
    (sourceClauseIndex : Metadata → Nat)
    (sourceClauseIndexPrimrec : Primrec sourceClauseIndex) :
    Primrec (complementSecondSourceRouteInput
      (Input := Input) (Variable := Variable) sourceClauseIndex) := by
  have clauseIndex : Primrec fun input :
      (Input × Metadata) × (Nat × PeriodicLiteral Variable) =>
      sourceClauseIndex input.1.2 :=
    sourceClauseIndexPrimrec.comp (Primrec.snd.comp Primrec.fst)
  exact Primrec.pair
    (Primrec.pair (Primrec.fst.comp Primrec.fst) clauseIndex)
    (Primrec.fst.comp Primrec.snd)

end PeriodicOneInThreePolarityNormalizationRouteSubdivision
end LeanTrominoes
