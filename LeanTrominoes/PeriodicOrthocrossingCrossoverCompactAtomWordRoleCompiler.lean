/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingCrossoverCompactAtomWordBoundaryCompiler
import LeanTrominoes.PeriodicOrthocrossingCrossoverCompactAtomWordInternalCompiler
import LeanTrominoes.TM2CompositionMachine

/-! # One-role crossover compact atom-word decoration -/

noncomputable section

namespace LeanTrominoes.PeriodicOrthocrossing
namespace CrossoverCompactAtomWords

open Computability Turing
open PeriodicCNFStripReduction.DirectSourceFinalAtomWords
open PlanarThreeSAT

def roleTokens (role : CrossoverVariable)
    (source : List DelimitedBinaryWords.Token) :
    List DelimitedBinaryWords.Token :=
  match internal? role with
  | none => boundaryTokens (sourceSide role) source
  | some internal =>
      appendSuffixTokens (crossoverInternalWord internal)
        (internalTokens source)

opaque roleTokensComputableInPolyTime
    (role : CrossoverVariable) :
    TM2ComputableInPolyTime id id (roleTokens role) := by
  unfold roleTokens
  cases internalEq : internal? role with
  | none =>
      change TM2ComputableInPolyTime id id
        (boundaryTokens (sourceSide role))
      exact boundaryTokensComputableInPolyTime _
  | some internal =>
      change TM2ComputableInPolyTime id id
        (fun source =>
          appendSuffixTokens (crossoverInternalWord internal)
            (internalTokens source))
      exact TM2CompositionMachine.computableInPolyTime
        internalTokensComputableInPolyTime
        (appendSuffixTokensComputableInPolyTime
          (crossoverInternalWord internal))

@[simp] theorem roleTokens_wordTokens
    (role : CrossoverVariable) (guarded : List Bool) :
    roleTokens role (DelimitedBinaryWords.wordTokens guarded) =
      DelimitedBinaryWords.encode ⟨word role guarded⟩ := by
  unfold roleTokens
  cases internalEq : internal? role with
  | none =>
      change boundaryTokens (sourceSide role)
          (DelimitedBinaryWords.wordTokens guarded) = _
      rw [boundaryTokens_wordTokens]
      cases guarded with
      | nil => rfl
      | cons active bits =>
          cases active <;>
            simp [word, internalEq, boundaryWord]
  | some internal =>
      change appendSuffixTokens (crossoverInternalWord internal)
          (internalTokens (DelimitedBinaryWords.wordTokens guarded)) = _
      rw [internalTokens_wordTokens, appendSuffixTokens_encode]
      cases guarded with
      | nil => rfl
      | cons active bits =>
          cases active <;>
            simp [word, internalEq, internalBaseWord]

end CrossoverCompactAtomWords
end LeanTrominoes.PeriodicOrthocrossing

end
