/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFFormulaShapeRetainedPlanarMetadataBendNormalizedFamilyDeduplication
import LeanTrominoes.PeriodicEqualityNormalizedClauseAtomWordSemantics

/-! # Atom-word column of the canonical bend family -/

namespace LeanTrominoes
namespace PeriodicCNF
namespace FormulaShapeRetainedPlanarMetadataDirection

open PeriodicOrthocrossing

/-- Base bend clauses flatten to the repeated endpoint-word block of each
canonical untranslated normalized bend link. -/
theorem baseBendNormalizedClauses_atomWords
    {Variable : Type} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (word : WrappedPeriodicPlanarSATVariable Variable → List Bool) :
    (baseBendNormalizedClauses source).flatMap
        (fun clause => clause.map fun literal => word literal.atom) =
      (baseBendNormalizedLinks source).flatMap fun link =>
        [word link.first, word link.second,
          word link.first, word link.second] := by
  unfold baseBendNormalizedClauses
  exact PeriodicEquality.normalizedClauses_atomWords
    word (baseBendNormalizedLinks source)

end FormulaShapeRetainedPlanarMetadataDirection
end PeriodicCNF
end LeanTrominoes
