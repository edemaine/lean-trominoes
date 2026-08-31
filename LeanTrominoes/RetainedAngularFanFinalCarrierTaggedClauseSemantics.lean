/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFFormulaShapeRetainedPlanarMetadataNormalizedCarrierClauseDescriptorLookup
import LeanTrominoes.RetainedAngularFanFinalCarrierTaggedLinkFamilyData

/-! # Indexed clauses of named final-carrier links -/

namespace LeanTrominoes.PeriodicEightOccurrenceSplit

open PeriodicCNF
open PeriodicCNF.FormulaShapeRetainedPlanarMetadataDirection
open PeriodicThreeSATThree

local instance finalCarrierTaggedClauseThreeOccurrenceDecidableEq
    {Variable : Type} [DecidableEq Variable] :
    DecidableEq (ThreeOccurrenceVariable Variable) :=
  fiveFamilyNormalizedThreeOccurrenceDecidableEq

/-- Indexing the generic carrier clause family is the same as mapping clause
normalization over the explicitly indexed tagged-link family. -/
theorem formulaCarrierMetadataNormalizedClauses_zipIdx_eq_taggedLinksFrom
    {Variable : Type} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (start : Nat) :
    (formulaCarrierMetadataNormalizedClauses source).zipIdx start =
      (finalCarrierTaggedLinksFrom source start).map
        (fun tagged =>
          (normalizedCarrierClauseAt
            (PeriodicThreeSATThree.formula source) tagged.1,
            tagged.2)) := by
  unfold formulaCarrierMetadataNormalizedClauses
    finalCarrierTaggedLinksFrom
    finalCarrierTaggedLinkValues
  rw [carrierMetadataNormalizedClauses_eq_map_taggedLinks,
    List.zipIdx_map]
  rfl

end LeanTrominoes.PeriodicEightOccurrenceSplit
