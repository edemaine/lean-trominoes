/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.RetainedAngularFanFinalCarrierTaggedLinkFamilyData

/-! # Indexed tagged links for the final carrier family -/

namespace LeanTrominoes
namespace PeriodicEightOccurrenceSplit

open PeriodicCNF
open PeriodicOrthocrossing PlanarThreeSAT

/-- The global final-carrier index relation between a tagged semantic link
and its clause position after the crossover prefix. -/
structure finalCarrierTaggedLinkIndexed
    {Variable : Type} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (taggedLink : EqualityLink CarrierNode × Bool)
    (clauseIndex : Nat) : Prop where
  member : (taggedLink, clauseIndex) ∈ finalCarrierTaggedLinks source

/-- Membership in the named generic carrier list constructs the corresponding
global-index certificate. -/
theorem finalCarrierTaggedLinkIndexed_of_mem
    {Variable : Type} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (taggedLink : EqualityLink CarrierNode × Bool)
    (clauseIndex : Nat)
    (member : (taggedLink, clauseIndex) ∈ finalCarrierTaggedLinks source) :
    finalCarrierTaggedLinkIndexed source taggedLink clauseIndex := by
  constructor
  exact member

end PeriodicEightOccurrenceSplit
end LeanTrominoes
