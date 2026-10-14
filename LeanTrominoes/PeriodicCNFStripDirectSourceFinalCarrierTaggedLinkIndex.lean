/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFProgramSource
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalCarrierTaggedLinkSemantics

/-! # Generic indices of direct-source final carrier links -/

noncomputable section

namespace LeanTrominoes.PeriodicCNFStripReduction

open PeriodicEightOccurrenceSplit
open PeriodicOrthocrossing
open PlanarThreeSAT

variable {Input : Type}
variable {encoding : _root_.LeanTrominoes.FiniteEncoding Input}
variable {language : Input → Prop}
variable (decider : PeriodicCNF.ProgramSource encoding language)


local instance directFinalCarrierTaggedLinkIndexBaseDecidableEq :
    DecidableEq (ThreeCNFVariable Nat) :=
  directSourceFinalStructuralBaseDecidableEq

/-- A member of the direct tagged-link presentation satisfies the generic
final-carrier global-index relation. -/
theorem directSourceFinalCarrierTaggedLink_indexed
    (symbols : List encoding.Γ)
    (tagged : (EqualityLink CarrierNode × Bool) × Nat)
    (taggedMember :
      tagged ∈ directSourceFinalCarrierTaggedLinks decider symbols) :
    finalCarrierTaggedLinkIndexed
      (directThreeCNFSourceFormula decider symbols)
      tagged.1 tagged.2 := by
  apply finalCarrierTaggedLinkIndexed_of_mem
  rw [← directSourceFinalCarrierTaggedLinks_eq_generic decider symbols]
  exact taggedMember

end LeanTrominoes.PeriodicCNFStripReduction

end
