/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalCarrierTaggedLiteralOccurrence
import LeanTrominoes.RetainedAngularFanFinalCarrierTaggedLiteralOccurrenceDirections

/-! # Exact route directions of direct-source final carrier literals -/

noncomputable section

namespace LeanTrominoes.PeriodicCNFStripReduction

open PeriodicCNF
open PeriodicCNF.FormulaShapeRetainedPlanarMetadataDirection
open PeriodicEightOccurrenceSplit
open PeriodicOrthocrossing
open PlanarThreeSAT

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

noncomputable local instance directFinalCarrierTaggedLiteralStackFintype
    (stack : decider.tm.K) : Fintype (decider.tm.Γ stack) :=
  decider.stackAlphabetFinite stack

local instance directFinalCarrierTaggedLiteralBaseDecidableEq :
    DecidableEq (ThreeCNFVariable Nat) :=
  directSourceFinalStructuralBaseDecidableEq

local instance directFinalCarrierTaggedLiteralVariableDecidableEq :
    DecidableEq Variable :=
  directSourceFinalStructuralVariableDecidableEq

/-- A literal selected from an indexed direct-source carrier implication has
the exact public route directions prescribed by the finite carrier model. -/
theorem directSourceFinalCarrierTaggedLiteral_publicDirections
    (symbols : List encoding.Γ)
    (tagged : (EqualityLink CarrierNode × Bool) × Nat)
    (taggedMember :
      tagged ∈ directSourceFinalCarrierTaggedLinks decider symbols)
    (literal : PeriodicLiteral (WrappedPeriodicPlanarSATVariable Variable))
    (literalIndex : Fin 2)
    (literalMember :
      (literal, literalIndex.val) ∈
        (normalizedCarrierClauseAt
          (PeriodicThreeSATThree.formula
            (directThreeCNFSourceFormula decider symbols))
          tagged.1).zipIdx)
    (nextSlice : Bool) :
    FinalCarrierTaggedLiteralPublicDirections
      (directThreeCNFSourceFormula decider symbols)
      tagged.1 tagged.2 literal literalIndex nextSlice := by
  exact
    (directSourceFinalCarrierTaggedLiteralOccurrence
      decider symbols tagged taggedMember literal literalIndex
      literalMember).publicDirections nextSlice

end LeanTrominoes.PeriodicCNFStripReduction

end
