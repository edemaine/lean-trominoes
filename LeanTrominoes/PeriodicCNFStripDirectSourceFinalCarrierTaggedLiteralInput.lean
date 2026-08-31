/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalCarrierTaggedLinkInput
import LeanTrominoes.RetainedAngularFanFinalCarrierTaggedLiteralInputData

/-! # Evidence selecting direct-source final carrier literals -/

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

noncomputable local instance directFinalCarrierTaggedInputStackFintype
    (stack : decider.tm.K) : Fintype (decider.tm.Γ stack) :=
  decider.stackAlphabetFinite stack

local instance directFinalCarrierTaggedInputBaseDecidableEq :
    DecidableEq (ThreeCNFVariable Nat) :=
  directSourceFinalStructuralBaseDecidableEq

local instance directFinalCarrierTaggedInputVariableDecidableEq :
    DecidableEq Variable :=
  directSourceFinalStructuralVariableDecidableEq

/-- Collect the direct-source shape facts, global carrier index, and literal
membership needed by the generic final-carrier occurrence constructor. -/
noncomputable def directSourceFinalCarrierTaggedLiteralInput
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
          tagged.1).zipIdx) :
    FinalCarrierTaggedLiteralInput
      (directThreeCNFSourceFormula decider symbols)
      tagged.1 tagged.2 literal literalIndex where
  linkInput :=
    directSourceFinalCarrierTaggedLinkInput
      decider symbols tagged taggedMember
  literalMember := literalMember

end LeanTrominoes.PeriodicCNFStripReduction

end
