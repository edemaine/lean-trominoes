/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalCarrierTaggedLiteralInput
import LeanTrominoes.RetainedAngularFanFinalCarrierTaggedLiteralInputOccurrence

/-! # Matched direct-source final carrier literals -/

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

noncomputable local instance directFinalCarrierTaggedOccurrenceStackFintype
    (stack : decider.tm.K) : Fintype (decider.tm.Γ stack) :=
  decider.stackAlphabetFinite stack

local instance directFinalCarrierTaggedOccurrenceBaseDecidableEq :
    DecidableEq (ThreeCNFVariable Nat) :=
  directSourceFinalStructuralBaseDecidableEq

local instance directFinalCarrierTaggedOccurrenceVariableDecidableEq :
    DecidableEq Variable :=
  directSourceFinalStructuralVariableDecidableEq

/-- Package a literal of an indexed direct-source carrier implication as its
matched final occurrence. -/
noncomputable def directSourceFinalCarrierTaggedLiteralOccurrence
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
    FinalCarrierTaggedLiteralOccurrence
      (directThreeCNFSourceFormula decider symbols)
      tagged.1 tagged.2 literal literalIndex :=
  (directSourceFinalCarrierTaggedLiteralInput
    decider symbols tagged taggedMember literal literalIndex
    literalMember).occurrence

end LeanTrominoes.PeriodicCNFStripReduction

end
