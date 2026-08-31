/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalClauseFamilyStarts

/-! # Tagged-link presentation of direct-source final carrier clauses -/

noncomputable section

namespace LeanTrominoes.PeriodicCNFStripReduction

open PeriodicOrthocrossing
open PlanarThreeSAT

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

noncomputable local instance directFinalCarrierTaggedLinkDataStackFintype
    (stack : decider.tm.K) : Fintype (decider.tm.Γ stack) :=
  decider.stackAlphabetFinite stack

local instance directFinalCarrierTaggedLinkDataVariableDecidableEq :
    DecidableEq Variable :=
  PeriodicThreeSATThree.fiveFamilyNormalizedThreeOccurrenceDecidableEq

/-- Raw retained carrier links, tagged by implication direction and by their
global positions in the final five-family clause presentation. -/
def directSourceFinalCarrierTaggedLinks
    (symbols : List encoding.Γ) :
    List ((EqualityLink CarrierNode × Bool) × Nat) :=
  ((retainedDrawingCompleteCarrierLinks
      (directSourceFinalNormalizedFormula decider symbols).incidenceGraph).product
        [true, false]).zipIdx
    (directSourceFinalCarrierStart decider symbols)

end LeanTrominoes.PeriodicCNFStripReduction

end
