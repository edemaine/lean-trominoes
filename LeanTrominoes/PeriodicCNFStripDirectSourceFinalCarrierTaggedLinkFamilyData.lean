/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalCarrierStartData
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalCarrierStartGenericData
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalCarrierTaggedLinkData
import LeanTrominoes.RetainedAngularFanFinalCarrierLookupSemantics

/-! # Named presentations of direct-source final carrier links -/

noncomputable section

namespace LeanTrominoes.PeriodicCNFStripReduction

open PeriodicEightOccurrenceSplit
open PeriodicOrthocrossing
open PeriodicThreeSATThree
open PlanarThreeSAT

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

noncomputable local instance directFinalCarrierTaggedLinkFamilyDataStackFintype
    (stack : decider.tm.K) : Fintype (decider.tm.Γ stack) :=
  decider.stackAlphabetFinite stack

local instance directFinalCarrierTaggedLinkFamilyDataBaseDecidableEq :
    DecidableEq (ThreeCNFVariable Nat) :=
  directSourceFinalStructuralBaseDecidableEq

local instance directFinalCarrierTaggedLinkFamilyDataVariableDecidableEq :
    DecidableEq Variable :=
  directSourceFinalStructuralVariableDecidableEq

/-- Generic final-carrier links of the direct source as a named function of
the base equality and global start. -/
def directSourceFinalCarrierTaggedLinksFamily
    (symbols : List encoding.Γ)
    (equality : DecidableEq (ThreeCNFVariable Nat))
    (start : Nat) :
    List ((EqualityLink CarrierNode × Bool) × Nat) :=
  @finalCarrierTaggedLinksFrom (ThreeCNFVariable Nat) equality
    (directThreeCNFSourceFormula decider symbols) start

/-- Generic carrier links of the direct source at the public family start. -/
def directSourceFinalCarrierOriginalTaggedLinks
    (symbols : List encoding.Γ) :
    List ((EqualityLink CarrierNode × Bool) × Nat) :=
  directSourceFinalCarrierTaggedLinksFamily decider symbols
    directSourceFinalOriginalBaseDecidableEq
    (directSourceFinalCarrierStart decider symbols)

/-- Direct carrier links after aligning the base equality, but before
transporting the public start. -/
def directSourceFinalCarrierEqualityAlignedTaggedLinks
    (symbols : List encoding.Γ) :
    List ((EqualityLink CarrierNode × Bool) × Nat) :=
  directSourceFinalCarrierTaggedLinksFamily decider symbols
    directSourceFinalStructuralBaseDecidableEq
    (directSourceFinalCarrierStart decider symbols)

/-- Generic carrier links of the direct source at the structural crossover
prefix length. -/
def directSourceFinalCarrierStructuralTaggedLinks
    (symbols : List encoding.Γ) :
    List ((EqualityLink CarrierNode × Bool) × Nat) :=
  directSourceFinalCarrierTaggedLinksFamily decider symbols
    directSourceFinalStructuralBaseDecidableEq
    (directSourceFinalCarrierStructuralStart decider symbols)

/-- Direct carrier links at the generic named structural start. -/
def directSourceFinalCarrierGenericTaggedLinks
    (symbols : List encoding.Γ) :
    List ((EqualityLink CarrierNode × Bool) × Nat) :=
  directSourceFinalCarrierTaggedLinksFamily decider symbols
    directSourceFinalStructuralBaseDecidableEq
    (directSourceFinalCarrierGenericStructuralStart decider symbols)

/-- Opaque certificate exposing the direct tagged-link definition through the
explicit-start generic carrier family. -/
structure DirectSourceFinalCarrierTaggedLinksUnfolded
    (symbols : List encoding.Γ) : Prop where
  eq : directSourceFinalCarrierTaggedLinks decider symbols =
    directSourceFinalCarrierOriginalTaggedLinks decider symbols

/-- Opaque certificate aligning the original and structural base equalities. -/
structure DirectSourceFinalCarrierTaggedLinksEqualityTransport
    (symbols : List encoding.Γ) : Prop where
  eq : directSourceFinalCarrierOriginalTaggedLinks decider symbols =
    directSourceFinalCarrierEqualityAlignedTaggedLinks decider symbols

/-- Opaque certificate transporting the equality-aligned carrier list from
its public start to the structural crossover-prefix start. -/
structure DirectSourceFinalCarrierTaggedLinksStartTransport
    (symbols : List encoding.Γ) : Prop where
  eq : directSourceFinalCarrierEqualityAlignedTaggedLinks decider symbols =
    directSourceFinalCarrierStructuralTaggedLinks decider symbols

/-- Opaque certificate transporting the direct structural start to the generic
named carrier start. -/
structure DirectSourceFinalCarrierTaggedLinksGenericStartTransport
    (symbols : List encoding.Γ) : Prop where
  eq : directSourceFinalCarrierStructuralTaggedLinks decider symbols =
    directSourceFinalCarrierGenericTaggedLinks decider symbols

/-- Opaque certificate identifying the structural direct list with the
generic carrier family. -/
structure DirectSourceFinalCarrierTaggedLinksGeneric
    (symbols : List encoding.Γ) : Prop where
  eq : directSourceFinalCarrierGenericTaggedLinks decider symbols =
    @finalCarrierTaggedLinks (ThreeCNFVariable Nat)
      directSourceFinalStructuralBaseDecidableEq
      (directThreeCNFSourceFormula decider symbols)

end LeanTrominoes.PeriodicCNFStripReduction

end
