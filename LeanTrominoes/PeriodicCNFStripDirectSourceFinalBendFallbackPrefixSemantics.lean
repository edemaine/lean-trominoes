/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.DelimitedRouteJoinSemantics
import LeanTrominoes.PeriodicCNFFormulaShapeRetainedPlanarMetadataAffineBendRoutePrefixDirectionStreamSemantics
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalBendFallbackPrefixCompiler
import LeanTrominoes.PeriodicCNFStripDirectSourceFormulaForwardLocalNamed
import LeanTrominoes.PeriodicCNFStripDirectSourceFormulaIncidenceDegree
import LeanTrominoes.PeriodicCNFStripDirectSourceRouteDescriptorPairFieldTagSemantics

/-! # Semantic scaled bend-prefix words of the direct source -/

noncomputable section

namespace LeanTrominoes.PeriodicCNFStripReduction

open PeriodicCNF PeriodicOrthocrossing
open PeriodicCNF.FormulaShapeRetainedPlanarMetadataDirection

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

noncomputable local instance directFinalBendFallbackPrefixSemanticsStackFintype
    (stack : decider.tm.K) : Fintype (decider.tm.Γ stack) :=
  decider.stackAlphabetFinite stack

local instance directFinalBendFallbackPrefixSemanticsVariableDecidableEq :
    DecidableEq Variable :=
  directSourceVariableDecidableEq

/-- The four undelimited, source-clearance-scaled prefix words of every
semantic untranslated bend, in numeric route and within-route bend order. -/
def directSourceFinalBendFallbackPrefixWords
    (symbols : List encoding.Γ) : List (List AxisDirection) :=
  (numericRouteDescriptors
    (directSourceFormula decider symbols)).flatMap fun descriptor =>
      (routeBends descriptor.edgeIndex (0, 0) descriptor.route).flatMap
        fun routeBend =>
          [Gadget.repeatDirections 1152
              (bendRoutePrefixDirections
                routeBend.incomingPort routeBend.outgoingPort 0 0),
            Gadget.repeatDirections 1152
              (bendRoutePrefixDirections
                routeBend.incomingPort routeBend.outgoingPort 0 1),
            Gadget.repeatDirections 1152
              (bendRoutePrefixDirections
                routeBend.incomingPort routeBend.outgoingPort 1 0),
            Gadget.repeatDirections 1152
              (bendRoutePrefixDirections
                routeBend.incomingPort routeBend.outgoingPort 1 1)]

@[simp] theorem directSourceFinalBendFallbackPrefixWords_length
    (symbols : List encoding.Γ) :
    (directSourceFinalBendFallbackPrefixWords decider symbols).length =
      4 * ((numericRouteDescriptors
        (directSourceFormula decider symbols)).flatMap fun descriptor =>
          routeBends descriptor.edgeIndex (0, 0) descriptor.route).length := by
  unfold directSourceFinalBendFallbackPrefixWords
  let descriptors := numericRouteDescriptors
    (directSourceFormula decider symbols)
  change
    (descriptors.flatMap fun descriptor =>
      (routeBends descriptor.edgeIndex (0, 0) descriptor.route).flatMap
        fun routeBend =>
          [Gadget.repeatDirections 1152
              (bendRoutePrefixDirections
                routeBend.incomingPort routeBend.outgoingPort 0 0),
            Gadget.repeatDirections 1152
              (bendRoutePrefixDirections
                routeBend.incomingPort routeBend.outgoingPort 0 1),
            Gadget.repeatDirections 1152
              (bendRoutePrefixDirections
                routeBend.incomingPort routeBend.outgoingPort 1 0),
            Gadget.repeatDirections 1152
              (bendRoutePrefixDirections
                routeBend.incomingPort routeBend.outgoingPort 1 1)]).length =
      4 * (descriptors.flatMap fun descriptor =>
        routeBends descriptor.edgeIndex (0, 0) descriptor.route).length
  induction descriptors with
  | nil => rfl
  | cons descriptor descriptors induction =>
      have blockLength :
          ((routeBends descriptor.edgeIndex (0, 0)
            descriptor.route).flatMap fun routeBend =>
              [Gadget.repeatDirections 1152
                  (bendRoutePrefixDirections
                    routeBend.incomingPort routeBend.outgoingPort 0 0),
                Gadget.repeatDirections 1152
                  (bendRoutePrefixDirections
                    routeBend.incomingPort routeBend.outgoingPort 0 1),
                Gadget.repeatDirections 1152
                  (bendRoutePrefixDirections
                    routeBend.incomingPort routeBend.outgoingPort 1 0),
                Gadget.repeatDirections 1152
                  (bendRoutePrefixDirections
                    routeBend.incomingPort routeBend.outgoingPort 1 1)]).length =
            4 * (routeBends descriptor.edgeIndex (0, 0)
              descriptor.route).length := by
        induction routeBends descriptor.edgeIndex (0, 0)
            descriptor.route with
        | nil => rfl
        | cons routeBend routeBends induction =>
            simp [induction]
            omega
      simp only [List.flatMap_cons, List.length_append]
      rw [blockLength, induction]
      omega

/-- Direct scaled bend-prefix compilation is exactly the four-prefix family
of every semantic untranslated bend. -/
theorem directSourceFinalBendFallbackPrefixDirections_eq
    (symbols : List encoding.Γ) :
    directSourceFinalBendFallbackPrefixDirections decider symbols =
      (directSourceFinalBendFallbackPrefixWords
        decider symbols).flatMap DelimitedRouteJoin.delimited := by
  have streamSemantics :=
    RouteDescriptorPairAffine.BendRoutePrefixDirectionScaling.streamOutput_numericRouteDescriptors
      (directSourceFormula decider symbols)
      (PeriodicCNF.incidenceGraph_isWellFormed _)
      (directSourceFormula_incidenceGraph_degreeAtMost decider symbols)
      (by
        unfold directSourceFormula
        exact PeriodicCNF.incidenceGraph_isLocal (sourceFormula_isLocal _))
      (directSourceFormula_isForwardLocal decider symbols)
  unfold directSourceFinalBendFallbackPrefixDirections
  rw [directSourceRouteDescriptorPairFieldTags_eq, streamSemantics]
  unfold directSourceFinalBendFallbackPrefixWords
    RouteDescriptorPairAffine.BendRoutePrefixDirectionScaling.canonicalScaledBendRoutePrefixDirectionBlock
    RouteDescriptorPairAffine.BendRoutePrefixDirectionScaling.scaledDelimitedBendRouteDirections
    RouteDescriptorPairAffine.delimitedBendRouteDirections
    DelimitedRouteJoin.delimited
  simp only [List.flatMap_assoc]
  apply List.flatMap_congr
  intro descriptor descriptorMember
  apply List.flatMap_congr
  intro routeBend routeBendMember
  simp

end LeanTrominoes.PeriodicCNFStripReduction

end
