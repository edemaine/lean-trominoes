/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorPairAffineTerminalCarrierKeySlotValueSemantics

/-! # Route-shape terminal carrier-key template values -/

namespace LeanTrominoes.PeriodicOrthocrossing.RouteDescriptorPairAffine

open PaddedSupportedCandidateBlocks

/-- Flattening a route shape's terminal template values gives the semantic
terminal keys of its evaluated neighboring occurrences. -/
theorem RouteShape.terminalCarrierKeyTemplateValues_eq
    (shape : RouteShape) (pair : RouteDescriptor × RouteDescriptor) :
    ((shape.segments .first).zipIdx.flatMap fun tagged =>
        (tagged.1.terminalCarrierKeyTemplateBlock
          pair tagged.2).map Template.value) =
      occurrenceTerminalCarrierKeys
        ((shape.segments .first).zipIdx.flatMap fun tagged =>
          neighborTranslations.map fun translate =>
            ((⟨pair.1.edgeIndex, tagged.2,
                tagged.1.evalPair pair⟩ : IndexedGridSegment),
              translate)) := by
  rw [show
      ((shape.segments .first).zipIdx.flatMap fun tagged =>
          (tagged.1.terminalCarrierKeyTemplateBlock
            pair tagged.2).map Template.value) =
        (shape.segments .first).zipIdx.flatMap fun tagged =>
          occurrenceTerminalCarrierKeys
            (neighborTranslations.map fun translate =>
              ((⟨pair.1.edgeIndex, tagged.2,
                  tagged.1.evalPair pair⟩ : IndexedGridSegment),
                translate)) by
    apply List.flatMap_congr
    intro tagged _taggedMember
    exact tagged.1.terminalCarrierKeyTemplateBlock_values
      pair tagged.2]
  unfold occurrenceTerminalCarrierKeys
  rw [List.flatMap_assoc]

end LeanTrominoes.PeriodicOrthocrossing.RouteDescriptorPairAffine
