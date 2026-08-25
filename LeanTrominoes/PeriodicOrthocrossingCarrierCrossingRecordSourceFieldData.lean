/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.DelimitedBinaryWordPairSelectorData
import LeanTrominoes.PeriodicOrthocrossingCarrierBoundaryPresenceFieldData
import LeanTrominoes.PeriodicOrthocrossingCarrierKeyFieldProjectorData
import LeanTrominoes.PeriodicOrthocrossingCarrierSourceKeyRepresentativeLookupData

/-! # Crossing-record fields carried by compact source keys -/

noncomputable section

namespace LeanTrominoes.PeriodicOrthocrossing
namespace CarrierCrossingRecordSourceField

open PaddedSupportedLastRepresentativeEqualityRows

/-- Crossing-record payload columns that are already present, without
arithmetic reconstruction, in one of the two compact source-key components.
The first segment index is omitted because its low three bits carry the node
side tag in the compact identity. -/
inductive Field
  | firstRoute
  | firstTranslateHorizontalPositive
  | firstTranslateHorizontalNegative
  | firstTranslateVerticalPositive
  | firstTranslateVerticalNegative
  | secondRoute
  | secondSegment
  | secondTranslateHorizontalPositive
  | secondTranslateHorizontalNegative
  | secondTranslateVerticalPositive
  | secondTranslateVerticalNegative
  deriving DecidableEq, Fintype

def component : Field → DelimitedBinaryWordPairSelector.Side
  | .firstRoute
  | .firstTranslateHorizontalPositive
  | .firstTranslateHorizontalNegative
  | .firstTranslateVerticalPositive
  | .firstTranslateVerticalNegative => .first
  | .secondRoute
  | .secondSegment
  | .secondTranslateHorizontalPositive
  | .secondTranslateHorizontalNegative
  | .secondTranslateVerticalPositive
  | .secondTranslateVerticalNegative => .second

def keyField : Field → CarrierKeyFieldProjector.Field
  | .firstRoute | .secondRoute => .route
  | .secondSegment => .segment
  | .firstTranslateHorizontalPositive
  | .secondTranslateHorizontalPositive => .horizontalPositive
  | .firstTranslateHorizontalNegative
  | .secondTranslateHorizontalNegative => .horizontalNegative
  | .firstTranslateVerticalPositive
  | .secondTranslateVerticalPositive => .verticalPositive
  | .firstTranslateVerticalNegative
  | .secondTranslateVerticalNegative => .verticalNegative

/-- Zero-indexed positions of these columns in the fifty-field rank scan. -/
def index : Field → Nat
  | .firstRoute => 14
  | .firstTranslateHorizontalPositive => 24
  | .firstTranslateHorizontalNegative => 25
  | .firstTranslateVerticalPositive => 26
  | .firstTranslateVerticalNegative => 27
  | .secondRoute => 28
  | .secondSegment => 29
  | .secondTranslateHorizontalPositive => 38
  | .secondTranslateHorizontalNegative => 39
  | .secondTranslateVerticalPositive => 40
  | .secondTranslateVerticalNegative => 41

def sourceKey (side : DelimitedBinaryWordPairSelector.Side)
    (node : CarrierNode) : CarrierKeyWords.CarrierKey :=
  match side with
  | .first => (CarrierNodeSourceKeys.pair node).1
  | .second => (CarrierNodeSourceKeys.pair node).2

def recordKey (side : DelimitedBinaryWordPairSelector.Side)
    (record : CrossingRecordCode) : CarrierKeyWords.CarrierKey :=
  match side with
  | .first =>
      (record.first.routeIndex, record.first.segmentIndex,
        record.firstTranslate)
  | .second =>
      (record.second.routeIndex, record.second.segmentIndex,
        record.secondTranslate)

/-- The selected compact source-key value, without checking the node kind. -/
def sourceNodeValue (field : Field) (node : CarrierNode) : Nat :=
  CarrierKeyFieldProjector.keyValue (keyField field)
    (sourceKey (component field) node)

def nodeValue (field : Field) : CarrierNode → Nat
  | .terminal _ => 0
  | .boundary boundary => sourceNodeValue field (.boundary boundary)

def optionalNodeValue (field : Field) : Option CarrierNode → Nat
  | none => 0
  | some node => nodeValue field node

def rankValue (field : Field) (datum : CarrierNodeRankDatum) : Nat :=
  match datum.boundaryCrossing with
  | none => 0
  | some record =>
      CarrierKeyFieldProjector.keyValue (keyField field)
        (recordKey (component field) record)

def terminalKeys (descriptors : List RouteDescriptor) :
    List (Option CarrierKeyWords.CarrierKey) :=
  (values
    (RouteDescriptorPairAffine.paddedTerminalCarrierNodeCandidateStream
      descriptors)).map (Option.map CarrierNode.carrierKey)

def crossingKeys (field : Field) (descriptors : List RouteDescriptor) :
    List (Option CarrierKeyWords.CarrierKey) :=
  (values
    (RouteDescriptorOccurrenceSlotCrossing.paddedCrossingCarrierNodeCandidateStream
      descriptors)).map
        (Option.map (sourceKey (component field)))

/-- Terminal slots contribute zero, crossing slots contribute the selected
source-key field, and the final zero is the representative-lookup sentinel. -/
def alignedValuesWithSentinel (field : Field)
    (descriptors : List RouteDescriptor) : List Nat :=
  (terminalKeys descriptors).map
      (GuardedPresenceFieldProjector.value false) ++
    (crossingKeys field descriptors).map
      (CarrierKeyFieldProjector.value (keyField field)) ++
    [0]

def values (field : Field) (descriptors : List RouteDescriptor) : List Nat :=
  CarrierSourceKeyRepresentativeLookup.values
    (alignedValuesWithSentinel field) descriptors

end CarrierCrossingRecordSourceField
end LeanTrominoes.PeriodicOrthocrossing

end
