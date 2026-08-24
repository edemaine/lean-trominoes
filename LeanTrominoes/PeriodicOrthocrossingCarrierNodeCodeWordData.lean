/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingCarrierKeyWordData
import LeanTrominoes.PeriodicOrthocrossingCarrierNodeCodeData

/-! # Self-delimiting binary words for carrier-node identities -/

namespace LeanTrominoes.PeriodicOrthocrossing.CarrierNodeCodeWords

open CarrierKeyWords

def cellWord (cell : Cell) : List Bool :=
  intField cell.1 ++ intField cell.2

def indexedSegmentWord (code : IndexedGridSegmentCode) : List Bool :=
  natField code.routeIndex ++ natField code.segmentIndex ++
    cellWord code.start ++ cellWord code.finish

def crossingRecordWord (code : CrossingRecordCode) : List Bool :=
  indexedSegmentWord code.first ++ cellWord code.firstTranslate ++
    indexedSegmentWord code.second ++ cellWord code.secondTranslate ++
      cellWord code.point

def segmentEndWord : SegmentEnd → List Bool
  | .start => [false]
  | .finish => [true]

def segmentTerminalWord (code : SegmentTerminalCode) : List Bool :=
  indexedSegmentWord code.indexed ++ cellWord code.translate ++
    segmentEndWord code.endpoint

def crossingSideWord : CrossingSide → List Bool
  | .left => [false, false]
  | .right => [false, true]
  | .top => [true, false]
  | .bottom => [true, true]

def crossingBoundaryWord (code : CrossingBoundaryCode) : List Bool :=
  crossingRecordWord code.crossing ++ crossingSideWord code.side

/-- A leading constructor bit distinguishes boundary identities from terminal
identities; every nested numeric field remains self-delimiting. -/
def word : CarrierNodeCode → List Bool
  | .boundary boundary => false :: crossingBoundaryWord boundary
  | .terminal terminal => true :: segmentTerminalWord terminal

end LeanTrominoes.PeriodicOrthocrossing.CarrierNodeCodeWords
