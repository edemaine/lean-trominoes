/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 6.1
-/
import LeanTrominoes.RetainedAngularFanDirectSourceSameTargetCertificateData

/-! Guarded kernel certificates for ordered incidences sharing a target. -/
namespace LeanTrominoes.PeriodicEightOccurrenceSplit
set_option maxRecDepth 10000
set_option maxHeartbeats 8000000

def sameTargetLocalChoicesCheck (first second : RetainedDirectSourceRouteChoice) : Bool :=
  guardedCheck (first.sourceSegment.finish = second.sourceSegment.finish)
    (guardedCheck ((retainedDirectSourcePrefixChoiceAt first.kind first.index).direction.angularRank ≤
      (retainedDirectSourcePrefixChoiceAt second.kind second.index).direction.angularRank)
      (finiteAll fun firstSlot : RetainedTerminalSlot =>
        finiteAll fun secondSlot : RetainedTerminalSlot =>
          guardedCheck (firstSlot.val < secondSlot.val)
            (finiteAll fun firstComponent : RetainedDirectSourceSameTargetComponent =>
              finiteAll fun secondComponent : RetainedDirectSourceSameTargetComponent =>
                guardedCheck (retainedDirectSourceSameTargetUsesAtlasCertificate firstComponent secondComponent = true)
                  (sameTargetPiecesCheck first second firstSlot secondSlot firstComponent secondComponent))))

def crossoverSameTargetCheck (firstClause : Fin 26) : Bool :=
  finiteAll fun secondClause : Fin 26 =>
    guardedCheck (firstClause ≠ secondClause)
      (finiteAll fun firstIndex : Fin (retainedDirectSourcePrefixChoices (.crossover firstClause)).length =>
        finiteAll fun secondIndex : Fin (retainedDirectSourcePrefixChoices (.crossover secondClause)).length =>
          sameTargetLocalChoicesCheck (retainedDirectSourceLocalChoice (.crossover firstClause) firstIndex)
            (retainedDirectSourceLocalChoice (.crossover secondClause) secondIndex))

def duplicatorSameTargetCheck (firstArm : PlanarThreeSAT.DuplicatorArm) (firstClause : Fin 2) : Bool :=
  finiteAll fun secondArm : PlanarThreeSAT.DuplicatorArm =>
    finiteAll fun secondClause : Fin 2 =>
      guardedCheck ((firstArm, firstClause) ≠ (secondArm, secondClause))
        (finiteAll fun firstIndex : Fin (retainedDirectSourcePrefixChoices (.duplicator firstArm firstClause)).length =>
          finiteAll fun secondIndex : Fin (retainedDirectSourcePrefixChoices (.duplicator secondArm secondClause)).length =>
            sameTargetLocalChoicesCheck (retainedDirectSourceLocalChoice (.duplicator firstArm firstClause) firstIndex)
              (retainedDirectSourceLocalChoice (.duplicator secondArm secondClause) secondIndex))


end LeanTrominoes.PeriodicEightOccurrenceSplit
