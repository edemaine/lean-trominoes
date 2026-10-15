/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.SAT.Planar.OccurrenceSplit.AngularFan.Direct.RetainedAngularFanDirectSourceHeadIsolationData

namespace LeanTrominoes.PeriodicEightOccurrenceSplit

def directSourceHeadFreshIndexCheck (kind : RetainedDirectClauseKind)
    (index : Fin (retainedDirectSourcePrefixChoices kind).length) : Bool :=
  finiteAll fun slot : RetainedTerminalSlot =>
    routeHeadGeometricallyFresh ((retainedDirectSourceZeroChoice kind index).completeFigure7Route slot)

end LeanTrominoes.PeriodicEightOccurrenceSplit
