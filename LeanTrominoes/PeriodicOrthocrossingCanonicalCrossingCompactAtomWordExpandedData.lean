/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingCanonicalCrossingCompactAtomWordSourceData
import LeanTrominoes.PeriodicOrthocrossingCrossoverCompactAtomWordData

/-! # Expanded canonical crossing compact-word streams -/

namespace LeanTrominoes.PeriodicOrthocrossing
namespace CanonicalCrossingCompactAtomWordSources

/-- Apply the fixed Figure 8(b) role expander independently to every selected
canonical crossing source pair. -/
def expandedWordsAtPeriod (period : Nat)
    (descriptors : List RouteDescriptor) : List (List Bool) :=
  (wordsAtPeriod period descriptors).flatMap
    CrossoverCompactAtomWords.wordsForRoles

end CanonicalCrossingCompactAtomWordSources
end LeanTrominoes.PeriodicOrthocrossing
