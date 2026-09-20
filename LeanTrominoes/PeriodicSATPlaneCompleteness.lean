/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.PeriodicCNFSyntaxComputability
import LeanTrominoes.PeriodicThreeSATThreeComputability

/-! # The plane parts of Theorems 3.2–3.4

These statements use the existing finite-presentation encodings and reject
presentations violating the stated syntax restrictions. They do not assert
the separate one-dimensional PSPACE classifications.
-/
namespace LeanTrominoes

namespace WangPeriodicCNF

/-- Unrestricted two-dimensional periodic CNF SAT is co-r.e. complete. -/
theorem coREComplete : LeanWang.CoREComplete Holds :=
  ⟨PeriodicCNF.satisfiable_coRE, coREHard⟩

/-- The local two-dimensional periodic CNF problem is co-r.e. complete. -/
theorem localCoREComplete : LeanWang.CoREComplete LocalHolds :=
  ⟨PeriodicCNF.restricted_coRE PeriodicCNF.isLocal_primrec, localCoREHard⟩

end WangPeriodicCNF

namespace PeriodicThreeCNF

/-- The plane part of Theorem 3.3. -/
theorem localThreeCNFCoREComplete : LeanWang.CoREComplete LocalThreeCNFHolds := by
  refine ⟨?_, localThreeCNFCoREHard⟩
  have upper := PeriodicCNF.restricted_coRE
    (PeriodicCNF.isLocal_primrec (V := ThreeCNFVariable LeanWang.WangTile) |>.and
      (PeriodicCNF.widthAtMost_primrec 3))
  simpa only [LeanWang.CoREPred, LocalThreeCNFHolds, and_assoc] using upper

end PeriodicThreeCNF

namespace PeriodicThreeSATThree

local instance : BEq (ThreeCNFVariable LeanWang.WangTile) := instBEqOfDecidableEq

/-- The plane part of Theorem 3.4. -/
theorem localThreeSATThreeCoREComplete : LeanWang.CoREComplete LocalThreeSATThreeHolds := by
  refine ⟨?_, localThreeSATThreeCoREHard⟩
  have upper := PeriodicCNF.restricted_coRE
    ((PeriodicCNF.isLocal_primrec (V := WangThreeSATThreeVariable)).and
      ((PeriodicCNF.widthAtMost_primrec 3).and (PeriodicCNF.occurrencesAtMost_primrec 3)))
  simpa only [LeanWang.CoREPred, LocalThreeSATThreeHolds, and_assoc] using upper

end PeriodicThreeSATThree
end LeanTrominoes
