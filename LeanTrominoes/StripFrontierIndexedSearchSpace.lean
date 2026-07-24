import LeanTrominoes.IndexedSavitchDFSSpace
import LeanTrominoes.StripFrontierIndexedSearch

/-!
# Flat space bound for indexed strip search

This file specializes the generic depth-first Savitch configuration bound to
the sparse strip-frontier graph.  Both a frontier index and the chosen search
depth fit in `stripSearchDepth + 1` binary cells, giving an explicit quadratic
bound in the encoded strip input length.
-/

namespace LeanTrominoes
namespace PeriodicStrip
namespace RawWindowState

/-- Explicit quadratic bound for the flat DFS configuration, as a function of
the encoded strip input length. -/
def stripDFSSpaceBound (inputLength : Nat) : Nat :=
  3 * (21 * inputLength + 3) +
    (21 * inputLength + 1) * (4 * (21 * inputLength + 3) + 3) + 2

/-- The same bound packaged as a polynomial for the PSPACE interface. -/
noncomputable def stripDFSSpacePolynomial : Polynomial Nat :=
  3 * (21 * Polynomial.X + 3) +
    (21 * Polynomial.X + 1) *
      (4 * (21 * Polynomial.X + 3) + 3) + 2

@[simp]
theorem stripDFSSpacePolynomial_eval (inputLength : Nat) :
    stripDFSSpacePolynomial.eval inputLength =
      stripDFSSpaceBound inputLength := by
  simp [stripDFSSpacePolynomial, stripDFSSpaceBound]

theorem indexCount_le_pow_stripSearchDepth_succ
    (periodicStrip : PeriodicStrip) :
    indexCount periodicStrip ≤
      2 ^ (stripSearchDepth periodicStrip + 1) := by
  exact (indexCount_le_pow_stripSearchDepth periodicStrip).trans
    (Nat.pow_le_pow_right (by omega) (Nat.le_succ _))

theorem stripSearchDepth_lt_pow_succ
    (periodicStrip : PeriodicStrip) :
    stripSearchDepth periodicStrip <
      2 ^ (stripSearchDepth periodicStrip + 1) := by
  exact (stripSearchDepth periodicStrip).lt_two_pow_self.trans_le
    (Nat.pow_le_pow_right (by omega) (Nat.le_succ _))

/-- Every configuration reached while answering one strip-frontier
reachability query obeys the explicit quadratic input-length bound. -/
theorem stripDivideEvalIterate_flatSpace_le
    (periodicStrip : PeriodicStrip)
    (relation : Nat → Nat → Bool)
    (first last steps : Nat)
    (firstBelow : first < indexCount periodicStrip)
    (lastBelow : last < indexCount periodicStrip) :
    (((FiniteState.divideEvalStep (indexCount periodicStrip) relation)^[steps]
      (FiniteState.divideEvalInitial (stripSearchDepth periodicStrip)
        first last)).flatSpace) ≤
      stripDFSSpaceBound
        ((Complexity.primcodableFinEncoding PeriodicStrip).encode
          periodicStrip).length := by
  have generic :=
    FiniteState.divideEvalIterate_flatSpace_le
      (indexCount periodicStrip)
      (stripSearchDepth periodicStrip)
      (stripSearchDepth periodicStrip + 1)
      first last steps relation firstBelow lastBelow
      (indexCount_le_pow_stripSearchDepth_succ periodicStrip)
      (stripSearchDepth_lt_pow_succ periodicStrip)
  simpa [stripSearchDepth, stripDFSSpaceBound] using generic

end RawWindowState
end PeriodicStrip
end LeanTrominoes
