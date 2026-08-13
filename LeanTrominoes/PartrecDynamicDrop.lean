import LeanTrominoes.PartrecFlatIteration
import LeanTrominoes.PartrecListCode

/-!
# Dynamic native-list suffix selection

The fixed `Code.drop` combinator bakes its offset into the program.  Flat
Savitch contexts instead begin after a variable-size DFS stack, so this module
uses the tail-style countdown to consume a runtime number of leading fields.
-/

namespace Turing.ToPartrec.Code

/-- Input `[count, values...]`; output `values.drop count`. -/
def dynamicDropCode : Code :=
  flatIterate tail

@[simp]
theorem dynamicDropCode_eval (count : Nat) (values : List Nat) :
    dynamicDropCode.eval (count :: values) = pure (values.drop count) := by
  have tailCorrect : ∀ payload : List Nat,
      tail.eval payload = pure payload.tail := by
    intro payload
    simp
  have iterated : ((List.tail)^[count]) values = values.drop count := by
    induction count generalizing values with
    | zero => rfl
    | succ count induction =>
        rw [Function.iterate_succ_apply]
        simpa using induction values.tail
  rw [dynamicDropCode,
    flatIterate_eval tail List.tail tailCorrect count values,
    iterated]

end Turing.ToPartrec.Code
