import LeanTrominoes.TrominoFiniteListExclusion

/-! Bounded certificate checks keep kernel reduction memory independent of
the number of nodes checked in one theorem. Each node still sees its full
suffix, so child indices retain their original meaning. -/

namespace LeanTrominoes.TrominoFiniteListExclusion

def checkPrefix (t : Tromino) : Nat → List Node → Bool
  | 0, _ => true
  | _ + 1, [] => true
  | n + 1, node :: later => decide (ValidStep t node later) && checkPrefix t n later

theorem check_split (t : Tromino) (n : Nat) (certificate : List Node) :
    check t certificate = (checkPrefix t n certificate && check t (certificate.drop n)) := by
  induction n generalizing certificate with
  | zero => simp [checkPrefix]
  | succ n ih =>
    cases certificate with
    | nil => simp [check,checkPrefix]
    | cons node later =>
      simp only [check,checkPrefix,List.drop_succ_cons]
      rw [ih later,Bool.and_assoc]

theorem check_of_prefix (t : Tromino) (n : Nat) (certificate : List Node)
    (checkedPrefix : checkPrefix t n certificate = true)
    (suffix : check t (certificate.drop n) = true) : check t certificate = true := by
  rw [check_split t n certificate,checkedPrefix,suffix]
  rfl

end LeanTrominoes.TrominoFiniteListExclusion
