import LeanTrominoes.PeriodicThreeDM
import Mathlib.Computability.Primrec.List

/-!
# Computability encodings for periodic three-dimensional matching

The natural-number periodic 3DM presentation is finite data.  This file gives
its references, triples, and complete instances canonical product encodings
for use by computable reductions.
-/

noncomputable section

namespace LeanTrominoes

namespace PeriodicThreeDMReference

/-- Product representation used by the standard computability encoding. -/
def equivData :
    PeriodicThreeDMReference ≃ Nat × Cell where
  toFun reference := (reference.atom, reference.offset)
  invFun data := ⟨data.1, data.2⟩
  left_inv reference := by cases reference; rfl
  right_inv data := by rcases data with ⟨atom, offset⟩; rfl

noncomputable instance : Primcodable PeriodicThreeDMReference :=
  Primcodable.ofEquiv (Nat × Cell) equivData

theorem equivData_primrec :
    Primrec equivData :=
  Primrec.of_equiv

theorem equivData_symm_primrec :
    Primrec equivData.symm :=
  Primrec.of_equiv_symm

theorem atom_primrec :
    Primrec PeriodicThreeDMReference.atom :=
  (Primrec.fst.comp equivData_primrec).of_eq fun _ => rfl

theorem offset_primrec :
    Primrec PeriodicThreeDMReference.offset :=
  (Primrec.snd.comp equivData_primrec).of_eq fun _ => rfl

end PeriodicThreeDMReference

namespace PeriodicThreeDMTriple

/-- Product representation used by the standard computability encoding. -/
def equivData :
    PeriodicThreeDMTriple ≃
      PeriodicThreeDMReference ×
        PeriodicThreeDMReference × PeriodicThreeDMReference where
  toFun triple := (triple.red, triple.green, triple.blue)
  invFun data := ⟨data.1, data.2.1, data.2.2⟩
  left_inv triple := by cases triple; rfl
  right_inv data := by
    rcases data with ⟨red, green, blue⟩
    rfl

noncomputable instance : Primcodable PeriodicThreeDMTriple :=
  Primcodable.ofEquiv
    (PeriodicThreeDMReference ×
      PeriodicThreeDMReference × PeriodicThreeDMReference)
    equivData

theorem equivData_primrec :
    Primrec equivData :=
  Primrec.of_equiv

theorem equivData_symm_primrec :
    Primrec equivData.symm :=
  Primrec.of_equiv_symm

theorem red_primrec :
    Primrec PeriodicThreeDMTriple.red :=
  (Primrec.fst.comp equivData_primrec).of_eq fun _ => rfl

theorem green_primrec :
    Primrec PeriodicThreeDMTriple.green :=
  ((Primrec.fst.comp Primrec.snd).comp
    equivData_primrec).of_eq fun _ => rfl

theorem blue_primrec :
    Primrec PeriodicThreeDMTriple.blue :=
  ((Primrec.snd.comp Primrec.snd).comp
    equivData_primrec).of_eq fun _ => rfl

end PeriodicThreeDMTriple

namespace PeriodicThreeDM

/-- Product representation used by the standard computability encoding. -/
def equivData :
    PeriodicThreeDM ≃
      Nat × Nat × Nat × List PeriodicThreeDMTriple where
  toFun problem :=
    (problem.redCount, problem.greenCount,
      problem.blueCount, problem.triples)
  invFun data :=
    ⟨data.1, data.2.1, data.2.2.1, data.2.2.2⟩
  left_inv problem := by cases problem; rfl
  right_inv data := by
    rcases data with ⟨redCount, greenCount,
      blueCount, triples⟩
    rfl

noncomputable instance : Primcodable PeriodicThreeDM :=
  Primcodable.ofEquiv
    (Nat × Nat × Nat × List PeriodicThreeDMTriple)
    equivData

theorem equivData_primrec :
    Primrec equivData :=
  Primrec.of_equiv

theorem equivData_symm_primrec :
    Primrec equivData.symm :=
  Primrec.of_equiv_symm

theorem redCount_primrec :
    Primrec PeriodicThreeDM.redCount :=
  (Primrec.fst.comp equivData_primrec).of_eq fun _ => rfl

theorem greenCount_primrec :
    Primrec PeriodicThreeDM.greenCount :=
  ((Primrec.fst.comp Primrec.snd).comp
    equivData_primrec).of_eq fun _ => rfl

theorem blueCount_primrec :
    Primrec PeriodicThreeDM.blueCount :=
  ((Primrec.fst.comp (Primrec.snd.comp Primrec.snd)).comp
    equivData_primrec).of_eq fun _ => rfl

theorem triples_primrec :
    Primrec PeriodicThreeDM.triples :=
  ((Primrec.snd.comp (Primrec.snd.comp Primrec.snd)).comp
    equivData_primrec).of_eq fun _ => rfl

end PeriodicThreeDM

end LeanTrominoes
