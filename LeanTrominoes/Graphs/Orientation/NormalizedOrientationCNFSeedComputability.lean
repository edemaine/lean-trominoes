/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.Graphs.Orientation.NormalizedOrientationCNF
import LeanTrominoes.SAT.CNF.PeriodicCNFSeededCoRE

/-! # Effective physical-port prescriptions for a fixed normalized drawing -/
noncomputable section
namespace LeanTrominoes.Gadget.NormalizedOrientation.AsCNF
open PeriodicOrthogonalDrawing Computability

instance sidePrimcodable : Primcodable Side :=
  Primcodable.ofEquiv (Fin (Fintype.card Side)) (Fintype.equivFin Side)

private theorem remainder_primrec (period : Nat) : Primrec (fun c : Int => c % (period : Int)) :=
  (int_subtract_primrec.comp Primrec.id
    (int_multiply_primrec.comp (int_edivNat_primrec.comp Primrec.id (Primrec.const period))
      (Primrec.const (period : Int)))).of_eq (fun c => by
        change c - c / (period : Int) * (period : Int) = c % (period : Int)
        have h := Int.emod_add_ediv_mul c (period : Int)
        omega)

theorem address_primrec (d : Drawing) : Primrec (address d) :=
  Primrec.pair
    (int_toNat_primrec.comp ((remainder_primrec d.horizontalPeriod).comp Primrec.fst))
    (int_toNat_primrec.comp ((remainder_primrec d.verticalPeriod).comp Primrec.snd))

theorem quotient_primrec (d : Drawing) : Primrec (quotient d) :=
  Primrec.pair (int_edivNat_primrec.comp Primrec.fst (Primrec.const d.horizontalPeriod))
    (int_edivNat_primrec.comp Primrec.snd (Primrec.const d.verticalPeriod))

theorem seed_primrec (d : Drawing) : Primrec (seed d) := by
  have pin : Primrec (fun p : (Cell × Side) × Bool =>
      (((address d p.1.1,p.1.2),quotient d p.1.1),p.2)) :=
    Primrec.pair
      (Primrec.pair
        (Primrec.pair ((address_primrec d).comp (Primrec.fst.comp Primrec.fst))
          (Primrec.snd.comp Primrec.fst))
        ((quotient_primrec d).comp (Primrec.fst.comp Primrec.fst))) Primrec.snd
  exact Primrec.list_map Primrec.id (pin.comp Primrec.snd)

theorem prescribed_coRE (d : Drawing) : LeanWang.CoREPred (Prescribed d) :=
  (LeanWang.REPred.comp (PeriodicCNF.fixed_seeded_coRE (formula d)) (seed_primrec d).to_comp).of_eq
    (fun prescriptions => not_congr (seeded_iff d prescriptions))

end LeanTrominoes.Gadget.NormalizedOrientation.AsCNF
