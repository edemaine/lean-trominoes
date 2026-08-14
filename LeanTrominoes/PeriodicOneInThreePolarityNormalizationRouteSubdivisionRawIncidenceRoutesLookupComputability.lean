/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNF

/-! # Metadata-list route-lookup computability -/

noncomputable section

namespace LeanTrominoes
namespace PeriodicOneInThreePolarityNormalizationRouteSubdivision

def incidenceRouteFromMetadataList {Input Metadata : Type*}
    (metadata : Input → List Metadata)
    (route : Input → Metadata → Nat → List Cell)
    (input : (Input × Nat) × Nat) : List Cell :=
  match (metadata input.1.1)[input.1.2]? with
  | none => []
  | some item => route input.1.1 item input.2

theorem incidenceRouteFromMetadataList_primrec
    {Input Metadata : Type*} [Primcodable Input] [Primcodable Metadata]
    (metadata : Input → List Metadata)
    (route : Input → Metadata → Nat → List Cell)
    (metadataPrimrec : Primrec metadata)
    (routePrimrec : Primrec fun input : (Input × Metadata) × Nat =>
      route input.1.1 input.1.2 input.2) :
    Primrec (incidenceRouteFromMetadataList metadata route) := by
  let Query := (Input × Nat) × Nat
  have lookup : Primrec fun input : Query =>
      (metadata input.1.1)[input.1.2]? :=
    Primrec.list_getElem?.comp
      (metadataPrimrec.comp (Primrec.fst.comp Primrec.fst))
      (Primrec.snd.comp Primrec.fst)
  have some : Primrec₂ fun (input : Query) (item : Metadata) =>
      route input.1.1 item input.2 := by
    change Primrec fun combined : Query × Metadata =>
      route combined.1.1.1 combined.2 combined.1.2
    exact routePrimrec.comp
      (Primrec.pair
        (Primrec.pair
          (Primrec.fst.comp (Primrec.fst.comp Primrec.fst))
          Primrec.snd)
        (Primrec.snd.comp Primrec.fst))
  exact (Primrec.option_casesOn lookup (Primrec.const []) some).of_eq
    fun input => by
      unfold incidenceRouteFromMetadataList
      cases (metadata input.1.1)[input.1.2]? <;> rfl

end PeriodicOneInThreePolarityNormalizationRouteSubdivision
end LeanTrominoes
