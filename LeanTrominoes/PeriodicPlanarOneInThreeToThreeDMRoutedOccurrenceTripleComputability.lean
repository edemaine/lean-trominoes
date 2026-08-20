/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicPlanarOneInThreeToThreeDMEncodingComputability
import LeanTrominoes.PeriodicPlanarOneInThreeToThreeDMRoutedTriples
import LeanTrominoes.FiniteDomainComputability
import LeanTrominoes.OrthogonalDrawing

/-! # Computability of routed occurrence triples -/

noncomputable section

namespace LeanTrominoes
namespace PeriodicPlanarOneInThreeToThreeDM

open Gadget PlanarThreeDM

local instance fixedRedConnectorTripleInhabited :
    Inhabited FixedRedConnectorTriple :=
  ⟨.auxiliary⟩

local instance variableOccurrenceTripleInhabited :
    Inhabited VariableOccurrenceTriple :=
  ⟨.auxiliary⟩

theorem routedOccurrenceTriple_primrec
    {Variable : Type*} [Primcodable Variable] [DecidableEq Variable] :
    Primrec fun input :
        ((PeriodicCNF Variable × Variable) × OccurrenceSlot) × WireColor =>
      routedOccurrenceTriple input.1.1.1 input.1.1.2
        input.1.2 input.2 := by
  let Input :=
    ((PeriodicCNF Variable × Variable) × OccurrenceSlot) × WireColor
  have metadata : Primrec fun input : Input =>
      ((input.1.1.1, input.1.1.2), input.1.2) :=
    Primrec.fst
  have atomSlot : Primrec fun input : Input =>
      (input.1.1.2, input.1.2) :=
    Primrec.pair
      (Primrec.snd.comp (Primrec.fst.comp Primrec.fst))
      (Primrec.snd.comp Primrec.fst)
  have kind : Primrec fun input : Input =>
      occurrenceConnectorKind input.1.1.1 input.1.1.2 input.1.2 :=
    occurrenceConnectorKind_primrec.comp metadata
  have isRed : PrimrecPred fun input : Input =>
      occurrenceConnectorKind input.1.1.1 input.1.1.2 input.1.2 =
        VariableConnectorKind.fixedRed :=
    Primrec.eq.comp kind
      (Primrec.const VariableConnectorKind.fixedRed)
  have isGreen : PrimrecPred fun input : Input =>
      occurrenceConnectorKind input.1.1.1 input.1.1.2 input.1.2 =
        VariableConnectorKind.fixedGreen :=
    Primrec.eq.comp kind
      (Primrec.const VariableConnectorKind.fixedGreen)
  have fixedLocal : Primrec fun color : WireColor =>
      match color with
      | .red => FixedRedConnectorTriple.bottomRight
      | .green => .auxiliary
      | .blue => .auxiliary :=
    Computability.finiteDomain_primrec _
  have fixed : Primrec fun input : Input =>
      Triple.fixedRed input.1.1.2 input.1.2
        (match input.2 with
        | .red => FixedRedConnectorTriple.bottomRight
        | .green => .auxiliary
        | .blue => .auxiliary) :=
    triple_fixedRed_primrec.comp
      (Primrec.pair atomSlot (fixedLocal.comp Primrec.snd))
  have ordinaryLocal : Primrec fun color : WireColor =>
      match color with
      | .red => VariableOccurrenceTriple.auxiliary
      | .green => .auxiliary
      | .blue => .first :=
    Computability.finiteDomain_primrec _
  have ordinary (variant : VariableOccurrenceVariant) :
      Primrec fun input : Input =>
        Triple.ordinary input.1.1.2 input.1.2 variant
          (match input.2 with
          | .red => VariableOccurrenceTriple.auxiliary
          | .green => .auxiliary
          | .blue => .first) :=
    triple_ordinary_primrec.comp
      (Primrec.pair
        (Primrec.pair atomSlot (Primrec.const variant))
        (ordinaryLocal.comp Primrec.snd))
  exact (Primrec.ite isRed fixed
    (Primrec.ite isGreen (ordinary .fixedGreen)
      (ordinary .fixedBlue))).of_eq fun input => by
        cases kindEq : occurrenceConnectorKind
          input.1.1.1 input.1.1.2 input.1.2 <;>
          cases input.2 <;>
          simp [routedOccurrenceTriple, kindEq]

end PeriodicPlanarOneInThreeToThreeDM
end LeanTrominoes
