/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PlanarThreeSATDuplicatorArmIncidenceDrawing

/-!
# Incidence drawings for routed source clauses

A routed source clause occupies the same vertex macrocell as the three
orthocrossing fanout ports.  Its clause vertex is at `(10, 10)`, while its
zero to three distinct variables occupy the left, middle, and right ports
used by the duplicator-arm geometry.

This file gives the input-independent finite certificate: every list of
signed, pairwise distinct ports yields a continuously planar straight-ray
star.  Polarity affects only the logical label and is exhaustively irrelevant
to the geometry.
-/

namespace LeanTrominoes
namespace PlanarThreeSAT

/-- One local source clause with signed literals at the three fanout ports. -/
def routedClausePortFormula
    (literals : List (DuplicatorArm × Bool)) :
    List (EmbeddedClause DuplicatorArm) :=
  [⟨(10, 10), literals⟩]

/-- Direct rays from the routed source-clause vertex to its active ports. -/
def routedClausePortStraightIncidenceDrawing
    (literals : List (DuplicatorArm × Bool)) :
    EmbeddedCNFIncidenceDrawing DuplicatorArm :=
  straightIncidenceDrawing
    (routedClausePortFormula literals)
    DuplicatorArm.portPosition

/-- Every direct routed-clause port ray has its advertised endpoints. -/
theorem routedClausePortStraightIncidenceDrawing_routesMatch
    (literals : List (DuplicatorArm × Bool)) :
    (routedClausePortStraightIncidenceDrawing
      literals).RoutesMatch := by
  exact straightIncidenceDrawing_routesMatch
    (routedClausePortFormula literals)
    DuplicatorArm.portPosition

/-- Any subset of the three routed-clause ports forms a continuously planar
star.  `Nodup` also bounds the list length because `DuplicatorArm` has exactly
three elements. -/
theorem routedClausePortStraightIncidenceDrawing_isPlanar
    (literals : List (DuplicatorArm × Bool))
    (portsNodup : (literals.map Prod.fst).Nodup) :
    (routedClausePortStraightIncidenceDrawing
      literals).IsPlanar := by
  have lengthLe : literals.length ≤ 3 := by
    have bound := portsNodup.length_le_card
    norm_num at bound ⊢
    exact bound
  cases literals with
  | nil =>
      native_decide
  | cons first rest =>
      cases rest with
      | nil =>
          rcases first with ⟨firstArm, firstPolarity⟩
          cases firstArm <;> cases firstPolarity <;> native_decide
      | cons second rest =>
          cases rest with
          | nil =>
              rcases first with ⟨firstArm, firstPolarity⟩
              rcases second with ⟨secondArm, secondPolarity⟩
              cases firstArm <;> cases firstPolarity <;>
                cases secondArm <;> cases secondPolarity <;>
                simp_all <;> native_decide
          | cons third rest =>
              cases rest with
              | nil =>
                  rcases first with ⟨firstArm, firstPolarity⟩
                  rcases second with ⟨secondArm, secondPolarity⟩
                  rcases third with ⟨thirdArm, thirdPolarity⟩
                  cases firstArm <;> cases firstPolarity <;>
                    cases secondArm <;> cases secondPolarity <;>
                    cases thirdArm <;> cases thirdPolarity <;>
                    simp_all <;> native_decide
              | cons fourth rest =>
                  simp at lengthLe
                  omega

end PlanarThreeSAT
end LeanTrominoes
