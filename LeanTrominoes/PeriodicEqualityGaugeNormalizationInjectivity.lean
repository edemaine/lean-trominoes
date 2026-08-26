/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicEqualityNormalization

/-! # Injectivity of gauged periodic-link normalization -/

namespace LeanTrominoes.PeriodicEquality

open PlanarThreeSAT

/-- Postcompose endpoint prototypes with an embedding and add a fixed gauge
depending on the embedded prototype. -/
def gaugeNormalization
    {Source Target Wrapped : Type*}
    (normalize : Source → Target × Cell)
    (embed : Target → Wrapped)
    (gauge : Wrapped → Cell)
    (source : Source) : Wrapped × Cell :=
  let normalized := normalize source
  let wrapped := embed normalized.1
  (wrapped, Cell.add normalized.2 (gauge wrapped))

/-- An injective prototype embedding and prototype-dependent endpoint gauge
do not identify any additional normalized equality links. -/
theorem normalizeLink_gaugeNormalization_eq_iff
    {Source Target Wrapped : Type*}
    (normalize : Source → Target × Cell)
    (embed : Target → Wrapped)
    (embedInjective : Function.Injective embed)
    (gauge : Wrapped → Cell)
    (first second : EqualityLink Source) :
    normalizeLink (gaugeNormalization normalize embed gauge) first =
        normalizeLink (gaugeNormalization normalize embed gauge) second ↔
      normalizeLink normalize first = normalizeLink normalize second := by
  rcases first with ⟨firstSource, firstTarget, firstPositions⟩
  rcases second with ⟨secondSource, secondTarget, secondPositions⟩
  rcases firstSourceEq : normalize firstSource with
    ⟨firstSourcePrototype, ⟨firstSourceX, firstSourceY⟩⟩
  rcases firstTargetEq : normalize firstTarget with
    ⟨firstTargetPrototype, ⟨firstTargetX, firstTargetY⟩⟩
  rcases secondSourceEq : normalize secondSource with
    ⟨secondSourcePrototype, ⟨secondSourceX, secondSourceY⟩⟩
  rcases secondTargetEq : normalize secondTarget with
    ⟨secondTargetPrototype, ⟨secondTargetX, secondTargetY⟩⟩
  constructor
  · intro gaugedEq
    simp only [normalizeLink, gaugeNormalization,
      firstSourceEq, firstTargetEq, secondSourceEq, secondTargetEq,
      Cell.add, Cell.sub, NormalizedLink.mk.injEq] at gaugedEq ⊢
    have sourcePrototypeEq :
        firstSourcePrototype = secondSourcePrototype :=
      embedInjective gaugedEq.1
    have targetPrototypeEq :
        firstTargetPrototype = secondTargetPrototype :=
      embedInjective gaugedEq.2.1
    subst secondSourcePrototype
    subst secondTargetPrototype
    simp only [true_and]
    rcases gauge (embed firstSourcePrototype) with
      ⟨sourceGaugeX, sourceGaugeY⟩
    rcases gauge (embed firstTargetPrototype) with
      ⟨targetGaugeX, targetGaugeY⟩
    simp only [Prod.mk.injEq] at gaugedEq ⊢
    constructor <;> omega
  · intro baseEq
    simp only [normalizeLink, gaugeNormalization,
      firstSourceEq, firstTargetEq, secondSourceEq, secondTargetEq,
      Cell.add, Cell.sub, NormalizedLink.mk.injEq] at baseEq ⊢
    rcases baseEq with
      ⟨sourcePrototypeEq, targetPrototypeEq, offsetEq⟩
    subst secondSourcePrototype
    subst secondTargetPrototype
    simp only [true_and]
    rcases gauge (embed firstSourcePrototype) with
      ⟨sourceGaugeX, sourceGaugeY⟩
    rcases gauge (embed firstTargetPrototype) with
      ⟨targetGaugeX, targetGaugeY⟩
    simp only [Prod.mk.injEq] at offsetEq ⊢
    constructor <;> omega

end LeanTrominoes.PeriodicEquality
