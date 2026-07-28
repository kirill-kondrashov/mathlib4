/-
Copyright (c) 2026 Kirill Kondrashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kirill Kondrashov, gpt-5.6-luna
-/
module

public import Mathlib.LinearAlgebra.ExteriorPower.Basis
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Mathlib.LinearAlgebra.Dual.Basis

/-!
# Duality for exterior powers

This file defines `exteriorPower.pairingDualEquiv`, the finite-dimensional linear equivalence
associated to the canonical map `exteriorPower.pairingDual`.

## Definitions

* `exteriorPower.pairingDualEquiv` identifies the exterior power of the dual with the dual of
  the exterior power.

## Theorems

The equivalence is induced by the canonical determinant pairing on exterior powers.
-/

@[expose] public section

namespace exteriorPower

open Module Set Set.powersetCard

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]

/- The exterior-power duality map takes the exterior basis induced by `b.dualBasis`
to the dual basis of the exterior basis induced by `b`. -/
set_option backward.privateInPublic true in
omit [FiniteDimensional K V] in
private theorem pairingDual_exteriorBasis (b : Basis (Fin (finrank K V)) K V)
    (k : ℕ) (s : powersetCard (Fin (finrank K V)) k) :
    pairingDual K V k (b.dualBasis.exteriorPower k s) =
      (b.exteriorPower k).dualBasis s := by
  rw [Basis.coe_dualBasis, basis_coord]
  simp [basis_apply, ιMulti_family, ιMultiDual, Basis.coe_dualBasis]

/- Evaluating the duality map on an exterior basis vector gives the corresponding
coordinate of the original exterior vector. -/
set_option backward.privateInPublic true in
omit [FiniteDimensional K V] in
private theorem pairingDual_apply_basis_repr (b : Basis (Fin (finrank K V)) K V)
    (k : ℕ) (f : ⋀[K]^k (Module.Dual K V))
    (s : powersetCard (Fin (finrank K V)) k) :
    pairingDual K V k f (b.exteriorPower k s) =
      (b.dualBasis.exteriorPower k).repr f s := by
  let e := b.dualBasis.exteriorPower k
  let d := b.exteriorPower k
  have hmap : (LinearMap.applyₗ (d s)).comp (pairingDual K V k) = e.coord s := by
    apply e.ext
    intro t
    change pairingDual K V k (b.dualBasis.exteriorPower k t) (b.exteriorPower k s) =
      (b.dualBasis.exteriorPower k).repr (b.dualBasis.exteriorPower k t) s
    rw [pairingDual_exteriorBasis]
    rw [Basis.dualBasis_apply_self, Basis.repr_self]
    simp only [Finsupp.single_apply]
    simp [eq_comm]
  simpa [e, d, LinearMap.applyₗ_apply_apply] using LinearMap.congr_fun hmap f

/- The canonical duality map is injective because exterior bases detect all coordinates. -/
set_option backward.privateInPublic true in
private theorem pairingDual_injective (k : ℕ) :
    Function.Injective (pairingDual K V k) := by
  let b := finBasis K V
  intro f g h
  apply (b.dualBasis.exteriorPower k).ext_elem
  intro s
  have hs := congrArg (fun q ↦ q (b.exteriorPower k s)) h
  rw [pairingDual_apply_basis_repr b k f s,
    pairingDual_apply_basis_repr b k g s] at hs
  exact hs

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
/-- The canonical linear equivalence from the exterior power of the dual to the dual of the
exterior power. -/
noncomputable def pairingDualEquiv (k : ℕ) :
    ⋀[K]^k (Module.Dual K V) ≃ₗ[K] Module.Dual K (⋀[K]^k V) := by
  apply LinearMap.linearEquivOfInjective (pairingDual K V k)
    (pairingDual_injective (V := V) k)
  calc
    finrank K (⋀[K]^k (Module.Dual K V)) =
        Nat.choose (finrank K (Module.Dual K V)) k := exteriorPower.finrank_eq K _
    _ = Nat.choose (finrank K V) k := by
      rw [(Module.finBasis K V).toDualEquiv.finrank_eq]
    _ = finrank K (⋀[K]^k V) := (exteriorPower.finrank_eq K _).symm
    _ = finrank K (Module.Dual K (⋀[K]^k V)) :=
      (Module.finBasis K (⋀[K]^k V)).toDualEquiv.finrank_eq

end exteriorPower
