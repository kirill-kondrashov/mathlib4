/-
Copyright (c) 2026 Kirill Kondrashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kirill Kondrashov
-/
module

public import Mathlib.LinearAlgebra.BilinearForm.Properties
public import Mathlib.LinearAlgebra.ExteriorPower.Basis

/-!
# Hodge star on exterior powers

We define the Hodge star on exterior powers associated to a nondegenerate bilinear form
and a finite linearly ordered basis.

## Definitions

* `exteriorPower.hodgeStar` is the Hodge star associated to a nondegenerate bilinear form
  and a finite linearly ordered basis.

## Theorems

* `exteriorPower.hodgeStar_apply_dualBasis_exteriorPower` states that the Hodge star sends a
  dual exterior-basis vector to the signed complementary basis vector.
-/

@[expose] public section

namespace exteriorPower

open Module Set Set.powersetCard

variable {K V ι : Type*} [Field K] [AddCommGroup V] [Module K V]
  [Fintype ι] [LinearOrder ι]

/-- The complementary index set used by the Hodge star. -/
def hodgeStarComplement (k : ℕ) (s : powersetCard ι k) :
    powersetCard ι (Fintype.card ι - k) :=
  let hk : (Fintype.card ι - k) + k = Fintype.card ι :=
    Nat.sub_add_cancel <| by
      have hs := Finset.card_le_card (Finset.subset_univ s.val)
      rw [s.prop] at hs
      simpa using hs
  compl hk s

/-- The index set of a Hodge star basis vector is disjoint from the original index set. -/
theorem hodgeStarComplement_disjoint (k : ℕ) (s : powersetCard ι k) :
    Disjoint s.val (hodgeStarComplement k s).val := by
  rw [hodgeStarComplement]
  rw [coe_compl, Finset.disjoint_left]
  intro i hi hci
  exact (Finset.mem_compl.mp hci) hi

/-- The signed complementary basis vector appearing in the Hodge star. -/
noncomputable def hodgeStarBasisVector (b : Basis ι K V) (k : ℕ) (s : powersetCard ι k) :
    ⋀[K]^(Fintype.card ι - k) V :=
  (permOfDisjoint (hodgeStarComplement_disjoint k s)).sign •
    b.exteriorPower (Fintype.card ι - k) (hodgeStarComplement k s)

/-- The Hodge star determined by a nondegenerate bilinear form and an ordered basis.
It maps degree `k` to the complementary degree `Fintype.card ι - k`. -/
noncomputable def hodgeStar (B : LinearMap.BilinForm K V) (hB : B.Nondegenerate)
    (b : Basis ι K V) (k : ℕ) :
    ⋀[K]^k V →ₗ[K]
      ⋀[K]^(Fintype.card ι - k) V :=
  ((B.dualBasis hB b).exteriorPower k).constr K (hodgeStarBasisVector b k)

/-- The Hodge star sends a dual exterior-basis vector to the signed complementary basis vector. -/
@[simp]
theorem hodgeStar_apply_dualBasis_exteriorPower (B : LinearMap.BilinForm K V)
    (hB : B.Nondegenerate) (b : Basis ι K V) (k : ℕ) (s : powersetCard ι k) :
    hodgeStar B hB b k ((B.dualBasis hB b).exteriorPower k s) =
      hodgeStarBasisVector b k s := by
  simp only [hodgeStar, Basis.constr_basis]

end exteriorPower
