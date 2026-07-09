/-
Copyright (c) 2026 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Malhar A. Patel
-/
module

public import Mathlib.Algebra.Polynomial.Lifts
public import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
public import Mathlib.FieldTheory.Galois.Infinite
public import Mathlib.FieldTheory.IsSepClosed

/-!
# Galois descent of the kernel polynomial

Helper lemmas for `FLT.KnownIn1980s.EllipticCurves.EllipticQuotient`: the set of
x-coordinates of the nonzero points of a finite subgroup `C ⊆ E(K)` is finite, the
squarefree polynomial `∏ (X − x)` over it is Galois-fixed when `C` is Galois-stable, and it
therefore lifts to a monic polynomial in `k[X]`.

That file imports this one, so its definitions (`kernelPolynomial`, `GaloisStable`, ...)
are not available here; the statements are phrased in raw terms and repackaged there.
-/

@[expose] public section

open Polynomial

open scoped WeierstrassCurve.Affine

namespace WeierstrassCurve

variable {k : Type*} [Field k] (K : Type*) [Field K] [Algebra k K] [IsSepClosure k K]
  [DecidableEq K] (E : WeierstrassCurve k)

omit [IsSepClosure k K] in
/-- The set of x-coordinates of the nonzero points of a finite `C` is finite. -/
lemma finite_xCoordSet (C : AddSubgroup (E⁄K).Point) [Finite C] :
    {x : K | ∃ (y : K) (hxy : (E⁄K).Nonsingular x y),
      Affine.Point.some x y hxy ∈ C}.Finite := by
  refine ((Set.toFinite (C : Set (E⁄K).Point)).image
    fun P => match P with | .zero => 0 | .some x _ _ => x).subset ?_
  rintro x ⟨y, hxy, hmem⟩
  exact ⟨Affine.Point.some x y hxy, hmem, rfl⟩

omit [IsSepClosure k K] in
/-- The Galois action permutes the nonzero points of a stable `C`, hence permutes their
x-coordinates, hence fixes `∏ (X − x)` (downstream: `kernelPolynomial_map_galois`). -/
lemma map_prod_X_sub_C_xCoordSet (C : AddSubgroup (E⁄K).Point) [Finite C]
    (hC : ∀ σ : K ≃ₐ[k] K, ∀ P ∈ C, Affine.Point.map σ.toAlgHom P ∈ C) (σ : K ≃ₐ[k] K) :
    (∏ x ∈ (finite_xCoordSet K E C).toFinset, (X - Polynomial.C x)).map (σ : K →+* K)
      = ∏ x ∈ (finite_xCoordSet K E C).toFinset, (X - Polynomial.C x) := by
  have himg : (finite_xCoordSet K E C).toFinset.image σ = (finite_xCoordSet K E C).toFinset := by
    refine Finset.eq_of_subset_of_card_le ?_
      (Finset.card_image_of_injective _ σ.injective).ge
    intro x hx
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hx
    simp only [Set.Finite.mem_toFinset, Set.mem_setOf_eq] at hy ⊢
    obtain ⟨z, hz, hmem⟩ := hy
    have h2 := hC σ _ hmem
    rw [Affine.Point.map_some] at h2
    exact ⟨σ z, _, h2⟩
  conv_rhs => rw [← himg, Finset.prod_image fun x _ y _ hxy => σ.injective hxy]
  simp [Polynomial.map_prod]

/-- Descent: For Galois-stable `C` each coefficient of `∏ (X − x)` is `Gal(K/k)`-fixed,
and the fixed field of a separable closure is `k`; so the product lifts to a monic
polynomial in `k[X]` (downstream: `exists_isKernelPolynomial`). -/
lemma exists_monic_map_eq_prod_X_sub_C_xCoordSet (C : AddSubgroup (E⁄K).Point) [Finite C]
    (hC : ∀ σ : K ≃ₐ[k] K, ∀ P ∈ C, Affine.Point.map σ.toAlgHom P ∈ C) :
    ∃ h : k[X], h.Monic ∧ h.map (algebraMap k K)
      = ∏ x ∈ (finite_xCoordSet K E C).toFinset, (X - Polynomial.C x) := by
  have hmem : (∏ x ∈ (finite_xCoordSet K E C).toFinset, (X - Polynomial.C x))
      ∈ Polynomial.lifts (algebraMap k K) := by
    rw [Polynomial.lifts_iff_coeff_lifts]
    intro n
    rw [InfiniteGalois.mem_range_algebraMap_iff_fixed]
    intro σ
    conv_rhs => rw [← map_prod_X_sub_C_xCoordSet K E C hC σ]
    rw [Polynomial.coeff_map]
    rfl
  obtain ⟨h, hh⟩ := (Polynomial.mem_lifts _).mp hmem
  exact ⟨h, Polynomial.monic_of_injective (algebraMap k K).injective
    (by rw [hh]; exact monic_prod_of_monic _ _ fun x _ => monic_X_sub_C x), hh⟩

end WeierstrassCurve
