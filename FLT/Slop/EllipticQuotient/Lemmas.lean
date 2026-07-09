/-
Copyright (c) 2026 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Malhar A. Patel
-/
module

public import FLT.KnownIn1980s.EllipticCurves.EllipticQuotient

/-!
# Supporting lemmas for `EllipticQuotient`

Lemmas about the definitions of `FLT.KnownIn1980s.EllipticCurves.EllipticQuotient` that are
not needed for its main statements: basic properties of the kernel polynomial, the
specification lemmas pinning `velT`/`velW` (open `sorry`s), and Galois-equivariance of
`Isogeny` (open `sorry`, blocked on the infinitude of `E(K)` for `K` separably closed).
-/

@[expose] public section

open Polynomial

open scoped WeierstrassCurve.Affine

namespace WeierstrassCurve

variable {k : Type*} [Field k] (K : Type*) [Field K] [Algebra k K] [IsSepClosure k K]
  [DecidableEq K]

/-! ## The kernel polynomial -/

section KernelPolynomial

variable (E : WeierstrassCurve k)

omit [IsSepClosure k K] in
lemma kernelPolynomial_monic (C : AddSubgroup (E⁄K).Point) [Finite C] :
    (kernelPolynomial K E C).Monic :=
  monic_prod_of_monic _ _ fun x _ => monic_X_sub_C x

omit [IsSepClosure k K] in
/-- The Galois action permutes the nonzero points of a stable `C`, hence permutes their
x-coordinates, hence fixes the kernel polynomial. -/
lemma kernelPolynomial_map_galois (C : AddSubgroup (E⁄K).Point) [Finite C]
    (hC : GaloisStable K E C) (σ : K ≃ₐ[k] K) :
    (kernelPolynomial K E C).map (σ : K →+* K) = kernelPolynomial K E C :=
  map_prod_X_sub_C_xCoordSet K E C hC σ

omit [IsSepClosure k K] in
/-- The descended kernel polynomial is unique, so downstream statements may take `h` as a
hypothesis without ambiguity. -/
lemma IsKernelPolynomial.unique (C : AddSubgroup (E⁄K).Point) [Finite C] {h₁ h₂ : k[X]}
    (H₁ : IsKernelPolynomial K E C h₁) (H₂ : IsKernelPolynomial K E C h₂) :
    h₁ = h₂ :=
  Polynomial.map_injective _ (algebraMap k K).injective (H₁.2.trans H₂.2.symm)

omit [IsSepClosure k K] in
/-- Nonzero points of `C` come in pairs `{Q, −Q}` sharing an x-coordinate, so if `C` has
trivial 2-torsion then `#C = 2·deg h + 1`. -/
lemma natCard_eq_of_two_torsion_free (C : AddSubgroup (E⁄K).Point) [Finite C]
    (h2 : ∀ P ∈ C, P + P = 0 → P = 0) :
    Nat.card C = 2 * (kernelPolynomial K E C).natDegree + 1 := by
  classical
  have hCfin : (C : Set (E⁄K).Point).Finite := Set.toFinite _
  have hdiff : ((C : Set (E⁄K).Point) \ {0}).Finite := hCfin.sdiff
  -- the x-coordinate extractor, with junk value `0` at the point at infinity
  let f : (E⁄K).Point → K := fun P => match P with | .zero => 0 | .some x _ _ => x
  -- the degree of the kernel polynomial is the number of distinct x-coordinates
  have hdeg : (kernelPolynomial K E C).natDegree = (finite_xCoordSet K E C).toFinset.card := by
    rw [kernelPolynomial, Polynomial.natDegree_prod _ _ fun x _ => X_sub_C_ne_zero x]
    simp
  -- `f` maps the nonzero points of `C` into the x-coordinate set ...
  have Hmaps : ∀ P ∈ hdiff.toFinset, f P ∈ (finite_xCoordSet K E C).toFinset := by
    rintro (_ | ⟨x, y, hxy⟩) hP <;>
      simp only [Set.Finite.mem_toFinset, Set.mem_sdiff, Set.mem_singleton_iff,
        Set.mem_setOf_eq] at hP ⊢
    · exact absurd rfl hP.2
    · exact ⟨y, hxy, hP.1⟩
  -- ... with every fiber being a pair `{Q, -Q}` of size exactly two (no 2-torsion)
  have fib : ∀ x ∈ (finite_xCoordSet K E C).toFinset,
      (hdiff.toFinset.filter fun P => f P = x).card = 2 := by
    intro x hx
    rw [Set.Finite.mem_toFinset] at hx
    obtain ⟨y, hxy, hmem⟩ := hx
    have hQ0 : Affine.Point.some x y hxy ≠ (0 : (E⁄K).Point) :=
      Affine.Point.some_ne_zero hxy
    have hne : Affine.Point.some x y hxy ≠ -Affine.Point.some x y hxy := by grind
    rw [Finset.card_eq_two]
    refine ⟨_, _, hne, ?_⟩
    ext P
    simp only [Finset.mem_filter, Set.Finite.mem_toFinset, Set.mem_sdiff,
      Set.mem_singleton_iff, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro ⟨⟨hPC, hP0⟩, hfP⟩
      cases P with
      | zero => exact absurd rfl hP0
      | some x' y' hxy' => exact Affine.Point.X_eq_iff.mp hfP
    · rintro (rfl | rfl)
      · exact ⟨⟨hmem, hQ0⟩, rfl⟩
      · exact ⟨⟨neg_mem hmem, neg_ne_zero.mpr hQ0⟩, by rw [Affine.Point.neg_some]⟩
  -- fiberwise count of the nonzero points, then add the point at infinity back in
  have key : hdiff.toFinset.card = 2 * (finite_xCoordSet K E C).toFinset.card := by
    rw [Finset.card_eq_sum_card_fiberwise Hmaps, Finset.sum_congr rfl fib, Finset.sum_const,
      smul_eq_mul, mul_comm]
  have htf : hCfin.toFinset = insert (0 : (E⁄K).Point) hdiff.toFinset := by
    ext P
    simp only [Set.Finite.mem_toFinset, Finset.mem_insert, Set.mem_sdiff,
      Set.mem_singleton_iff, SetLike.mem_coe]
    grind [C.zero_mem]
  have h0not : (0 : (E⁄K).Point) ∉ hdiff.toFinset := by
    simp [Set.Finite.mem_toFinset]
  calc Nat.card C = (C : Set (E⁄K).Point).ncard := rfl
    _ = hCfin.toFinset.card := Set.ncard_eq_toFinset_card _ hCfin
    _ = (insert (0 : (E⁄K).Point) hdiff.toFinset).card := by rw [htf]
    _ = hdiff.toFinset.card + 1 := Finset.card_insert_of_notMem h0not
    _ = 2 * (kernelPolynomial K E C).natDegree + 1 := by rw [key, hdeg]

end KernelPolynomial

/-! ## Specification of `velT` and `velW` -/

section VelSpec

variable (E : WeierstrassCurve k)

/-- Spec for `velT` in the two-torsion-free case, in terms of the elementary symmetric
functions `sᵢ = velS i h` and `n = deg h` — pins the definition. -/
lemma velT_spec (C : AddSubgroup (E⁄K).Point) [Finite C] {h : k[X]}
    (hh : IsKernelPolynomial K E C h) (h2 : ∀ P ∈ C, P + P = 0 → P = 0) :
    velT E h = 6 * (velS 1 h ^ 2 - 2 * velS 2 h) + E.b₂ * velS 1 h + h.natDegree * E.b₄ :=
  sorry

/-- Spec for `velW` in the two-torsion-free case. -/
lemma velW_spec (C : AddSubgroup (E⁄K).Point) [Finite C] {h : k[X]}
    (hh : IsKernelPolynomial K E C h) (h2 : ∀ P ∈ C, P + P = 0 → P = 0) :
    velW E h = 10 * (velS 1 h ^ 3 - 3 * velS 1 h * velS 2 h + 3 * velS 3 h)
      + 2 * E.b₂ * (velS 1 h ^ 2 - 2 * velS 2 h) + 3 * E.b₄ * velS 1 h
      + h.natDegree * E.b₆ :=
  sorry

end VelSpec

/-! ## Galois-equivariance of isogenies -/

namespace Isogeny

variable {E E' : WeierstrassCurve k}

/-- Galois-equivariance is a theorem: `σ` fixes the coefficients of `φx, φyLin, φyConst`, so
`σ ∘ toHom ∘ σ⁻¹` and `toHom` agree away from the finitely many points over the roots of
`φx.denom`, and two homomorphisms on `E(K)` agreeing off a finite set agree everywhere since
`E(K)` is infinite (`K` is separably closed — this infinitude is the missing mathlib
ingredient). -/
theorem map_galoisAction (φ : Isogeny K E E') (σ : K ≃ₐ[k] K) (P : (E⁄K).Point) :
    φ.toHom (Affine.Point.map σ.toAlgHom P)
      = Affine.Point.map σ.toAlgHom (φ.toHom P) :=
  sorry

/-- Kernels of `k`-isogenies are Galois-stable. -/
theorem ker_galoisStable (φ : Isogeny K E E') : GaloisStable K E φ.toHom.ker := by
  intro σ P hP
  simp_all [AddMonoidHom.mem_ker, map_galoisAction]

end Isogeny

end WeierstrassCurve
