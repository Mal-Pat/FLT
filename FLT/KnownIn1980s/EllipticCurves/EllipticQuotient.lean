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
public import Mathlib.FieldTheory.RatFunc.Basic

/-!

# Quotients of elliptic curves by finite Galois-stable subgroups

Let `E` be an elliptic curve over a field `k` with separable closure `K`. The main theorem
`exists_quotientCurve_isogeny` says that a finite Galois-stable subgroup `C ⊆ E(K)` is the
kernel of a `k`-isogeny from `E` to an elliptic curve over `k`.

Following Kohel, `C` is encoded by its *kernel polynomial* `h(X) = ∏ (X − x_Q)`, the product
over the distinct x-coordinates of the nonzero points of `C`:

* Galois-stability of `C` makes the coefficients of `h` Galois-fixed, so `h` descends to
  `k[X]` (`exists_isKernelPolynomial`, proved). This one lemma is the entire descent layer.
* The quotient curve (`quotientCurve`) is given by Vélu's formulas in Kohel's form: pure
  polynomial arithmetic over `k`, parametrized by `h : k[X]`.
* Galois-equivariance of the isogeny is automatic, because its defining rational maps have
  coefficients in `k`.

## Remaining `sorry`s

1. `velT`, `velW`: Vélu's sums `t`, `w` as expressions in the coefficients of `h`. When `C`
   has trivial 2-torsion these are the power-sum expressions of `velT_spec`/`velW_spec`; in
   general they need Kohel's 2-torsion correction, splitting `h` into a 2-torsion factor
   `gcd(h, 4X³ + b₂X² + 2b₄X + b₆)` and an odd part (Kohel's thesis, §2.4).
2. `isElliptic_quotientCurve`: nonvanishing of the quotient discriminant.
3. `exists_quotientIsogeny`: the rational maps of the isogeny (denominators `h²` and `h³`),
   surjectivity, and the kernel computation — the algebraic heart.
4. `Isogeny.map_galoisAction`: needs "two homomorphisms on `E(K)` agreeing off a finite set
   agree", i.e. the infinitude of `E(K)` for `K` separably closed, not yet in mathlib.

## Faithfulness caveat in characteristic `p`

Over a perfect `k` of characteristic `p` (so `K = k̄`), composing the quotient isogeny with
Frobenius gives another witness of the main theorem with the same kernel on points, so `E'`
is pinned only up to purely inseparable isogeny; a separability condition on the rational
maps would remove this slack. (Over imperfect `k` the `surjective` field already rules out
Frobenius, and in characteristic zero there is no slack.)
-/

@[expose] public section

open Polynomial

open scoped WeierstrassCurve.Affine

namespace WeierstrassCurve

variable {k : Type*} [Field k] (K : Type*) [Field K] [Algebra k K] [IsSepClosure k K]
  [DecidableEq K]

/-! ## Galois-stability and the kernel polynomial over `K` -/

section KernelPolynomial

variable (E : WeierstrassCurve k)

/-- `C` is stable under the Galois action `Affine.Point.map σ.toAlgHom`. -/
def GaloisStable (C : AddSubgroup (E⁄K).Point) : Prop :=
  ∀ σ : K ≃ₐ[k] K, ∀ P ∈ C, Affine.Point.map σ.toAlgHom P ∈ C

omit [IsSepClosure k K] in
/-- The set of x-coordinates of the nonzero points of a finite `C` is finite. -/
lemma finite_xCoordSet (C : AddSubgroup (E⁄K).Point) [Finite C] :
    {x : K | ∃ (y : K) (hxy : (E⁄K).Nonsingular x y),
      Affine.Point.some x y hxy ∈ C}.Finite := by
  refine ((Set.toFinite (C : Set (E⁄K).Point)).image
    fun P => match P with | .zero => 0 | .some x _ _ => x).subset ?_
  rintro x ⟨y, hxy, hmem⟩
  exact ⟨Affine.Point.some x y hxy, hmem, rfl⟩

/-- The kernel polynomial of `C` over `K`: `∏ (X − x)` over the distinct x-coordinates of
the nonzero points of `C`. (`Q` and `−Q` share an x-coordinate, so this is the standard
squarefree kernel polynomial, uniform in the presence of 2-torsion.) -/
noncomputable def kernelPolynomial (C : AddSubgroup (E⁄K).Point) [Finite C] : K[X] :=
  ∏ x ∈ (finite_xCoordSet K E C).toFinset, (X - Polynomial.C x)

omit [IsSepClosure k K] in
lemma kernelPolynomial_monic (C : AddSubgroup (E⁄K).Point) [Finite C] :
    (kernelPolynomial K E C).Monic :=
  monic_prod_of_monic _ _ fun x _ => monic_X_sub_C x

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

omit [IsSepClosure k K] in
/-- The Galois action permutes the nonzero points of a stable `C`, hence permutes their
x-coordinates, hence fixes the kernel polynomial. -/
lemma kernelPolynomial_map_galois (C : AddSubgroup (E⁄K).Point) [Finite C]
    (hC : GaloisStable K E C) (σ : K ≃ₐ[k] K) :
    (kernelPolynomial K E C).map (σ : K →+* K) = kernelPolynomial K E C := by
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
  conv_rhs => rw [kernelPolynomial, ← himg,
    Finset.prod_image fun x _ y _ hxy => σ.injective hxy]
  simp [kernelPolynomial, Polynomial.map_prod]

/-! ## Descent -/

/-- `h : k[X]` is the kernel polynomial of `C`, seen from `k`. -/
def IsKernelPolynomial (C : AddSubgroup (E⁄K).Point) [Finite C] (h : k[X]) : Prop :=
  h.Monic ∧ h.map (algebraMap k K) = kernelPolynomial K E C

/-- Descent: A Galois-stable `C` has kernel polynomial defined over `k`: each coefficient
is `Gal(K/k)`-fixed by `kernelPolynomial_map_galois`, and the fixed field of a separable
closure is `k`. -/
lemma exists_isKernelPolynomial (C : AddSubgroup (E⁄K).Point) [Finite C]
    (hC : GaloisStable K E C) :
    ∃ h : k[X], IsKernelPolynomial K E C h := by
  have hmem : kernelPolynomial K E C ∈ Polynomial.lifts (algebraMap k K) := by
    rw [Polynomial.lifts_iff_coeff_lifts]
    intro n
    rw [InfiniteGalois.mem_range_algebraMap_iff_fixed]
    intro σ
    conv_rhs => rw [← kernelPolynomial_map_galois K E C hC σ]
    rw [Polynomial.coeff_map]
    rfl
  obtain ⟨h, hh⟩ := (Polynomial.mem_lifts _).mp hmem
  exact ⟨h, Polynomial.monic_of_injective (algebraMap k K).injective
    (by rw [hh]; exact kernelPolynomial_monic K E C), hh⟩

omit [IsSepClosure k K] in
/-- The descended kernel polynomial is unique, so downstream statements may take `h` as a
hypothesis without ambiguity. -/
lemma IsKernelPolynomial.unique (C : AddSubgroup (E⁄K).Point) [Finite C] {h₁ h₂ : k[X]}
    (H₁ : IsKernelPolynomial K E C h₁) (H₂ : IsKernelPolynomial K E C h₂) :
    h₁ = h₂ :=
  Polynomial.map_injective _ (algebraMap k K).injective (H₁.2.trans H₂.2.symm)

end KernelPolynomial

/-! ## The Kohel construction over `k`

Pure polynomial arithmetic over `k`, parametrized by an abstract monic `h : k[X]`; the
connection to `C` enters only through an `IsKernelPolynomial` hypothesis where needed. -/

/-- The `i`-th signed coefficient of `h`, i.e. (for `h` monic and split) the `i`-th
elementary symmetric function of its roots. The guard makes `velS i h = 0` — the honest
`eᵢ` — when `i > deg h`, where `ℕ`-subtraction would otherwise produce a wrong nonzero
value. -/
noncomputable def velS (i : ℕ) (h : k[X]) : k :=
  if i ≤ h.natDegree then (-1) ^ i * h.coeff (h.natDegree - i) else 0

/-- Vélu's `t`, as an expression in the coefficients of `E` and `h`. `sorry`d: with trivial
2-torsion it is the power-sum expression of `velT_spec`; in general the 2-torsion points
contribute half the paired contribution, requiring Kohel's correction (thesis §2.4). -/
noncomputable def velT (E : WeierstrassCurve k) (h : k[X]) : k := sorry

/-- Vélu's `w`. `sorry`d, same status as `velT`; the trivial-2-torsion form is in
`velW_spec`. -/
noncomputable def velW (E : WeierstrassCurve k) (h : k[X]) : k := sorry

/-- The quotient curve `E/C` (Vélu/Kohel): `a₁, a₂, a₃` unchanged, `a₄' = a₄ − 5t`,
`a₆' = a₆ − b₂t − 7w`. -/
noncomputable def quotientCurve (E : WeierstrassCurve k) (h : k[X]) : WeierstrassCurve k where
  a₁ := E.a₁
  a₂ := E.a₂
  a₃ := E.a₃
  a₄ := E.a₄ - 5 * velT E h
  a₆ := E.a₆ - E.b₂ * velT E h - 7 * velW E h

section MainStatements

variable (E : WeierstrassCurve k)

/-- Spec for `velT` in the two-torsion-free case, in terms of the elementary symmetric
functions `sᵢ = velS i h` and `n = deg h` — pins the `sorry`d definition. -/
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

/-- The quotient of an elliptic curve by a genuine kernel polynomial is elliptic
(nonvanishing discriminant). -/
theorem isElliptic_quotientCurve [E.IsElliptic]
    (C : AddSubgroup (E⁄K).Point) [Finite C] {h : k[X]}
    (hh : IsKernelPolynomial K E C h) :
    (quotientCurve E h).IsElliptic :=
  sorry

/-! ## Isogenies -/

/-- A `k`-isogeny `E → E'`, carried by rational maps over `k`:
`(x, y) ↦ (φx(x), φyLin(x)·y + φyConst(x))`. Rational functions are evaluated as `num/denom`
via `eval₂` (mathlib's `RatFunc.eval` forces source and target into the same universe).
Since the defining maps have coefficients in `k`, Galois-equivariance is a theorem
(`Isogeny.map_galoisAction`) rather than a field of the structure. -/
structure Isogeny (E E' : WeierstrassCurve k) where
  /-- x-coordinate map, a rational function over `k`. -/
  φx : RatFunc k
  /-- coefficient of `y` in the y-coordinate map. -/
  φyLin : RatFunc k
  /-- y-independent part of the y-coordinate map. -/
  φyConst : RatFunc k
  /-- the induced homomorphism on `K`-points. -/
  toHom : (E⁄K).Point →+ (E'⁄K).Point
  /-- coherence: away from the poles of `φx`, `toHom` evaluates the rational maps. -/
  toHom_some :
    ∀ (x y : K) (hxy : (E⁄K).Nonsingular x y),
      φx.denom.eval₂ (algebraMap k K) x ≠ 0 →
      ∃ hxy' : (E'⁄K).Nonsingular
          (φx.num.eval₂ (algebraMap k K) x / φx.denom.eval₂ (algebraMap k K) x)
          (φyLin.num.eval₂ (algebraMap k K) x / φyLin.denom.eval₂ (algebraMap k K) x * y
            + φyConst.num.eval₂ (algebraMap k K) x / φyConst.denom.eval₂ (algebraMap k K) x),
        toHom (Affine.Point.some x y hxy) = Affine.Point.some _ _ hxy'
  /-- surjectivity on `K`-points. -/
  surjective : Function.Surjective toHom
  /-- finiteness of the kernel. -/
  finite_ker : Finite toHom.ker

namespace Isogeny

variable {E' : WeierstrassCurve k} {E}

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

/-! ## The quotient isogeny and the main theorem -/

/-- The quotient isogeny: There is a `k`-isogeny `E → E/C` with kernel exactly `C`:
`φx` has denominator `h²` and numerator determined by `h` and `E` (Kohel §2.4; Washington
§12.3), the y-maps have denominator `h³`, and `φx` has poles exactly at `x(C ∖ {0})`, the
roots of `h`. -/
theorem exists_quotientIsogeny [E.IsElliptic]
    (C : AddSubgroup (E⁄K).Point) [Finite C] {h : k[X]}
    (hh : IsKernelPolynomial K E C h) :
    ∃ φ : Isogeny K E (quotientCurve E h), φ.toHom.ker = C :=
  sorry

/-- If `E/k` is elliptic and `C ⊆ E(K)` is a finite Galois-stable
subgroup, there are an elliptic curve `E'` over `k` and a `k`-isogeny `E → E'` with kernel
exactly `C`. -/
theorem exists_quotientCurve_isogeny [E.IsElliptic]
    (C : AddSubgroup (E⁄K).Point) [Finite C] (hC : GaloisStable K E C) :
    ∃ (E' : WeierstrassCurve k) (_ : E'.IsElliptic) (φ : Isogeny K E E'),
      φ.toHom.ker = C := by
  obtain ⟨h, hh⟩ := exists_isKernelPolynomial K E C hC
  obtain ⟨φ, hφ⟩ := exists_quotientIsogeny K E C hh
  exact ⟨quotientCurve E h, isElliptic_quotientCurve K E C hh, φ, hφ⟩

end MainStatements

end WeierstrassCurve
