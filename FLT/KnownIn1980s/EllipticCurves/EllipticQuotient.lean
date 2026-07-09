/-
Copyright (c) 2026 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Malhar A. Patel
-/
module

public import FLT.Slop.EllipticQuotient.Descent
public import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
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

## File organisation

This file contains the definitions and the main statements only. Helper lemmas live in
`FLT.Slop.EllipticQuotient.Descent` (imported here; the Galois-descent chain, phrased
without this file's definitions) and `FLT.Slop.EllipticQuotient.Lemmas` (imports this file;
all other supporting lemmas, including the specification lemmas pinning `velT`, `velW` and
Galois-equivariance of `Isogeny`).

## Remaining `sorry`s

In this file:
1. `isElliptic_quotientCurve`: nonvanishing of the quotient discriminant.
2. `exists_quotientIsogeny`: the rational maps of the isogeny (denominators `h²` and `h³`),
   surjectivity, and the kernel computation — the algebraic heart.

In `FLT.Slop.EllipticQuotient.Lemmas`:
3. `velT_spec`, `velW_spec`: the defined `velT`, `velW` evaluate to the power-sum
   expressions when `C` has trivial 2-torsion.
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

/-! ## Definitions -/

section KernelPolynomial

variable (E : WeierstrassCurve k)

/-- `C` is stable under the Galois action `Affine.Point.map σ.toAlgHom`. -/
def GaloisStable (C : AddSubgroup (E⁄K).Point) : Prop :=
  ∀ σ : K ≃ₐ[k] K, ∀ P ∈ C, Affine.Point.map σ.toAlgHom P ∈ C

/-- The kernel polynomial of `C` over `K`: `∏ (X − x)` over the distinct x-coordinates of
the nonzero points of `C` (a finite set, `finite_xCoordSet`). `Q` and `−Q` share an
x-coordinate, so this is the standard squarefree kernel polynomial, uniform in the presence
of 2-torsion. -/
noncomputable def kernelPolynomial (C : AddSubgroup (E⁄K).Point) [Finite C] : K[X] :=
  ∏ x ∈ (finite_xCoordSet K E C).toFinset, (X - Polynomial.C x)

/-- `h : k[X]` is the kernel polynomial of `C`, seen from `k`. Such an `h` is unique
(`IsKernelPolynomial.unique`), so downstream statements may take it as a hypothesis. -/
def IsKernelPolynomial (C : AddSubgroup (E⁄K).Point) [Finite C] (h : k[X]) : Prop :=
  h.Monic ∧ h.map (algebraMap k K) = kernelPolynomial K E C

end KernelPolynomial

/-- The `i`-th signed coefficient of `h`, i.e. (for `h` monic and split) the `i`-th
elementary symmetric function of its roots. The guard makes `velS i h = 0` — the honest
`eᵢ` — when `i > deg h`, where `ℕ`-subtraction would otherwise produce a wrong nonzero
value. -/
noncomputable def velS (i : ℕ) (h : k[X]) : k :=
  if i ≤ h.natDegree then (-1) ^ i * h.coeff (h.natDegree - i) else 0

open Classical in
/-- Vélu's `t`, in Kohel's form (thesis §2.4): split `h` into its 2-torsion factor
`g = gcd(h, 4X³ + b₂X² + 2b₄X + b₆)` and odd part `h₀ = h/g`. Each pair `{Q, −Q}` of
non-2-torsion points contributes `6x² + b₂x + b₄`, summed over the roots of `h₀` via their
power sums, and each 2-torsion point contributes half that. In characteristic 2 a genuine
`g` has degree at most 1 and the halved contribution at its root `x₀` is `x₀² + a₄ + a₁y₀`,
where `a₁y₀` is the unique square root of `a₁²(x₀³ + a₂x₀² + a₄x₀ + a₆)` (junk `0` if there
is none in `k`). -/
noncomputable def velT (E : WeierstrassCurve k) (h : k[X]) : k :=
  let g := normalize (EuclideanDomain.gcd h E.twoTorsionPolynomial.toPoly)
  let h₀ := h /ₘ g
  6 * (velS 1 h₀ ^ 2 - 2 * velS 2 h₀) + E.b₂ * velS 1 h₀ + h₀.natDegree * E.b₄
    + if (2 : k) = 0 then
        if g.natDegree = 1 then
          let x₀ := -g.coeff 0
          x₀ ^ 2 + E.a₄ +
            if H : ∃ s : k, s ^ 2 = E.a₁ ^ 2 * (x₀ ^ 3 + E.a₂ * x₀ ^ 2 + E.a₄ * x₀ + E.a₆)
            then H.choose else 0
        else 0
      else (6 * (velS 1 g ^ 2 - 2 * velS 2 g) + E.b₂ * velS 1 g + g.natDegree * E.b₄) / 2

open Classical in
/-- Vélu's `w`, with the same splitting `h = g·h₀` as `velT`: a pair `{Q, −Q}` contributes
`10x³ + 2b₂x² + 3b₄x + b₆`, and a 2-torsion point contributes `x₀·t_Q` (its `u_Q`-term
`4x₀³ + b₂x₀² + 2b₄x₀ + b₆` vanishes), i.e. `x₀` times its `velT` contribution. -/
noncomputable def velW (E : WeierstrassCurve k) (h : k[X]) : k :=
  let g := normalize (EuclideanDomain.gcd h E.twoTorsionPolynomial.toPoly)
  let h₀ := h /ₘ g
  10 * (velS 1 h₀ ^ 3 - 3 * velS 1 h₀ * velS 2 h₀ + 3 * velS 3 h₀)
    + 2 * E.b₂ * (velS 1 h₀ ^ 2 - 2 * velS 2 h₀) + 3 * E.b₄ * velS 1 h₀
    + h₀.natDegree * E.b₆
    + if (2 : k) = 0 then
        if g.natDegree = 1 then
          let x₀ := -g.coeff 0
          x₀ * (x₀ ^ 2 + E.a₄ +
            if H : ∃ s : k, s ^ 2 = E.a₁ ^ 2 * (x₀ ^ 3 + E.a₂ * x₀ ^ 2 + E.a₄ * x₀ + E.a₆)
            then H.choose else 0)
        else 0
      else
        (6 * (velS 1 g ^ 3 - 3 * velS 1 g * velS 2 g + 3 * velS 3 g)
          + E.b₂ * (velS 1 g ^ 2 - 2 * velS 2 g) + E.b₄ * velS 1 g) / 2

/-- The quotient curve `E/C` (Vélu/Kohel): `a₁, a₂, a₃` unchanged, `a₄' = a₄ − 5t`,
`a₆' = a₆ − b₂t − 7w`. -/
noncomputable def quotientCurve (E : WeierstrassCurve k) (h : k[X]) : WeierstrassCurve k where
  a₁ := E.a₁
  a₂ := E.a₂
  a₃ := E.a₃
  a₄ := E.a₄ - 5 * velT E h
  a₆ := E.a₆ - E.b₂ * velT E h - 7 * velW E h

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

/-! ## Main statements -/

section MainStatements

variable (E : WeierstrassCurve k)

/-- **Descent.** A Galois-stable `C` has kernel polynomial defined over `k`: each
coefficient is `Gal(K/k)`-fixed, and the fixed field of a separable closure is `k`. -/
lemma exists_isKernelPolynomial (C : AddSubgroup (E⁄K).Point) [Finite C]
    (hC : GaloisStable K E C) :
    ∃ h : k[X], IsKernelPolynomial K E C h :=
  exists_monic_map_eq_prod_X_sub_C_xCoordSet K E C hC

/-- The quotient of an elliptic curve by a genuine kernel polynomial is elliptic
(nonvanishing discriminant). -/
theorem isElliptic_quotientCurve [E.IsElliptic]
    (C : AddSubgroup (E⁄K).Point) [Finite C] {h : k[X]}
    (hh : IsKernelPolynomial K E C h) :
    (quotientCurve E h).IsElliptic :=
  sorry

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
