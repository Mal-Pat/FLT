/-
Copyright (c) 2026 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Buzzard
-/
module

public import Mathlib.Algebra.Polynomial.Lifts
public import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
public import Mathlib.FieldTheory.Galois.Infinite
public import Mathlib.FieldTheory.IsSepClosed
public import Mathlib.FieldTheory.RatFunc.Basic

/-!

# Quotient by a finite Galois-stable subgroup — kernel-polynomial (Kohel) blueprint

Third variant, restructured for EASE OF FORMALIZATION. The previous architecture was
"construct over `kˢᵉᵖ` by Vélu, then descend curve + map to `k`". Here the subgroup `C` is
encoded by its KERNEL POLYNOMIAL `h(X) = ∏ (X − x_Q)` (product over the distinct
x-coordinates of the nonzero points of `C`), and:

  * Galois-stability of `C` ⟺ the coefficients of `h` are Galois-fixed ⟹ `h` descends to
    `k[X]`. This ONE polynomial-coefficient lemma (`exists_isKernelPolynomial`, **proved**)
    is the entire descent layer; the old `exists_quotient_descends` (descend a curve) and the
    equivariance bookkeeping for the map disappear.
  * The construction (`quotientCurve`, `quotientIsogeny`) is polynomial arithmetic OVER `k`,
    parametrized by `h : k[X]`. No base change, no `IsScalarTower` juggling, during
    construction.
  * Galois-equivariance of the isogeny is automatic (coefficients in `k`), as in the one-def
    file — but now the construction is equivariant by fiat too.

Definition count is deliberately larger than the one-def file (the user's trade-off: more
definitions, easier proofs). Each definition is either explicit polynomial arithmetic or a
named `sorry` isolating one known formula.

## Where the remaining difficulty lives (the honest list)
  1. `velT`, `velW` in full generality — Vélu's sums as expressions in `h`'s coefficients.
     The clean power-sum formulas hold when `C` has trivial 2-torsion (stated as spec lemmas
     `velT_spec`, `velW_spec`); nontrivial 2-torsion needs Kohel's correction (his thesis
     §2.4 splits `h` into a 2-torsion factor and the rest). These two `def`s are the formula
     work.
  2. `isElliptic_quotientCurve` — nonvanishing of the quotient discriminant.
  3. `quotientIsogeny` + `ker_quotientIsogeny` — the rational maps (denominators `h²`, `h³`)
     and the kernel computation; the algebraic heart, as before, but now over `k`.
  4. `Isogeny.map_galoisAction` — needs "two homomorphisms on `E(K)` agreeing off a finite
     set agree", i.e. the infinitude of `E(K)` for `K` separably closed, which is not yet
     in mathlib.

Everything else (§§1–2 in full, and the assembly of the main theorem from the leaves above)
is **proved** below.

## Faithfulness caveat (characteristic `p`, perfect base)
Over a perfect field `k` of characteristic `p` (so `K = k̄`), composing the quotient isogeny
with Frobenius gives another witness of the main theorem with the same kernel on points, so
`E'` is pinned only up to purely inseparable isogeny; a separability witness on the rational
maps would remove the slack. Over imperfect `k` the `surjective` field already rules this
out (Frobenius is not surjective on `K`-points when `K = kˢᵉᵖ` is imperfect), and in
characteristic zero there is no slack at all.

## Setting
`K` is any separable closure of `k` (`[IsSepClosure k K]`); instantiate
`K := SeparableClosure k`. Curves use the `WeierstrassCurve k` + `[IsElliptic]` typeclass
API. The Galois action on points is the existing `Affine.Point.map σ.toAlgHom`.
-/

@[expose] public section

open Polynomial

open scoped WeierstrassCurve.Affine

namespace WeierstrassCurve

variable {k : Type*} [Field k] (K : Type*) [Field K] [Algebra k K] [IsSepClosure k K]
  [DecidableEq K]

/-! ## §1 Galois-stability and the kernel polynomial over `K` -/

section KernelPolynomial

variable (E : WeierstrassCurve k)

/-- `C` is stable under the Galois action `Affine.Point.map σ.toAlgHom` (existing API). -/
def GaloisStable (C : AddSubgroup (E⁄K).Point) : Prop :=
  ∀ σ : K ≃ₐ[k] K, ∀ P ∈ C, Affine.Point.map σ.toAlgHom P ∈ C

/-- The set of x-coordinates of the nonzero points of `C`. -/
def xCoordSet (C : AddSubgroup (E⁄K).Point) : Set K :=
  {x | ∃ (y : K) (hxy : (E⁄K).Nonsingular x y), Affine.Point.some x y hxy ∈ C}

omit [IsSepClosure k K] in
lemma finite_xCoordSet (C : AddSubgroup (E⁄K).Point) [Finite C] :
    (xCoordSet K E C).Finite := by
  have hC : (C : Set (E⁄K).Point).Finite := Set.toFinite _
  refine (hC.image fun P => match P with | .zero => 0 | .some x _ _ => x).subset ?_
  rintro x ⟨y, hxy, hmem⟩
  exact ⟨Affine.Point.some x y hxy, hmem, rfl⟩

/-- The kernel polynomial of `C` over `K`: `∏ (X − x)` over the DISTINCT x-coordinates of the
nonzero points of `C` (each counted once; `Q` and `−Q` share an x-coordinate, so this is the
standard squarefree kernel polynomial, uniform in the presence of 2-torsion). -/
noncomputable def kernelPolynomial (C : AddSubgroup (E⁄K).Point) [Finite C] : K[X] :=
  ∏ x ∈ (finite_xCoordSet K E C).toFinset, (X - Polynomial.C x)

omit [IsSepClosure k K] in
lemma kernelPolynomial_monic (C : AddSubgroup (E⁄K).Point) [Finite C] :
    (kernelPolynomial K E C).Monic :=
  monic_prod_of_monic _ _ fun x _ => monic_X_sub_C x

omit [IsSepClosure k K] in
/-- Nonzero points of `C` come in pairs `{Q, −Q}` sharing an x-coordinate, so when `C` has
trivial 2-torsion, `#C = 2·deg h + 1`. (Cheap, useful for the degree bookkeeping later.) -/
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
  -- `f` maps the nonzero points of `C` into the x-coordinate set
  have Hmaps : ∀ P ∈ hdiff.toFinset, f P ∈ (finite_xCoordSet K E C).toFinset := by
    intro P hP
    rw [Set.Finite.mem_toFinset] at hP ⊢
    obtain ⟨hPC, hP0⟩ := hP
    cases P with
    | zero => exact absurd rfl hP0
    | some x' y' hxy' => exact ⟨y', hxy', hPC⟩
  -- ... with every fiber being a pair `{Q, -Q}` of size exactly two (no 2-torsion)
  have fib : ∀ x ∈ (finite_xCoordSet K E C).toFinset,
      (hdiff.toFinset.filter fun P => f P = x).card = 2 := by
    intro x hx
    rw [Set.Finite.mem_toFinset] at hx
    obtain ⟨y, hxy, hmem⟩ := hx
    have hQ0 : Affine.Point.some x y hxy ≠ (0 : (E⁄K).Point) :=
      Affine.Point.some_ne_zero hxy
    have hne : Affine.Point.some x y hxy ≠ -Affine.Point.some x y hxy := by
      intro hcontra
      refine hQ0 (h2 _ hmem ?_)
      nth_rewrite 2 [hcontra]
      exact add_neg_cancel _
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
      · refine ⟨⟨neg_mem hmem, fun h0 => hQ0 (neg_eq_zero.mp h0)⟩, ?_⟩
        rw [Affine.Point.neg_some]
  -- fiberwise count of the nonzero points
  have key : hdiff.toFinset.card = 2 * (finite_xCoordSet K E C).toFinset.card := by
    rw [Finset.card_eq_sum_card_fiberwise Hmaps, Finset.sum_congr rfl fib, Finset.sum_const,
      smul_eq_mul, mul_comm]
  -- add the point at infinity back in
  have htf : hCfin.toFinset = insert (0 : (E⁄K).Point) hdiff.toFinset := by
    ext P
    simp only [Set.Finite.mem_toFinset, Finset.mem_insert, Set.mem_sdiff,
      Set.mem_singleton_iff]
    constructor
    · intro hP
      rcases eq_or_ne P 0 with h0 | h0
      · exact Or.inl h0
      · exact Or.inr ⟨hP, h0⟩
    · rintro (rfl | ⟨hP, -⟩)
      · exact C.zero_mem
      · exact hP
  have h0not : (0 : (E⁄K).Point) ∉ hdiff.toFinset := by
    simp [Set.Finite.mem_toFinset]
  calc Nat.card C = (C : Set (E⁄K).Point).ncard := rfl
    _ = hCfin.toFinset.card := Set.ncard_eq_toFinset_card _ hCfin
    _ = (insert (0 : (E⁄K).Point) hdiff.toFinset).card := by rw [htf]
    _ = hdiff.toFinset.card + 1 := Finset.card_insert_of_notMem h0not
    _ = 2 * (kernelPolynomial K E C).natDegree + 1 := by rw [key, hdeg]

omit [IsSepClosure k K] in
/-- **Key lemma (all of equivariance in one line).** The Galois action permutes the nonzero
points of a stable `C`, hence permutes their x-coordinates, hence fixes `h`. -/
lemma kernelPolynomial_map_galois (C : AddSubgroup (E⁄K).Point) [Finite C]
    (hC : GaloisStable K E C) (σ : K ≃ₐ[k] K) :
    (kernelPolynomial K E C).map (σ : K →+* K) = kernelPolynomial K E C := by
  -- the Galois action maps the x-coordinate set into itself ...
  have hsub : ∀ τ : K ≃ₐ[k] K, ∀ x ∈ xCoordSet K E C, τ x ∈ xCoordSet K E C := by
    rintro τ x ⟨y, hxy, hmem⟩
    have h2 := hC τ _ hmem
    rw [Affine.Point.map_some] at h2
    exact ⟨τ y, _, h2⟩
  -- ... hence (using `τ := σ⁻¹` too) permutes it
  have himg : (finite_xCoordSet K E C).toFinset.image σ = (finite_xCoordSet K E C).toFinset := by
    refine Finset.Subset.antisymm ?_ ?_ <;> intro x hx <;>
      simp only [Finset.mem_image, Set.Finite.mem_toFinset] at hx ⊢
    · obtain ⟨y, hy, rfl⟩ := hx
      exact hsub σ y hy
    · exact ⟨σ.symm x, hsub σ.symm x hx, σ.apply_symm_apply x⟩
  calc (kernelPolynomial K E C).map (σ : K →+* K)
      = ∏ x ∈ (finite_xCoordSet K E C).toFinset, (X - Polynomial.C (σ x)) := by
        rw [kernelPolynomial, Polynomial.map_prod]
        simp only [Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C, RingHom.coe_coe]
    _ = ∏ x ∈ (finite_xCoordSet K E C).toFinset.image σ, (X - Polynomial.C x) := by
        rw [Finset.prod_image fun x _ y _ hxy => σ.injective hxy]
    _ = kernelPolynomial K E C := by rw [himg, kernelPolynomial]

/-! ## §2 Descent — the whole descent layer is one coefficient lemma -/

/-- `h : k[X]` is THE kernel polynomial of `C`, seen from `k`. -/
def IsKernelPolynomial (C : AddSubgroup (E⁄K).Point) [Finite C] (h : k[X]) : Prop :=
  h.Monic ∧ h.map (algebraMap k K) = kernelPolynomial K E C

/-- **Descent.** A Galois-stable `C` has kernel polynomial defined over `k`: each coefficient
is fixed by `Gal(K/k)` (by `kernelPolynomial_map_galois`), and the fixed field of a separable
closure is `k`. This single lemma replaces descending the quotient curve and the quotient
map. -/
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
/-- The descended kernel polynomial is unique (`Polynomial.map` of a field embedding is
injective), so downstream statements may take `h` as a hypothesis without ambiguity. -/
lemma IsKernelPolynomial.unique (C : AddSubgroup (E⁄K).Point) [Finite C] {h₁ h₂ : k[X]}
    (H₁ : IsKernelPolynomial K E C h₁) (H₂ : IsKernelPolynomial K E C h₂) :
    h₁ = h₂ :=
  Polynomial.map_injective _ (algebraMap k K).injective (H₁.2.trans H₂.2.symm)

end KernelPolynomial

/-! ## §3 The Kohel construction over `k` — pure polynomial arithmetic, no base change

Everything below is parametrized by an abstract monic `h : k[X]`; the connection to `C`
enters only through an `IsKernelPolynomial` hypothesis where mathematically needed.

The three `velSᵢ` are the signed coefficients of `h`, i.e. the elementary symmetric
functions of the kernel x-coordinates. The guards `i ≤ h.natDegree` matter: without them,
`ℕ`-subtraction junk (`h.natDegree - i = 0`) would make `velSᵢ` WRONG (nonzero instead of
`eᵢ = 0`) whenever `natDegree h < i`, and the spec lemmas `velT_spec`/`velW_spec` would be
false for kernels of order `≤ 5`. With the guards they are the honest `eᵢ` in every
degree. -/

/-- First signed coefficient: `s₁ = Σ x_Q` (sum of the kernel x-coordinates). -/
noncomputable def velS₁ (h : k[X]) : k :=
  if 1 ≤ h.natDegree then -(h.coeff (h.natDegree - 1)) else 0

/-- Second signed coefficient: `s₂ = Σ_{i<j} x_i x_j`. -/
noncomputable def velS₂ (h : k[X]) : k :=
  if 2 ≤ h.natDegree then h.coeff (h.natDegree - 2) else 0

/-- Third signed coefficient: `s₃ = Σ_{i<j<l} x_i x_j x_l`. -/
noncomputable def velS₃ (h : k[X]) : k :=
  if 3 ≤ h.natDegree then -(h.coeff (h.natDegree - 3)) else 0

/-- Vélu's `t`, as an explicit expression in `E`'s coefficients and `h`'s coefficients.

SORRY-DEF (formula work, item 1 of the header list). When the kernel has trivial 2-torsion
this is the power-sum expression `6(s₁² − 2s₂) + b₂s₁ + n·b₄` where `n = deg h` (spec:
`velT_spec`); with 2-torsion present, the per-point contribution of a 2-torsion point is
half the paired contribution, so the definition must include Kohel's correction term
(thesis §2.4, splitting `h` into its 2-torsion factor `gcd(h, 4X³ + b₂X² + 2b₄X + b₆)` and
the odd part). -/
noncomputable def velT (E : WeierstrassCurve k) (h : k[X]) : k := sorry

/-- Vélu's `w`. SORRY-DEF, same status as `velT`; trivial-2-torsion form is
`10(s₁³ − 3s₁s₂ + 3s₃) + 2b₂(s₁² − 2s₂) + 3b₄s₁ + n·b₆` (spec: `velW_spec`). -/
noncomputable def velW (E : WeierstrassCurve k) (h : k[X]) : k := sorry

/-- **The quotient curve `E/C`, explicitly.** Vélu/Kohel: `a₁, a₂, a₃` unchanged,
`a₄' = a₄ − 5t`, `a₆' = a₆ − b₂t − 7w`. Uniform in all cases once `t, w` are correct. -/
noncomputable def quotientCurve (E : WeierstrassCurve k) (h : k[X]) : WeierstrassCurve k where
  a₁ := E.a₁
  a₂ := E.a₂
  a₃ := E.a₃
  a₄ := E.a₄ - 5 * velT E h
  a₆ := E.a₆ - E.b₂ * velT E h - 7 * velW E h

section MainStatements

variable (E : WeierstrassCurve k)

/-- Spec for `velT` in the two-torsion-free case — pins the sorried definition. -/
lemma velT_spec (C : AddSubgroup (E⁄K).Point) [Finite C] {h : k[X]}
    (hh : IsKernelPolynomial K E C h) (h2 : ∀ P ∈ C, P + P = 0 → P = 0) :
    velT E h = 6 * (velS₁ h ^ 2 - 2 * velS₂ h) + E.b₂ * velS₁ h + h.natDegree * E.b₄ :=
  sorry

/-- Spec for `velW` in the two-torsion-free case. -/
lemma velW_spec (C : AddSubgroup (E⁄K).Point) [Finite C] {h : k[X]}
    (hh : IsKernelPolynomial K E C h) (h2 : ∀ P ∈ C, P + P = 0 → P = 0) :
    velW E h = 10 * (velS₁ h ^ 3 - 3 * velS₁ h * velS₂ h + 3 * velS₃ h)
      + 2 * E.b₂ * (velS₁ h ^ 2 - 2 * velS₂ h) + 3 * E.b₄ * velS₁ h
      + h.natDegree * E.b₆ :=
  sorry

/-- The quotient of an elliptic curve by a genuine kernel polynomial is elliptic
(nonvanishing discriminant). Item 2 of the header list. -/
theorem isElliptic_quotientCurve [E.IsElliptic]
    (C : AddSubgroup (E⁄K).Point) [Finite C] {h : k[X]}
    (hh : IsKernelPolynomial K E C h) :
    (quotientCurve E h).IsElliptic :=
  sorry

/-! ## §4 Isogenies (the same single structure as the one-def file) -/

/-- A `k`-isogeny `E → E'`, carried by rational maps over `k`:
`(x, y) ↦ (φx(x), φyLin(x)·y + φyConst(x))`. Same structure as the one-def blueprint, now
parametrized by the separable closure `K` and stated for plain Weierstrass curves
(ellipticity is imposed where needed, not baked in). Rational functions are evaluated as
`num/denom` via `eval₂` (mathlib's `RatFunc.eval` forces source and target into the same
universe). Galois-equivariance is a THEOREM (`Isogeny.map_galoisAction`), since the defining
maps have coefficients in `k`. -/
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
`σ ∘ toHom ∘ σ⁻¹` and `toHom` agree wherever the coherence clause bites, i.e. away from the
finitely many points over the roots of `φx.denom`; two homomorphisms on `E(K)` agreeing off
a finite set agree everywhere since `E(K)` is infinite (`K` is separably closed — this
infinitude is the missing mathlib ingredient, item 4 of the header list). -/
theorem map_galoisAction (φ : Isogeny K E E') (σ : K ≃ₐ[k] K) (P : (E⁄K).Point) :
    φ.toHom (Affine.Point.map σ.toAlgHom P)
      = Affine.Point.map σ.toAlgHom (φ.toHom P) :=
  sorry

/-- Kernels of `k`-isogenies are Galois-stable (immediate from equivariance). -/
theorem ker_galoisStable (φ : Isogeny K E E') : GaloisStable K E φ.toHom.ker := by
  intro σ P hP
  rw [AddMonoidHom.mem_ker] at hP ⊢
  rw [map_galoisAction K φ σ P, hP]
  exact _root_.map_zero _

end Isogeny

/-! ## §5 The quotient isogeny and the main theorem -/

/-- **The quotient isogeny `E → E/C`.** SORRY-DEF (item 3): supplies the rational maps —
`φx` with denominator `h²` and numerator determined by `h` and `E` (Kohel §2.4; Washington
§12.3), the y-maps with denominator `h³` — together with the induced point map, coherence,
surjectivity, and finite kernel. Every field of the structure is constructed over `k`. -/
noncomputable def quotientIsogeny [E.IsElliptic]
    (C : AddSubgroup (E⁄K).Point) [Finite C] {h : k[X]}
    (hh : IsKernelPolynomial K E C h) :
    Isogeny K E (quotientCurve E h) :=
  sorry

/-- The kernel of the quotient isogeny is exactly `C`. With `quotientIsogeny` in hand this is
the statement that `φx` has a pole exactly at the roots of `h`, i.e. at `x(C ∖ {0})`. -/
theorem ker_quotientIsogeny [E.IsElliptic]
    (C : AddSubgroup (E⁄K).Point) [Finite C] {h : k[X]}
    (hh : IsKernelPolynomial K E C h) :
    (quotientIsogeny K E C hh).toHom.ker = C :=
  sorry

/-- **Main theorem (faithful form).** If `E/k` is elliptic and `C ⊆ E(K)` is a finite
Galois-stable subgroup, there is an elliptic curve `E'` over `k` and a `k`-isogeny `E → E'`
with kernel exactly `C`. Proved by three-line assembly from §§1–5: obtain `h` from
`exists_isKernelPolynomial`, take `E' := quotientCurve E h` (elliptic by
`isElliptic_quotientCurve`) and `φ := quotientIsogeny K E C hh`, and finish with
`ker_quotientIsogeny`. -/
theorem exists_quotientCurve_isogeny [E.IsElliptic]
    (C : AddSubgroup (E⁄K).Point) [Finite C] (hC : GaloisStable K E C) :
    ∃ (E' : WeierstrassCurve k) (_ : E'.IsElliptic) (φ : Isogeny K E E'),
      φ.toHom.ker = C := by
  obtain ⟨h, hh⟩ := exists_isKernelPolynomial K E C hC
  exact ⟨quotientCurve E h, isElliptic_quotientCurve K E C hh,
    quotientIsogeny K E C hh, ker_quotientIsogeny K E C hh⟩

end MainStatements

end WeierstrassCurve
