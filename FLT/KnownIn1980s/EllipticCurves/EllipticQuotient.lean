/-
Copyright (c) 2026 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Buzzard
-/
module

public import Mathlib.Algebra.BigOperators.Finprod
public import Mathlib.Algebra.Polynomial.Lifts
public import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
public import Mathlib.FieldTheory.Finite.Basic
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

## Where the remaining difficulty lives (the honest list — 5 leaves)
  1. `equation_quotientX_quotientY` — the computational heart of Vélu's theorem: the
     translate sums satisfy the Weierstrass equation of the quotient curve (smoothness is
     NOT part of this leaf; it is outsourced to leaf 2 via `equation_iff_nonsingular`).
     This identity also pins the correctness of the `velT`/`velW` formulas.
  2. `isElliptic_quotientCurve` — nonvanishing of the quotient discriminant.
  3. `quotientPointFun_add_of_notMem` — rigidity, narrowed to `P, R ∉ C` (the kernel
     cases are proved from the `C`-invariance `quotientX_add_mem`/`quotientY_add_mem`).
  4. `exists_isQuotientPhiData` — the quotient point map is, off the poles, induced by a
     triple of rational functions over `k` (`φx` with denominator `h²`, y-maps with `h³`;
     Kohel §2.4 has the explicit numerators). This one existence statement consolidates
     the former rational-map data leaves and the coherence leaf; the maps themselves are
     extracted from it by choice (`quotientPhiData`), and coherence
     (`quotientPointHom_some`) is a theorem.
  5. `finite_compl_range_quotientPointHom` — cofinitely many points of the quotient curve
     are hit (`K`-rationality of generic fibers of a separable isogeny over `kˢᵉᵖ`); full
     surjectivity is then a theorem via `AddSubgroup.eq_top_of_compl_finite`.

Everything else is **proved** below: §§0–2 in full — including `Affine.Point.infinite`
(an elliptic curve over a separably closed field has infinitely many points, via separable
quadratics/Artin–Schreier and `infinite_of_isSepClosed`) and the Galois-equivariance
theorem `Isogeny.map_galoisAction` (two homomorphisms agreeing off the finitely many
pole points agree, `AddMonoidHom.eq_of_setOf_ne_finite`) — and `velT`/`velW` are now
sorry-free definitions in every characteristic (power sums on the odd factor, halved
power sums on the 2-torsion factor in characteristic `≠ 2`, and the unique square root
`choiceSqrt` for the single possible 2-torsion point in characteristic `2`; specs
`velT_spec`/`velW_spec`, sanity `quotientCurve_one`). The kernel
(`ker_quotientPointHom`) and the assembly of the main theorem are proved from the leaves
above.

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

/-- Two homomorphisms out of an infinite additive group that agree away from a finite set
agree everywhere: any `a` can be written `(a - b) + b` with both `b` and `a - b` in the
(cofinite) agreement set. -/
theorem AddMonoidHom.eq_of_setOf_ne_finite {A B : Type*} [AddGroup A] [Infinite A]
    [AddZeroClass B] {ψ₁ ψ₂ : A →+ B} (h : {a : A | ψ₁ a ≠ ψ₂ a}.Finite) : ψ₁ = ψ₂ := by
  ext a
  have hinj : Function.Injective (a - · : A → A) := fun _ _ h' => sub_right_inj.mp h'
  obtain ⟨b, hb⟩ := (h.union <| h.preimage hinj.injOn).infinite_compl.nonempty
  simp only [Set.mem_compl_iff, Set.mem_union, Set.mem_preimage, Set.mem_setOf_eq, not_or,
    not_not] at hb
  rw [← sub_add_cancel a b, map_add, map_add, hb.1, hb.2]

/-- A subgroup with finite complement in an infinite group is everything: a nontrivial
coset would be an infinite subset of the finite complement. -/
theorem AddSubgroup.eq_top_of_compl_finite {G : Type*} [AddGroup G] [Infinite G]
    (H : AddSubgroup G) (hfin : ((H : Set G)ᶜ).Finite) : H = ⊤ := by
  rw [AddSubgroup.eq_top_iff']
  intro g
  by_contra hg
  have hH : (H : Set G).Infinite := by simpa using hfin.infinite_compl
  refine (hH.image (add_right_injective g).injOn).mono ?_ hfin
  rintro _ ⟨x, hx, rfl⟩ hmem
  exact hg (by simpa using H.sub_mem hmem hx)

namespace WeierstrassCurve

/-! ## §0 Preliminaries on points over an arbitrary field

Three ingredients for the equivariance theorem `Isogeny.map_galoisAction`: for a fixed
x-coordinate there are only finitely many points (the Weierstrass equation is a quadratic
in `y`), hence only finitely many points above any finite set of x-coordinates; and an
elliptic curve over a separably closed field has infinitely many points (the remaining
`sorry` leaf of this section). -/

section Preliminaries

variable {F : Type*} [Field F]

/-- For a fixed `x`, the `y`-coordinates satisfying the Weierstrass equation are the roots of
a monic quadratic, so there are only finitely many. -/
lemma Affine.finite_setOf_equation (W : Affine F) (x : F) :
    {y : F | W.Equation x y}.Finite := by
  refine (Polynomial.finite_setOf_isRoot (p := X ^ 2 + C (W.a₁ * x + W.a₃) * X
    - C (x ^ 3 + W.a₂ * x ^ 2 + W.a₄ * x + W.a₆)) fun hp => by
      have h2 := congrArg (coeff · 2) hp
      simp only [coeff_add, coeff_sub, coeff_C_mul, coeff_X_pow, coeff_C, coeff_X,
        coeff_zero] at h2
      norm_num at h2
    ).subset fun y hy => ?_
  simp only [Set.mem_setOf_eq, IsRoot, eval_sub, eval_add, eval_mul, eval_pow, eval_C, eval_X]
  linear_combination (W.equation_iff x y).mp hy

/-- The affine points of a Weierstrass curve lying above a finite set of x-coordinates form a
finite set. -/
lemma Affine.Point.finite_setOf_xCoord_mem {W : Affine F} {s : Set F} (hs : s.Finite) :
    {P : W.Point | ∃ (x y : F) (hxy : W.Nonsingular x y),
      P = Affine.Point.some x y hxy ∧ x ∈ s}.Finite := by
  classical
  have hbig : (⋃ x ∈ s, {x} ×ˢ {y : F | W.Equation x y}).Finite :=
    hs.biUnion fun x _ => (Set.finite_singleton x).prod (Affine.finite_setOf_equation W x)
  refine (hbig.image fun p => if h : W.Nonsingular p.1 p.2
    then Affine.Point.some p.1 p.2 h else 0).subset ?_
  rintro _ ⟨x, y, hxy, rfl, hxs⟩
  exact ⟨(x, y), Set.mem_biUnion hxs ⟨rfl, hxy.1⟩, dif_pos hxy⟩

/-- The x-coordinate of an affine point, with junk value `0` at the point at infinity. -/
def Affine.Point.xCoord {W : Affine F} : W.Point → F
  | .zero => 0
  | .some x _ _ => x

/-- The y-coordinate of an affine point, with junk value `0` at the point at infinity. -/
def Affine.Point.yCoord {W : Affine F} : W.Point → F
  | .zero => 0
  | .some _ y _ => y

lemma Affine.Point.xCoord_some {W : Affine F} {x y : F} (hxy : W.Nonsingular x y) :
    (Affine.Point.some x y hxy).xCoord = x := rfl

lemma Affine.Point.yCoord_some {W : Affine F} {x y : F} (hxy : W.Nonsingular x y) :
    (Affine.Point.some x y hxy).yCoord = y := rfl

/-- The 2-torsion polynomial commutes with `map`. -/
lemma map_twoTorsionPolynomial {F' : Type*} [Field F'] (W : WeierstrassCurve F)
    (f : F →+* F') :
    (W.map f).twoTorsionPolynomial = W.twoTorsionPolynomial.map f := by
  simp [twoTorsionPolynomial, Cubic.map, map_b₂, map_b₄, map_b₆, map_ofNat]

/-- On the curve, the 2-division polynomial evaluates to the square `(2y + a₁x + a₃)²` — in
particular it vanishes at `x` exactly when `(x, y)` is a 2-torsion point. -/
lemma twoTorsionPolynomial_toPoly_eval {W : WeierstrassCurve F} {x y : F}
    (hxy : W.toAffine.Equation x y) :
    W.twoTorsionPolynomial.toPoly.eval x = (2 * y + W.a₁ * x + W.a₃) ^ 2 := by
  simp only [twoTorsionPolynomial, Cubic.toPoly, eval_add, eval_mul, eval_pow, eval_C, eval_X,
    b₂, b₄, b₆]
  linear_combination -4 * (W.toAffine.equation_iff x y).mp hxy

/-- In characteristic `2` an elliptic curve has `a₁ ≠ 0` or `a₃ ≠ 0`: both zero would force
`b₂ = b₄ = b₆ = 0` and hence `Δ = 0`. -/
lemma a₁_ne_zero_or_a₃_ne_zero (W : WeierstrassCurve F) [W.IsElliptic]
    (h2 : (2 : F) = 0) : W.a₁ ≠ 0 ∨ W.a₃ ≠ 0 := by
  refine not_and_or.mp fun ⟨ha₁, ha₃⟩ => (W.isElliptic_iff.mp ‹W.IsElliptic›).ne_zero ?_
  have hb₂ : W.b₂ = 0 := by rw [b₂, ha₁]; linear_combination 2 * W.a₂ * h2
  have hb₄ : W.b₄ = 0 := by rw [b₄, ha₁]; linear_combination W.a₄ * h2
  have hb₆ : W.b₆ = 0 := by rw [b₆, ha₃]; linear_combination 2 * W.a₆ * h2
  rw [Δ, hb₂, hb₄, hb₆]
  ring

/-- For an elliptic curve the 2-division polynomial is nonzero: in characteristic `≠ 2` its
leading coefficient is `4`, and in characteristic `2` it is `a₁²X² + a₃²` with `a₁ = a₃ = 0`
excluded by `a₁_ne_zero_or_a₃_ne_zero`. -/
lemma twoTorsionPolynomial_toPoly_ne_zero (W : WeierstrassCurve F) [W.IsElliptic] :
    W.twoTorsionPolynomial.toPoly ≠ 0 := by
  rcases eq_or_ne (2 : F) 0 with h2 | h2
  · rcases a₁_ne_zero_or_a₃_ne_zero W h2 with ha | ha
    · refine Cubic.ne_zero_of_b_ne_zero fun hb => ha (sq_eq_zero_iff.mp ?_)
      have hb' : W.b₂ = 0 := hb
      rw [b₂] at hb'
      linear_combination hb' - 2 * W.a₂ * h2
    · refine Cubic.ne_zero_of_d_ne_zero fun hd => ha (sq_eq_zero_iff.mp ?_)
      have hd' : W.b₆ = 0 := hd
      rw [b₆] at hd'
      linear_combination hd' - 2 * W.a₆ * h2
  · refine Cubic.ne_zero_of_a_ne_zero fun h4 => h2 (mul_self_eq_zero.mp ?_)
    have h4' : (4 : F) = 0 := h4
    linear_combination h4'

/-- A separably closed field is infinite: over a finite field with `q` elements the
polynomial `X^(q+1) − 1` is separable, so it would have `q + 1` distinct roots. -/
theorem infinite_of_isSepClosed [IsSepClosed F] : Infinite F := by
  apply Infinite.of_not_fintype
  intro hfin
  set f : F[X] := X ^ (Fintype.card F + 1) - C 1 with hf
  have hsep : f.Separable :=
    separable_X_pow_sub_C 1 (by simp [Nat.cast_card_eq_zero]) one_ne_zero
  refine Nat.not_succ_le_self (Fintype.card F) ?_
  calc Fintype.card F + 1 = Fintype.card (f.rootSet F) := by
        rw [card_rootSet_eq_natDegree hsep (IsSepClosed.splits_domain f hsep),
          natDegree_X_pow_sub_C]
    _ ≤ Fintype.card F := Fintype.card_le_of_injective _ Subtype.coe_injective

/-- Over a separably closed field every monic quadratic `y² + by = c` with `2 ≠ 0` or
`b ≠ 0` has a root: complete the square in characteristic `≠ 2`, and use the separable
Artin–Schreier-type equation `y² + by − c = 0` in characteristic `2`. -/
lemma exists_quadratic_root [IsSepClosed F] (b c : F) (hbc : (2 : F) ≠ 0 ∨ b ≠ 0) :
    ∃ y : F, y ^ 2 + b * y = c := by
  rcases eq_or_ne (2 : F) 0 with h2 | h2
  · -- characteristic 2: `X² + bX − c` is separable since its derivative is `b ≠ 0`
    obtain ⟨y, hy⟩ := IsSepClosed.exists_root_C_mul_X_pow_add_C_mul_X_add_C 1 b (-c)
      (by exact_mod_cast h2) le_rfl (hbc.resolve_left fun h => h h2)
    exact ⟨y, by linear_combination hy⟩
  · -- characteristic ≠ 2: complete the square with a square root of `b² + 4c`
    haveI : NeZero ((2 : ℕ) : F) := ⟨by exact_mod_cast h2⟩
    obtain ⟨s, hs⟩ := IsSepClosed.exists_pow_nat_eq (b ^ 2 + 4 * c) 2
    exact ⟨(s - b) / 2, by field_simp; linear_combination hs⟩

/-- If `2 ≠ 0` or `a₁x + a₃ ≠ 0`, then `x` is the x-coordinate of a point of the curve: the
Weierstrass quadratic in `y` has a root by `exists_quadratic_root`, and every equation point
of an elliptic curve is nonsingular. -/
lemma Affine.exists_nonsingular [IsSepClosed F] (W : WeierstrassCurve F) [W.IsElliptic]
    {x : F} (hx : (2 : F) ≠ 0 ∨ W.a₁ * x + W.a₃ ≠ 0) :
    ∃ y : F, W.toAffine.Nonsingular x y := by
  obtain ⟨y, hy⟩ := exists_quadratic_root (W.a₁ * x + W.a₃)
    (x ^ 3 + W.a₂ * x ^ 2 + W.a₄ * x + W.a₆) hx
  exact ⟨y, W.toAffine.equation_iff_nonsingular.mp <| (W.toAffine.equation_iff x y).mpr <| by
    linear_combination hy⟩

/-- **An elliptic curve over a separably closed field has infinitely many points**: all but
finitely many `x` are x-coordinates of points (`Affine.exists_nonsingular`; the exceptions
are the roots of `a₁X + a₃` in characteristic `2`), and distinct `x`'s give distinct
points. -/
theorem Affine.Point.infinite [IsSepClosed F] (W : WeierstrassCurve F) [W.IsElliptic] :
    Infinite W.toAffine.Point := by
  haveI : Infinite F := infinite_of_isSepClosed
  -- all but finitely many `x` satisfy the solvability hypothesis of `exists_nonsingular`
  have hgood : {x : F | (2 : F) ≠ 0 ∨ W.a₁ * x + W.a₃ ≠ 0}.Infinite := by
    rcases eq_or_ne (2 : F) 0 with h2 | h2
    · have hfin : {x : F | W.a₁ * x + W.a₃ = 0}.Finite := by
        rcases eq_or_ne W.a₁ 0 with h1 | h1
        · have h3 := (a₁_ne_zero_or_a₃_ne_zero W h2).resolve_left (not_not_intro h1)
          simp [h1, h3]
        · refine Set.Subsingleton.finite fun x hx y hy => mul_left_cancel₀ h1 ?_
          simp only [Set.mem_setOf_eq] at hx hy
          linear_combination hx - hy
      simpa [h2, Set.compl_setOf] using hfin.infinite_compl
    · simpa [h2] using Set.infinite_univ (α := F)
  choose y hy using fun x : {x : F | (2 : F) ≠ 0 ∨ W.a₁ * x + W.a₃ ≠ 0} =>
    Affine.exists_nonsingular W x.2
  haveI := hgood.to_subtype
  refine Infinite.of_injective (fun x => Affine.Point.some x.1 (y x) (hy x))
    fun x₁ x₂ h => ?_
  simp only [Affine.Point.some.injEq] at h
  exact Subtype.ext h.1

end Preliminaries

variable {k : Type*} [Field k] (K : Type*) [Field K] [Algebra k K] [IsSepClosure k K]
  [DecidableEq K]

omit [IsSepClosure k K] [DecidableEq K] in
/-- A `k`-algebra automorphism of `K` commutes with evaluation (via `eval₂`) of a polynomial
with coefficients in `k`. -/
lemma algEquiv_eval₂_algebraMap (p : k[X]) (σ : K ≃ₐ[k] K) (x : K) :
    σ (p.eval₂ (algebraMap k K) x) = p.eval₂ (algebraMap k K) (σ x) := by
  simpa only [aeval_def] using (aeval_algHom_apply σ x p).symm

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
  refine ((Set.toFinite (C : Set (E⁄K).Point)).image Affine.Point.xCoord).subset ?_
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
  -- the degree of the kernel polynomial is the number of distinct x-coordinates
  have hdeg : (kernelPolynomial K E C).natDegree = (finite_xCoordSet K E C).toFinset.card := by
    rw [kernelPolynomial, Polynomial.natDegree_prod _ _ fun x _ => X_sub_C_ne_zero x]
    simp
  -- `xCoord` maps the nonzero points of `C` into the x-coordinate set
  have Hmaps : ∀ P ∈ hdiff.toFinset,
      Affine.Point.xCoord P ∈ (finite_xCoordSet K E C).toFinset := by
    rintro (_ | ⟨x', y', hxy'⟩) hP <;> rw [Set.Finite.mem_toFinset] at hP ⊢
    · exact absurd rfl hP.2
    · exact ⟨y', hxy', hP.1⟩
  -- ... with every fiber being a pair `{Q, -Q}` of size exactly two (no 2-torsion)
  have fib : ∀ x ∈ (finite_xCoordSet K E C).toFinset,
      (hdiff.toFinset.filter fun P => Affine.Point.xCoord P = x).card = 2 := by
    intro x hx
    rw [Set.Finite.mem_toFinset] at hx
    obtain ⟨y, hxy, hmem⟩ := hx
    have hQ0 : Affine.Point.some x y hxy ≠ (0 : (E⁄K).Point) :=
      Affine.Point.some_ne_zero hxy
    have hne : Affine.Point.some x y hxy ≠ -Affine.Point.some x y hxy :=
      fun hcon => hQ0 (h2 _ hmem (add_eq_zero_iff_eq_neg.mpr hcon))
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
      · exact ⟨⟨neg_mem hmem, fun h0 => hQ0 (neg_eq_zero.mp h0)⟩,
          by simp [Affine.Point.xCoord_some]⟩
  -- fiberwise count of the nonzero points, then add the point at infinity back in
  calc Nat.card C = (C : Set (E⁄K).Point).ncard := rfl
    _ = ((C : Set (E⁄K).Point) \ {0}).ncard + 1 :=
        (Set.ncard_sdiff_singleton_add_one C.zero_mem hCfin).symm
    _ = hdiff.toFinset.card + 1 := by rw [Set.ncard_eq_toFinset_card _ hdiff]
    _ = 2 * (kernelPolynomial K E C).natDegree + 1 := by
        rw [Finset.card_eq_sum_card_fiberwise Hmaps, Finset.sum_congr rfl fib,
          Finset.sum_const, smul_eq_mul, mul_comm, hdeg]

omit [IsSepClosure k K] in
/-- **Key lemma (all of equivariance in one line).** The Galois action permutes the nonzero
points of a stable `C`, hence permutes their x-coordinates, hence fixes `h`. -/
lemma kernelPolynomial_map_galois (C : AddSubgroup (E⁄K).Point) [Finite C]
    (hC : GaloisStable K E C) (σ : K ≃ₐ[k] K) :
    (kernelPolynomial K E C).map (σ : K →+* K) = kernelPolynomial K E C := by
  -- the Galois action maps the (finite) x-coordinate set into itself, hence permutes it
  have himg : (finite_xCoordSet K E C).toFinset.image σ = (finite_xCoordSet K E C).toFinset := by
    refine Finset.eq_of_subset_of_card_le ?_ (Finset.card_image_of_injective _ σ.injective).ge
    intro x hx
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hx
    rw [Set.Finite.mem_toFinset] at hy ⊢
    obtain ⟨z, hz, hmem⟩ := hy
    have h2 := hC σ _ hmem
    rw [Affine.Point.map_some] at h2
    exact ⟨σ z, _, h2⟩
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

open Classical in
/-- The 2-torsion factor of a kernel polynomial: the monic-normalized gcd of `h` with the
2-division polynomial `ψ₂² = 4X³ + b₂X² + 2b₄X + b₆`. Its roots are the kernel
x-coordinates of 2-torsion points; for a two-torsion-free kernel of an elliptic curve it is
`1` (`IsKernelPolynomial.twoTorsionFactor_eq_one`). -/
noncomputable def twoTorsionFactor (E : WeierstrassCurve k) (h : k[X]) : k[X] :=
  EuclideanDomain.gcd h E.twoTorsionPolynomial.toPoly
    * Polynomial.C (EuclideanDomain.gcd h E.twoTorsionPolynomial.toPoly).leadingCoeff⁻¹

/-- The odd (paired, non-2-torsion) part of a kernel polynomial. -/
noncomputable def oddFactor (E : WeierstrassCurve k) (h : k[X]) : k[X] :=
  h /ₘ twoTorsionFactor E h

/-- Vélu's `t` for the paired part of the kernel — the power-sum expression
`6(s₁² − 2s₂) + b₂s₁ + n·b₄` in the coefficients of `h` (REAL definition; this is the whole
of `velT` when the kernel is two-torsion-free). -/
noncomputable def velTOdd (E : WeierstrassCurve k) (h : k[X]) : k :=
  6 * (velS₁ h ^ 2 - 2 * velS₂ h) + E.b₂ * velS₁ h + h.natDegree * E.b₄

/-- Vélu's `w` for the paired part of the kernel (REAL definition). -/
noncomputable def velWOdd (E : WeierstrassCurve k) (h : k[X]) : k :=
  10 * (velS₁ h ^ 3 - 3 * velS₁ h * velS₂ h + 3 * velS₃ h)
    + 2 * E.b₂ * (velS₁ h ^ 2 - 2 * velS₂ h) + 3 * E.b₄ * velS₁ h + h.natDegree * E.b₆

open Classical in
/-- A square root of `a`, chosen by choice if one exists; junk value `0` otherwise. It is
used only in characteristic `2`, where square roots are unique (Frobenius is injective),
so no arbitrariness actually arises there. -/
noncomputable def choiceSqrt (a : k) : k :=
  if H : ∃ s : k, s ^ 2 = a then H.choose else 0

lemma choiceSqrt_sq {a : k} (H : ∃ s : k, s ^ 2 = a) : choiceSqrt a ^ 2 = a := by
  rw [choiceSqrt, dif_pos H]
  exact H.choose_spec

open Classical in
/-- Kohel's 2-torsion correction to Vélu's `t`, as a function of the 2-torsion factor `g`:
the sum of `gˣ_Q = 3x₀² + 2a₂x₀ + a₄ − a₁y₀` over the roots `x₀` of `g` (Kohel's thesis
§2.4). REAL definition, in two branches:

* characteristic `≠ 2`: the 2-torsion point above `x₀` has `y₀ = −(a₁x₀ + a₃)/2`, giving
  `gˣ_Q = (6x₀² + b₂x₀ + b₄)/2` — half the paired contribution — so the correction is the
  power-sum expression `(6(s₁² − 2s₂) + b₂s₁ + m·b₄)/2` in the coefficients of `g`;
* characteristic `2`: a genuine 2-torsion factor has degree `≤ 1`, because `E[2](kˢᵉᵖ)`
  has order `≤ 2` there (the 2-torsion condition degenerates to `a₁x + a₃ = 0`, giving at
  most one `x₀`, with a unique `y₀` above it). For `g = X − x₀` (so `x₀ = −g.coeff 0`) the
  correction is `gˣ_Q = x₀² + a₄ + a₁y₀`, where `y₀² = x₀³ + a₂x₀² + a₄x₀ + a₆` (the
  Weierstrass equation at `a₁x₀ + a₃ = 0`), so `a₁y₀` is THE square root of
  `a₁²(x₀³ + a₂x₀² + a₄x₀ + a₆)`, taken with `choiceSqrt` (unique in characteristic `2`;
  it lies in `k` because the 2-torsion point above `x₀` is unique, hence Galois-fixed).
  Degrees `≥ 2` cannot arise from Galois-stable kernels in characteristic `2` and get the
  junk value `0`.

Guarded to vanish on the trivial factor, so the two-torsion-free case is exact by
definition (`velTEven_one`). -/
noncomputable def velTEven (E : WeierstrassCurve k) (g : k[X]) : k :=
  if g = 1 then 0
  else if (2 : k) = 0 then
    if g.natDegree = 1 then
      g.coeff 0 ^ 2 + E.a₄
        + choiceSqrt (E.a₁ ^ 2 * (-(g.coeff 0 ^ 3) + E.a₂ * g.coeff 0 ^ 2
            - E.a₄ * g.coeff 0 + E.a₆))
    else 0
  else (6 * (velS₁ g ^ 2 - 2 * velS₂ g) + E.b₂ * velS₁ g + g.natDegree * E.b₄) / 2

open Classical in
/-- Kohel's 2-torsion correction to Vélu's `w`: since `gʸ_Q = 0` for 2-torsion points, the
per-root contribution is `x₀·gˣ_Q`. REAL definition: in characteristic `≠ 2` the power-sum
expression `(6p₃ + b₂p₂ + b₄p₁)/2`, and in characteristic `2` it is `x₀ = −g.coeff 0`
times the `velTEven` contribution, with the same `choiceSqrt` and the same degree bound as
there. -/
noncomputable def velWEven (E : WeierstrassCurve k) (g : k[X]) : k :=
  if g = 1 then 0
  else if (2 : k) = 0 then
    if g.natDegree = 1 then
      -(g.coeff 0) * (g.coeff 0 ^ 2 + E.a₄
        + choiceSqrt (E.a₁ ^ 2 * (-(g.coeff 0 ^ 3) + E.a₂ * g.coeff 0 ^ 2
            - E.a₄ * g.coeff 0 + E.a₆)))
    else 0
  else (6 * (velS₁ g ^ 3 - 3 * velS₁ g * velS₂ g + 3 * velS₃ g)
    + E.b₂ * (velS₁ g ^ 2 - 2 * velS₂ g) + E.b₄ * velS₁ g) / 2

lemma velTEven_one (E : WeierstrassCurve k) : velTEven E 1 = 0 := if_pos rfl

lemma velWEven_one (E : WeierstrassCurve k) : velWEven E 1 = 0 := if_pos rfl

/-- Vélu's `t`, decomposed into the paired part (a real formula in the coefficients of the
odd factor) plus Kohel's 2-torsion correction (the sorried leaf `velTEven`). -/
noncomputable def velT (E : WeierstrassCurve k) (h : k[X]) : k :=
  velTOdd E (oddFactor E h) + velTEven E (twoTorsionFactor E h)

/-- Vélu's `w`, decomposed like `velT`. -/
noncomputable def velW (E : WeierstrassCurve k) (h : k[X]) : k :=
  velWOdd E (oddFactor E h) + velWEven E (twoTorsionFactor E h)

/-- **The quotient curve `E/C`, explicitly.** Vélu/Kohel: `a₁, a₂, a₃` unchanged,
`a₄' = a₄ − 5t`, `a₆' = a₆ − b₂t − 7w`. Uniform in all cases once `t, w` are correct. -/
noncomputable def quotientCurve (E : WeierstrassCurve k) (h : k[X]) : WeierstrassCurve k where
  a₁ := E.a₁
  a₂ := E.a₂
  a₃ := E.a₃
  a₄ := E.a₄ - 5 * velT E h
  a₆ := E.a₆ - E.b₂ * velT E h - 7 * velW E h

lemma twoTorsionFactor_one (E : WeierstrassCurve k) : twoTorsionFactor E 1 = 1 := by
  classical
  simp [twoTorsionFactor, EuclideanDomain.gcd_one_left]

lemma velT_one (E : WeierstrassCurve k) : velT E (1 : k[X]) = 0 := by
  simp [velT, velTOdd, oddFactor, Polynomial.divByMonic_one, velS₁,
    velS₂, velTEven_one, twoTorsionFactor_one]

lemma velW_one (E : WeierstrassCurve k) : velW E (1 : k[X]) = 0 := by
  simp [velW, velWOdd, oddFactor, Polynomial.divByMonic_one, velS₁,
    velS₂, velS₃, velWEven_one, twoTorsionFactor_one]

/-- Sanity check for the decomposed definitions: the quotient of `E` by the trivial kernel
polynomial is `E` itself. -/
theorem quotientCurve_one (E : WeierstrassCurve k) : quotientCurve E 1 = E := by
  ext <;> simp [quotientCurve, velT_one, velW_one]

section MainStatements

variable (E : WeierstrassCurve k)

omit [IsSepClosure k K] in
/-- A two-torsion-free kernel has kernel polynomial coprime to the 2-division polynomial:
its 2-torsion factor is trivial. The point: on the curve `ψ₂²(x) = (2y + a₁x + a₃)²`
(`twoTorsionPolynomial_toPoly_eval`), which vanishes iff `(x, y) = -(x, y)`; so a common
root of `h` and `ψ₂²` in `K` would be the x-coordinate of a nontrivial 2-torsion point
of `C`. -/
lemma IsKernelPolynomial.twoTorsionFactor_eq_one [E.IsElliptic]
    {C : AddSubgroup (E⁄K).Point} [Finite C] {h : k[X]} (hh : IsKernelPolynomial K E C h)
    (h2 : ∀ P ∈ C, P + P = 0 → P = 0) :
    twoTorsionFactor E h = 1 := by
  classical
  have hψ : E.twoTorsionPolynomial.toPoly ≠ 0 := twoTorsionPolynomial_toPoly_ne_zero E
  -- it suffices that the (un-normalized) gcd is a unit, i.e. a nonzero constant
  suffices hu : IsUnit (EuclideanDomain.gcd h E.twoTorsionPolynomial.toPoly) by
    obtain ⟨c, hc, hC⟩ := Polynomial.isUnit_iff.mp hu
    rw [twoTorsionFactor, ← hC, Polynomial.leadingCoeff_C, ← Polynomial.C_mul,
      mul_inv_cancel₀ hc.ne_zero, Polynomial.C_1]
  by_contra hunit
  set d := EuclideanDomain.gcd h E.twoTorsionPolynomial.toPoly with hd
  -- a nonunit divisor of the (split, nonzero) kernel polynomial has a root `x₀` in `K` ...
  have hdmap : d.map (algebraMap k K) ∣ kernelPolynomial K E C := by
    rw [← hh.2]
    exact Polynomial.map_dvd _ (EuclideanDomain.gcd_dvd_left h E.twoTorsionPolynomial.toPoly)
  have hkps : (kernelPolynomial K E C).Splits := by
    rw [kernelPolynomial]
    exact Polynomial.Splits.prod fun x _ => Polynomial.Splits.X_sub_C x
  have hdeg : (d.map (algebraMap k K)).degree ≠ 0 := by
    rw [Polynomial.degree_map]
    exact fun h0 => hunit (Polynomial.isUnit_iff_degree_eq_zero.mpr h0)
  obtain ⟨x₀, hx₀⟩ := ((hkps.of_dvd (kernelPolynomial_monic K E C).ne_zero
    hdmap).exists_eval_eq_zero hdeg)
  -- ... which is the x-coordinate of a kernel point `Q = (x₀, y)` ...
  have hxkp : (kernelPolynomial K E C).eval x₀ = 0 :=
    Polynomial.eval_eq_zero_of_dvd_of_eval_eq_zero hdmap hx₀
  rw [kernelPolynomial, Polynomial.eval_prod] at hxkp
  obtain ⟨x₁, hx₁, hx₁eq⟩ := Finset.prod_eq_zero_iff.mp hxkp
  rw [Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C, sub_eq_zero] at hx₁eq
  subst hx₁eq
  rw [Set.Finite.mem_toFinset] at hx₁
  obtain ⟨y, hxy, hmem⟩ := hx₁
  -- ... and also a root of the 2-division polynomial of `E⁄K`
  have hdψ : d.map (algebraMap k K) ∣ (E⁄K).twoTorsionPolynomial.toPoly := by
    change d.map (algebraMap k K) ∣ (E.map (algebraMap k K)).twoTorsionPolynomial.toPoly
    rw [map_twoTorsionPolynomial E (algebraMap k K), Cubic.map_toPoly]
    exact Polynomial.map_dvd _ (EuclideanDomain.gcd_dvd_right h E.twoTorsionPolynomial.toPoly)
  have hψx : ((E⁄K).twoTorsionPolynomial.toPoly).eval x₀ = 0 :=
    Polynomial.eval_eq_zero_of_dvd_of_eval_eq_zero hdψ hx₀
  -- so `Q` is a nontrivial 2-torsion point of `C`, contradiction
  have hy0 : y = (E⁄K).negY x₀ y := by
    have hsq := sq_eq_zero_iff.mp (twoTorsionPolynomial_toPoly_eval hxy.1 ▸ hψx)
    have hnegY : (E⁄K).negY x₀ y = -y - (E⁄K).a₁ * x₀ - (E⁄K).a₃ := rfl
    rw [hnegY]
    linear_combination hsq
  refine Affine.Point.some_ne_zero hxy (h2 _ hmem (add_eq_zero_iff_eq_neg.mpr ?_))
  rw [Affine.Point.neg_some]
  simp only [Affine.Point.some.injEq]
  exact ⟨trivial, hy0⟩

omit [IsSepClosure k K] in
/-- Spec for `velT` in the two-torsion-free case — now a theorem: the 2-torsion factor is
trivial, so `velT` is definitionally the power-sum formula on all of `h`. -/
lemma velT_spec [E.IsElliptic] (C : AddSubgroup (E⁄K).Point) [Finite C] {h : k[X]}
    (hh : IsKernelPolynomial K E C h) (h2 : ∀ P ∈ C, P + P = 0 → P = 0) :
    velT E h = 6 * (velS₁ h ^ 2 - 2 * velS₂ h) + E.b₂ * velS₁ h + h.natDegree * E.b₄ := by
  have hg := IsKernelPolynomial.twoTorsionFactor_eq_one K E hh h2
  simp only [velT, velTOdd, oddFactor, hg, Polynomial.divByMonic_one, velTEven_one, add_zero]

omit [IsSepClosure k K] in
/-- Spec for `velW` in the two-torsion-free case — now a theorem, like `velT_spec`. -/
lemma velW_spec [E.IsElliptic] (C : AddSubgroup (E⁄K).Point) [Finite C] {h : k[X]}
    (hh : IsKernelPolynomial K E C h) (h2 : ∀ P ∈ C, P + P = 0 → P = 0) :
    velW E h = 10 * (velS₁ h ^ 3 - 3 * velS₁ h * velS₂ h + 3 * velS₃ h)
      + 2 * E.b₂ * (velS₁ h ^ 2 - 2 * velS₂ h) + 3 * E.b₄ * velS₁ h
      + h.natDegree * E.b₆ := by
  have hg := IsKernelPolynomial.twoTorsionFactor_eq_one K E hh h2
  simp only [velW, velWOdd, oddFactor, hg, Polynomial.divByMonic_one, velWEven_one, add_zero]

omit [IsSepClosure k K] in
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
`toHom ∘ σ` and `σ ∘ toHom` agree wherever the coherence clause bites, i.e. away from the
finitely many points over the roots of `φx.denom` (`Affine.Point.finite_setOf_xCoord_mem`);
two homomorphisms on `E(K)` agreeing off a finite set agree everywhere
(`AddMonoidHom.eq_of_setOf_ne_finite`) since `E(K)` is infinite (`Affine.Point.infinite`,
the remaining leaf). -/
theorem map_galoisAction [E.IsElliptic] (φ : Isogeny K E E') (σ : K ≃ₐ[k] K)
    (P : (E⁄K).Point) :
    φ.toHom (Affine.Point.map σ.toAlgHom P)
      = Affine.Point.map σ.toAlgHom (φ.toHom P) := by
  haveI : IsSepClosed K := IsSepClosure.sep_closed k
  haveI : (E⁄K).IsElliptic := inferInstanceAs ((E.map (algebraMap k K)).IsElliptic)
  haveI : Infinite (E⁄K).Point := Affine.Point.infinite (E⁄K)
  -- the poles of `φx` in `K` form a finite set
  have hpoles : {x : K | φ.φx.denom.eval₂ (algebraMap k K) x = 0}.Finite := by
    simpa only [IsRoot.def, eval_map] using Polynomial.finite_setOf_isRoot
      ((Polynomial.map_ne_zero_iff (algebraMap k K).injective).mpr (RatFunc.denom_ne_zero φ.φx))
  -- away from the poles the two compositions agree, by the coherence clause on both sides
  have key : ∀ Q : (E⁄K).Point,
      φ.toHom (Affine.Point.map σ.toAlgHom Q) ≠ Affine.Point.map σ.toAlgHom (φ.toHom Q) →
      ∃ (x y : K) (hxy : (E⁄K).Nonsingular x y), Q = Affine.Point.some x y hxy ∧
        x ∈ {x : K | φ.φx.denom.eval₂ (algebraMap k K) x = 0} := by
    intro Q hQ
    cases Q with
    | zero =>
      refine absurd ?_ hQ
      change φ.toHom (Affine.Point.map σ.toAlgHom 0) = Affine.Point.map σ.toAlgHom (φ.toHom 0)
      rw [_root_.map_zero, _root_.map_zero, _root_.map_zero]
    | some x y hxy =>
      refine ⟨x, y, hxy, rfl, ?_⟩
      by_contra hden
      simp only [Set.mem_setOf_eq] at hden
      apply hQ
      -- the denominator does not vanish at `σ x` either, since it has coefficients in `k`
      have hdenσ : φ.φx.denom.eval₂ (algebraMap k K) (σ x) ≠ 0 := by
        rw [← algEquiv_eval₂_algebraMap]
        exact fun hc => hden (σ.injective (hc.trans (_root_.map_zero σ).symm))
      have hcoe : ∀ a : K, σ.toAlgHom a = σ a := fun _ => rfl
      obtain ⟨h₁, e₁⟩ := φ.toHom_some x y hxy hden
      obtain ⟨h₂, e₂⟩ := φ.toHom_some (σ x) (σ y)
        ((E.toAffine.baseChange_nonsingular σ.toAlgHom.injective ..).mpr hxy) hdenσ
      rw [e₁, Affine.Point.map_some, Affine.Point.map_some]
      refine e₂.trans ?_
      simp only [hcoe, map_add, map_mul, map_div₀, algEquiv_eval₂_algebraMap]
  -- conclude: the two compositions are equal as homomorphisms
  have heq : φ.toHom.comp (Affine.Point.map σ.toAlgHom)
      = (Affine.Point.map σ.toAlgHom).comp φ.toHom := by
    refine AddMonoidHom.eq_of_setOf_ne_finite ?_
    refine (Affine.Point.finite_setOf_xCoord_mem hpoles).subset ?_
    intro Q hQ
    simp only [Set.mem_setOf_eq, AddMonoidHom.coe_comp, Function.comp_apply] at hQ
    exact key Q hQ
  exact DFunLike.congr_fun heq P

/-- Kernels of `k`-isogenies are Galois-stable (immediate from equivariance). -/
theorem ker_galoisStable [E.IsElliptic] (φ : Isogeny K E E') :
    GaloisStable K E φ.toHom.ker := fun σ P hP => by
  rw [AddMonoidHom.mem_ker, map_galoisAction K φ σ P, AddMonoidHom.mem_ker.mp hP,
    _root_.map_zero]

end Isogeny

/-! ## §5 The quotient isogeny and the main theorem -/

/-- The x-coordinate of Vélu's isogeny, as a function on points of `E` over `K`:
`X(P) = x(P) + Σ_{Q ∈ C∖{0}} (x(P+Q) − x(Q))`, computed with the group law of `E`. The
rational expression `quotientPhiX` is its closed form. Junk when `P ∈ C`. -/
noncomputable def quotientX (C : AddSubgroup (E⁄K).Point) (P : (E⁄K).Point) : K :=
  P.xCoord + ∑ᶠ Q ∈ (C : Set (E⁄K).Point) \ {0}, ((P + Q).xCoord - Q.xCoord)

/-- The y-coordinate of Vélu's isogeny, as a function on points of `E` over `K`:
`Y(P) = y(P) + Σ_{Q ∈ C∖{0}} (y(P+Q) − y(Q))`. Junk when `P ∈ C`. -/
noncomputable def quotientY (C : AddSubgroup (E⁄K).Point) (P : (E⁄K).Point) : K :=
  P.yCoord + ∑ᶠ Q ∈ (C : Set (E⁄K).Point) \ {0}, ((P + Q).yCoord - Q.yCoord)

omit [IsSepClosure k K] in
/-- Translate-sum invariance: for any coordinate function `g` and `Q₀ ∈ C`, the Vélu-style
sum `g(P) + Σ_{Q ∈ C∖0} (g(P+Q) − g(Q))` is unchanged by `P ↦ P + Q₀`: both sides equal
`Σ_{Q ∈ C} g(P+Q) − Σ_{Q ∈ C∖0} g(Q)`. This is the first step of the additivity leaf and
the well-definedness of the induced map on `E(K)/C`. -/
theorem translate_finsum_add_mem (C : AddSubgroup (E⁄K).Point) [Finite C]
    (g : (E⁄K).Point → K) (P : (E⁄K).Point) {Q₀ : (E⁄K).Point} (hQ₀ : Q₀ ∈ C) :
    g (P + Q₀) + ∑ᶠ Q ∈ (C : Set (E⁄K).Point) \ {0}, (g (P + Q₀ + Q) - g Q)
      = g P + ∑ᶠ Q ∈ (C : Set (E⁄K).Point) \ {0}, (g (P + Q) - g Q) := by
  classical
  rcases eq_or_ne Q₀ 0 with rfl | hQ₀0
  · simp only [add_zero]
  have hCfin : (C : Set (E⁄K).Point).Finite := Set.toFinite _
  have hdfin : ((C : Set (E⁄K).Point) \ {0}).Finite := hCfin.sdiff
  have hcoe : ∀ f : (E⁄K).Point → K,
      (∑ᶠ Q ∈ (C : Set (E⁄K).Point) \ {0}, f Q) = ∑ Q ∈ hdfin.toFinset, f Q := fun f => by
    rw [← finsum_mem_coe_finset, Set.Finite.coe_toFinset]
  -- the difference-set is the full finset with `0` erased
  have herase0 : hdfin.toFinset = hCfin.toFinset.erase 0 := by
    ext Q
    simp only [Set.Finite.mem_toFinset, Set.mem_sdiff, Set.mem_singleton_iff,
      Finset.mem_erase, and_comm]
  -- translation by `Q₀` permutes `C`, matching `C ∖ {0}` with `C ∖ {Q₀}`
  have himgFull : hCfin.toFinset.image (fun Q => Q₀ + Q) = hCfin.toFinset := by
    refine Finset.eq_of_subset_of_card_le ?_
      (Finset.card_image_of_injective _ (add_right_injective Q₀)).ge
    intro R hR
    obtain ⟨Q, hQ, rfl⟩ := Finset.mem_image.mp hR
    rw [Set.Finite.mem_toFinset] at hQ ⊢
    exact C.add_mem hQ₀ hQ
  have himg : (hCfin.toFinset.erase 0).image (fun Q => Q₀ + Q) = hCfin.toFinset.erase Q₀ := by
    rw [Finset.image_erase (add_right_injective Q₀), himgFull]
    simp
  rw [hcoe, hcoe, Finset.sum_sub_distrib, Finset.sum_sub_distrib, herase0]
  have hre : ∑ Q ∈ hCfin.toFinset.erase 0, g (P + Q₀ + Q)
      = ∑ R ∈ hCfin.toFinset.erase Q₀, g (P + R) := by
    rw [← himg, Finset.sum_image fun x _ y _ hxy => add_right_injective Q₀ hxy]
    exact Finset.sum_congr rfl fun Q _ => by rw [add_assoc]
  rw [hre]
  -- with `Q₀` (resp. `0`) reinserted, both translated sums are `Σ_{Q ∈ C} g (P + Q)`
  have hQ₀mem : Q₀ ∈ hCfin.toFinset := (Set.Finite.mem_toFinset _).mpr hQ₀
  have h0mem : (0 : (E⁄K).Point) ∈ hCfin.toFinset := (Set.Finite.mem_toFinset _).mpr C.zero_mem
  have hfull : g (P + Q₀) + ∑ R ∈ hCfin.toFinset.erase Q₀, g (P + R)
      = g P + ∑ Q ∈ hCfin.toFinset.erase 0, g (P + Q) := by
    calc g (P + Q₀) + ∑ R ∈ hCfin.toFinset.erase Q₀, g (P + R)
        = ∑ R ∈ hCfin.toFinset, g (P + R) :=
          Finset.add_sum_erase _ (fun R => g (P + R)) hQ₀mem
      _ = g (P + 0) + ∑ Q ∈ hCfin.toFinset.erase 0, g (P + Q) :=
          (Finset.add_sum_erase _ (fun R => g (P + R)) h0mem).symm
      _ = g P + ∑ Q ∈ hCfin.toFinset.erase 0, g (P + Q) := by rw [add_zero]
  linear_combination hfull

omit [IsSepClosure k K] in
/-- `C`-invariance of Vélu's x-coordinate function (instance of
`translate_finsum_add_mem`). -/
theorem quotientX_add_mem (C : AddSubgroup (E⁄K).Point) [Finite C] (P : (E⁄K).Point)
    {Q₀ : (E⁄K).Point} (hQ₀ : Q₀ ∈ C) :
    quotientX K E C (P + Q₀) = quotientX K E C P := by
  simpa only [quotientX] using
    translate_finsum_add_mem K E C (fun R => R.xCoord) P hQ₀

omit [IsSepClosure k K] in
/-- `C`-invariance of Vélu's y-coordinate function. -/
theorem quotientY_add_mem (C : AddSubgroup (E⁄K).Point) [Finite C] (P : (E⁄K).Point)
    {Q₀ : (E⁄K).Point} (hQ₀ : Q₀ ∈ C) :
    quotientY K E C (P + Q₀) = quotientY K E C P := by
  simpa only [quotientY] using
    translate_finsum_add_mem K E C (fun R => R.yCoord) P hQ₀

omit [IsSepClosure k K] in
/-- Equation leaf (the computational heart of Vélu's theorem, now separated from
smoothness): for `P ∉ C` the translate sums `(X(P), Y(P))` satisfy the Weierstrass
equation of the quotient curve. This polynomial identity also carries the correctness of
the `velTEven`/`velWEven` correction branches, since the quotient curve is built from
`velT`/`velW`. -/
theorem equation_quotientX_quotientY [E.IsElliptic]
    (C : AddSubgroup (E⁄K).Point) [Finite C] {h : k[X]}
    (hh : IsKernelPolynomial K E C h) {P : (E⁄K).Point} (hP : P ∉ C) :
    ((quotientCurve E h)⁄K).Equation (quotientX K E C P) (quotientY K E C P) :=
  sorry

omit [IsSepClosure k K] in
/-- For `P ∉ C` the translate sums land at a nonsingular point — now a consequence of the
equation leaf: the quotient curve is elliptic (`isElliptic_quotientCurve`), and every
equation point on an elliptic curve is nonsingular. -/
theorem nonsingular_quotientX_quotientY [E.IsElliptic]
    (C : AddSubgroup (E⁄K).Point) [Finite C] {h : k[X]}
    (hh : IsKernelPolynomial K E C h) {P : (E⁄K).Point} (hP : P ∉ C) :
    ((quotientCurve E h)⁄K).Nonsingular (quotientX K E C P) (quotientY K E C P) := by
  haveI : (quotientCurve E h).IsElliptic := isElliptic_quotientCurve K E C hh
  haveI : ((quotientCurve E h)⁄K).IsElliptic :=
    inferInstanceAs (((quotientCurve E h).map (algebraMap k K)).IsElliptic)
  exact Affine.equation_iff_nonsingular.mp (equation_quotientX_quotientY K E C hh hP)

open Classical in
/-- The underlying function of the quotient point map: `C ↦ 0`, and `P ↦ (X(P), Y(P))` for
`P ∉ C`. REAL definition (given the nonsingularity leaf). -/
noncomputable def quotientPointFun [E.IsElliptic]
    (C : AddSubgroup (E⁄K).Point) [Finite C] {h : k[X]}
    (hh : IsKernelPolynomial K E C h) (P : (E⁄K).Point) :
    ((quotientCurve E h)⁄K).Point :=
  if hP : P ∈ C then 0
  else Affine.Point.some _ _ (nonsingular_quotientX_quotientY K E C hh hP)

omit [IsSepClosure k K] in
theorem quotientPointFun_apply_of_mem [E.IsElliptic]
    (C : AddSubgroup (E⁄K).Point) [Finite C] {h : k[X]}
    (hh : IsKernelPolynomial K E C h) {P : (E⁄K).Point} (hP : P ∈ C) :
    quotientPointFun K E C hh P = 0 :=
  dif_pos hP

omit [IsSepClosure k K] in
theorem quotientPointFun_apply_of_notMem [E.IsElliptic]
    (C : AddSubgroup (E⁄K).Point) [Finite C] {h : k[X]}
    (hh : IsKernelPolynomial K E C h) {P : (E⁄K).Point} (hP : P ∉ C) :
    quotientPointFun K E C hh P
      = Affine.Point.some _ _ (nonsingular_quotientX_quotientY K E C hh hP) :=
  dif_neg hP

omit [IsSepClosure k K] in
/-- Additivity leaf (the deepest: rigidity), narrowed to the essential case `P, R ∉ C`
(which includes the subcase `P + R ∈ C`, i.e. `φ(R) = -φ(P)`). On paper: `(X, Y)` are
`C`-invariant functions on `E` (proved: `quotientX_add_mem`, `quotientY_add_mem`), so
`quotientPointFun` descends to a morphism of curves `E/C → E'` sending `0` to `0`, hence
is a group homomorphism. -/
theorem quotientPointFun_add_of_notMem [E.IsElliptic]
    (C : AddSubgroup (E⁄K).Point) [Finite C] {h : k[X]}
    (hh : IsKernelPolynomial K E C h) {P R : (E⁄K).Point} (hP : P ∉ C) (hR : R ∉ C) :
    quotientPointFun K E C hh (P + R)
      = quotientPointFun K E C hh P + quotientPointFun K E C hh R :=
  sorry

omit [IsSepClosure k K] in
/-- Additivity of the quotient point map. The cases where either summand lies in the
kernel are PROVED from the `C`-invariance of the translate sums; the essential case is
the narrowed leaf `quotientPointFun_add_of_notMem`. -/
theorem quotientPointFun_add [E.IsElliptic]
    (C : AddSubgroup (E⁄K).Point) [Finite C] {h : k[X]}
    (hh : IsKernelPolynomial K E C h) (P R : (E⁄K).Point) :
    quotientPointFun K E C hh (P + R)
      = quotientPointFun K E C hh P + quotientPointFun K E C hh R := by
  by_cases hP : P ∈ C <;> by_cases hR : R ∈ C
  · -- both in the kernel: everything is `0`
    rw [quotientPointFun_apply_of_mem K E C hh hP, quotientPointFun_apply_of_mem K E C hh hR,
      quotientPointFun_apply_of_mem K E C hh (C.add_mem hP hR), add_zero]
  · -- `P` in the kernel: translation invariance
    have hPR : P + R ∉ C := fun hmem => hR (by simpa using C.sub_mem hmem hP)
    rw [quotientPointFun_apply_of_mem K E C hh hP, zero_add,
      quotientPointFun_apply_of_notMem K E C hh hPR,
      quotientPointFun_apply_of_notMem K E C hh hR]
    simp only [Affine.Point.some.injEq]
    rw [add_comm P R]
    exact ⟨quotientX_add_mem K E C R hP, quotientY_add_mem K E C R hP⟩
  · -- `R` in the kernel: translation invariance
    have hPR : P + R ∉ C := fun hmem => hP (by simpa using C.sub_mem hmem hR)
    rw [quotientPointFun_apply_of_mem K E C hh hR, add_zero,
      quotientPointFun_apply_of_notMem K E C hh hPR,
      quotientPointFun_apply_of_notMem K E C hh hP]
    simp only [Affine.Point.some.injEq]
    exact ⟨quotientX_add_mem K E C P hR, quotientY_add_mem K E C P hR⟩
  · exact quotientPointFun_add_of_notMem K E C hh hP hR

/-- **The quotient point map** `E(K) →+ (E/C)(K)` — now a REAL definition: Vélu's translate
sums bundled with the additivity leaf. -/
noncomputable def quotientPointHom [E.IsElliptic]
    (C : AddSubgroup (E⁄K).Point) [Finite C] {h : k[X]}
    (hh : IsKernelPolynomial K E C h) :
    (E⁄K).Point →+ ((quotientCurve E h)⁄K).Point where
  toFun := quotientPointFun K E C hh
  map_zero' := quotientPointFun_apply_of_mem K E C hh (zero_mem C)
  map_add' := quotientPointFun_add K E C hh

/-- The predicate on a triple `(φx, φyLin, φyConst)` of rational functions over `k`: away
from the poles of the first, the quotient point map is given by evaluating them. -/
def IsQuotientPhiData [E.IsElliptic] (C : AddSubgroup (E⁄K).Point) [Finite C] {h : k[X]}
    (hh : IsKernelPolynomial K E C h) (p : RatFunc k × RatFunc k × RatFunc k) : Prop :=
  ∀ (x y : K) (hxy : (E⁄K).Nonsingular x y),
    p.1.denom.eval₂ (algebraMap k K) x ≠ 0 →
    ∃ hxy' : ((quotientCurve E h)⁄K).Nonsingular
        (p.1.num.eval₂ (algebraMap k K) x / p.1.denom.eval₂ (algebraMap k K) x)
        (p.2.1.num.eval₂ (algebraMap k K) x / p.2.1.denom.eval₂ (algebraMap k K) x * y
          + p.2.2.num.eval₂ (algebraMap k K) x / p.2.2.denom.eval₂ (algebraMap k K) x),
      quotientPointHom K E C hh (Affine.Point.some x y hxy) = Affine.Point.some _ _ hxy'

/-- Rationality leaf: THE remaining content about the quotient map's shape — Vélu's
translate sums are induced, away from the poles, by a triple of rational functions over
`k` (`φx` with denominator `h²`, the y-maps with denominator `h³`; Kohel §2.4, Washington
§12.3, where the explicit numerators are written down). This one existence statement
consolidates what were previously three unpinned rational-map data leaves plus the
coherence leaf. -/
theorem exists_isQuotientPhiData [E.IsElliptic]
    (C : AddSubgroup (E⁄K).Point) [Finite C] {h : k[X]}
    (hh : IsKernelPolynomial K E C h) :
    ∃ p : RatFunc k × RatFunc k × RatFunc k, IsQuotientPhiData K E C hh p :=
  sorry

open Classical in
/-- The rational maps of the quotient isogeny, extracted by choice from the rationality
leaf (junk `(0, 0, 0)` if it were to fail). Replacing this by Kohel's explicit formulas —
and proving `exists_isQuotientPhiData` with them — is the intended future strengthening. -/
noncomputable def quotientPhiData [E.IsElliptic]
    (C : AddSubgroup (E⁄K).Point) [Finite C] {h : k[X]}
    (hh : IsKernelPolynomial K E C h) : RatFunc k × RatFunc k × RatFunc k :=
  if H : ∃ p : RatFunc k × RatFunc k × RatFunc k, IsQuotientPhiData K E C hh p then H.choose
  else (0, 0, 0)

/-- x-coordinate rational map of the quotient isogeny. -/
noncomputable def quotientPhiX [E.IsElliptic]
    (C : AddSubgroup (E⁄K).Point) [Finite C] {h : k[X]}
    (hh : IsKernelPolynomial K E C h) : RatFunc k :=
  (quotientPhiData K E C hh).1

/-- Coefficient of `y` in the y-coordinate map of the quotient isogeny. -/
noncomputable def quotientPhiYLin [E.IsElliptic]
    (C : AddSubgroup (E⁄K).Point) [Finite C] {h : k[X]}
    (hh : IsKernelPolynomial K E C h) : RatFunc k :=
  (quotientPhiData K E C hh).2.1

/-- y-independent part of the y-coordinate map of the quotient isogeny. -/
noncomputable def quotientPhiYConst [E.IsElliptic]
    (C : AddSubgroup (E⁄K).Point) [Finite C] {h : k[X]}
    (hh : IsKernelPolynomial K E C h) : RatFunc k :=
  (quotientPhiData K E C hh).2.2

/-- The chosen rational maps do satisfy the coherence predicate (from the rationality
leaf). -/
theorem isQuotientPhiData_quotientPhiData [E.IsElliptic]
    (C : AddSubgroup (E⁄K).Point) [Finite C] {h : k[X]}
    (hh : IsKernelPolynomial K E C h) :
    IsQuotientPhiData K E C hh (quotientPhiData K E C hh) := by
  have H := exists_isQuotientPhiData K E C hh
  rw [quotientPhiData, dif_pos H]
  exact H.choose_spec

/-- Coherence — now a theorem: away from the poles of `φx`, the quotient point map is
given by evaluating the rational maps (immediate from `isQuotientPhiData_quotientPhiData`,
which carries the rationality leaf). -/
theorem quotientPointHom_some [E.IsElliptic]
    (C : AddSubgroup (E⁄K).Point) [Finite C] {h : k[X]}
    (hh : IsKernelPolynomial K E C h) (x y : K) (hxy : (E⁄K).Nonsingular x y)
    (hden : (quotientPhiX K E C hh).denom.eval₂ (algebraMap k K) x ≠ 0) :
    ∃ hxy' : ((quotientCurve E h)⁄K).Nonsingular
        ((quotientPhiX K E C hh).num.eval₂ (algebraMap k K) x
          / (quotientPhiX K E C hh).denom.eval₂ (algebraMap k K) x)
        ((quotientPhiYLin K E C hh).num.eval₂ (algebraMap k K) x
            / (quotientPhiYLin K E C hh).denom.eval₂ (algebraMap k K) x * y
          + (quotientPhiYConst K E C hh).num.eval₂ (algebraMap k K) x
            / (quotientPhiYConst K E C hh).denom.eval₂ (algebraMap k K) x),
      quotientPointHom K E C hh (Affine.Point.some x y hxy) = Affine.Point.some _ _ hxy' :=
  isQuotientPhiData_quotientPhiData K E C hh x y hxy hden

/-- Cofinite-range leaf: all but finitely many points of the quotient curve are in the
image of the quotient point map. (The quotient isogeny is separable — its kernel consists
of honest `K`-points — so away from finitely many branch points the fiber equations are
separable and their solutions over `K = kˢᵉᵖ` are `K`-rational.) Full surjectivity follows
by pure group theory (`AddSubgroup.eq_top_of_compl_finite`), so ramified points need no
separate analysis. -/
theorem finite_compl_range_quotientPointHom [E.IsElliptic]
    (C : AddSubgroup (E⁄K).Point) [Finite C] {h : k[X]}
    (hh : IsKernelPolynomial K E C h) :
    (((quotientPointHom K E C hh).range : Set ((quotientCurve E h)⁄K).Point)ᶜ).Finite :=
  sorry

/-- Surjectivity — now a theorem, from the cofinite-range leaf: the range is a subgroup
with finite complement in the (infinite, by `Affine.Point.infinite`) group of points of the
quotient curve, hence everything. -/
theorem surjective_quotientPointHom [E.IsElliptic]
    (C : AddSubgroup (E⁄K).Point) [Finite C] {h : k[X]}
    (hh : IsKernelPolynomial K E C h) :
    Function.Surjective (quotientPointHom K E C hh) := by
  haveI : IsSepClosed K := IsSepClosure.sep_closed k
  haveI : (quotientCurve E h).IsElliptic := isElliptic_quotientCurve K E C hh
  haveI : ((quotientCurve E h)⁄K).IsElliptic :=
    inferInstanceAs (((quotientCurve E h).map (algebraMap k K)).IsElliptic)
  haveI : Infinite ((quotientCurve E h)⁄K).Point :=
    Affine.Point.infinite ((quotientCurve E h)⁄K)
  rw [← AddMonoidHom.range_eq_top]
  exact AddSubgroup.eq_top_of_compl_finite _ (finite_compl_range_quotientPointHom K E C hh)

omit [IsSepClosure k K] in
/-- Kernel — now a theorem: points of `C` map to `0` by definition, and points outside `C`
map to affine points, which are nonzero. -/
theorem ker_quotientPointHom [E.IsElliptic]
    (C : AddSubgroup (E⁄K).Point) [Finite C] {h : k[X]}
    (hh : IsKernelPolynomial K E C h) :
    (quotientPointHom K E C hh).ker = C := by
  ext P
  rw [AddMonoidHom.mem_ker]
  refine ⟨fun h0 => ?_, fun hP => quotientPointFun_apply_of_mem K E C hh hP⟩
  by_contra hP
  rw [show quotientPointHom K E C hh P = quotientPointFun K E C hh P from rfl,
    quotientPointFun_apply_of_notMem K E C hh hP] at h0
  exact Affine.Point.some_ne_zero _ h0

/-- **The quotient isogeny `E → E/C`** — a REAL assembly of the data leaves
(`quotientPhiX/YLin/YConst`, `quotientPointHom`) and the property leaves
(`quotientPointHom_some`, `surjective_quotientPointHom`, `ker_quotientPointHom`);
`finite_ker` comes for free from `ker = C` and `Finite C`. -/
noncomputable def quotientIsogeny [E.IsElliptic]
    (C : AddSubgroup (E⁄K).Point) [Finite C] {h : k[X]}
    (hh : IsKernelPolynomial K E C h) :
    Isogeny K E (quotientCurve E h) where
  φx := quotientPhiX K E C hh
  φyLin := quotientPhiYLin K E C hh
  φyConst := quotientPhiYConst K E C hh
  toHom := quotientPointHom K E C hh
  toHom_some := quotientPointHom_some K E C hh
  surjective := surjective_quotientPointHom K E C hh
  finite_ker := by rw [ker_quotientPointHom K E C hh]; exact ‹Finite C›

/-- The kernel of the quotient isogeny is exactly `C` (now immediate from the kernel
leaf). -/
theorem ker_quotientIsogeny [E.IsElliptic]
    (C : AddSubgroup (E⁄K).Point) [Finite C] {h : k[X]}
    (hh : IsKernelPolynomial K E C h) :
    (quotientIsogeny K E C hh).toHom.ker = C :=
  ker_quotientPointHom K E C hh

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
