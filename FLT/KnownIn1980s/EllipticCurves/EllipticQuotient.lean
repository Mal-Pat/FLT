module

public import Mathlib.Algebra.BigOperators.Finprod
public import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
public import Mathlib.FieldTheory.Galois.Infinite
public import Mathlib.FieldTheory.IsSepClosed
public import Mathlib.FieldTheory.RatFunc.Basic
public import Mathlib.GroupTheory.QuotientGroup.Basic

/-!

# Quotient of an elliptic curve by a finite Galois-stable subgroup

If `E` is an elliptic curve over a field `k` and `C ⊆ E(kˢᵉᵖ)` is a finite subgroup which is
stable under the action of `Gal(kˢᵉᵖ/k)`, then there is an elliptic curve `E'` over `k` and a
separable `k`-isogeny `E → E'` whose kernel is exactly `C`; the curve `E'` is the quotient
`E/C`. The main theorem is `exists_pointsHom_surjective_ker_eq`; it is stated so as to be
*faithful* to this: its coherence clauses pin the witnesses to the concrete Vélu data defined
in this file (`E'` base-changes to *the* Vélu quotient curve, and `φ` agrees off `C` with
*the* Vélu coordinate functions), so no degenerate witnesses are possible, and the
`k`-rationality of the quotient is carried by `E'` living over `k` together with the (proved)
Galois-fixedness of the Vélu data. The file is organised as a *proof decomposition*: a Vélu
layer over an arbitrary field and a Galois-descent layer. **All construction data is real** —
the quotient curve and the quotient map are honestly defined by Vélu's formulas — and every
remaining `sorry` is a proposition about that data.

## Layer 1 (Vélu, over an arbitrary field `K`)
For a finite subgroup `C ⊆ E(K)`, Vélu's formulas [Vélu, *Isogénies entre courbes
elliptiques*, C. R. Acad. Sci. Paris 273 (1971); Washington, *Elliptic Curves*, §12.3]
produce:
* the quotient curve `E.veluQuotient C` (**defined**, via the sums `veluT`, `veluW` — see
  their docstrings for the choice-free per-point form used here and its equivalence with the
  orbit sums in the literature), with the sanity check `veluQuotient_bot : E/⊥ = E`
  (**proved**);
* the quotient map `E.veluMap C` (**defined**: on points it is Vélu's
  `P ↦ (x(P) + Σ_{Q ∈ C∖0} (x(P+Q) - x(Q)), y(P) + Σ_{Q ∈ C∖0} (y(P+Q) - y(Q)))`, computed
  with the group law of `E`, and `C ↦ 0`), with `ker = C` (**proved**: points of `C` map to
  `0` by definition, and points outside `C` map to affine points, which are nonzero);
* the first isomorphism theorem `E(K)/C ≃+ (E/C)(K)` (`veluQuotientEquiv`, **proved**).

The `sorry` leaves of this layer are all propositions:
`isElliptic_veluQuotient` (the quotient is smooth), `nonsingular_veluX_veluY` (images of
points off `C` land on the quotient curve), `veluMapFun_add` (additivity — the deepest),
and `surjective_veluMap` (surjectivity over a separably closed field).

## Layer 2 (Galois action and descent to `k`)
* The action of `Gal(kˢᵉᵖ/k)` on `E(kˢᵉᵖ)` as a `DistribMulAction` instance (**proved**):
  `σ • P` is `Affine.Point.map σ.toAlgHom P` — "the mod-nothing Galois representation" —
  together with equivariance of the coordinate functions and of Vélu's `gˣ`, `gʸ`
  (`xCoord_smul`, `yCoord_smul`, `veluGx_smul`, `veluGy_smul`, all **proved**).
* `Affine.Point.map_mem_ker` (**proved**): the kernel of a Galois-equivariant homomorphism on
  points is Galois-stable.
* `exists_baseChange_eq_of_forall_map_eq` (**proved**): a Weierstrass curve over `kˢᵉᵖ` whose
  coefficients are fixed by `Gal(kˢᵉᵖ/k)` descends to `k`, via
  `InfiniteGalois.mem_range_algebraMap_iff_fixed` (mathlib has `IsSepClosure.isGalois`, so
  `IsGalois k ksep` is automatic).
* `isElliptic_of_baseChange` (**proved**): ellipticity descends along base change.
* `veluQuotient_map_eq_of_galoisStable` (**proved**): if `C` is Galois-stable then the Vélu
  quotient curve is Galois-fixed — each `σ` permutes `C ∖ {0}` and commutes with the
  polynomial summands of `veluT`, `veluW`, whose coefficients come from `k`.
* `exists_pointsHom_surjective_ker_eq` (**proved** from the above): the main theorem — for
  `C ⊆ E(kˢᵉᵖ)` finite and Galois-stable there is an elliptic `E'/k` with
  `E'⁄kˢᵉᵖ = (E⁄kˢᵉᵖ).veluQuotient C` and a surjective `φ : E(kˢᵉᵖ) →+ E'(kˢᵉᵖ)` with
  `ker φ = C`, agreeing off `C` with `(veluX, veluY)`.

The remaining `sorry`s are exactly the four Layer-1 propositions listed above — the
computational core of Vélu's theorem; every definition is real, and the descent layer and
main theorem are fully proved from those four leaves. (A still stronger endpoint would
additionally expose `veluX`, `veluY` as rational functions over `k` in the sense of
`RatFunc`, via Vélu's expansion `X = x + Σ_Q (v_Q/(x - x_Q) + u_Q/(x - x_Q)²)`; that upgrade
is deliberately left out.)
-/

@[expose] public section

open scoped WeierstrassCurve.Affine -- `(E⁄K).Point` notation for the group of `K`-points

namespace WeierstrassCurve

/-! ### Layer 1: Vélu's construction over an arbitrary field -/

section Velu

-- let K be a field (`DecidableEq` is needed for the group law on points)
variable {K : Type*} [Field K] [DecidableEq K]

/-- The `x`-coordinate of an affine point, with junk value `0` at the point at infinity. -/
def Affine.Point.xCoord {W : Affine K} : W.Point → K
  | .zero => 0
  | .some x _ _ => x

/-- The `y`-coordinate of an affine point, with junk value `0` at the point at infinity. -/
def Affine.Point.yCoord {W : Affine K} : W.Point → K
  | .zero => 0
  | .some _ y _ => y

/-- Vélu's quantity `gˣ_Q = 3x_Q² + 2a₂x_Q + a₄ - a₁y_Q` attached to an affine point `Q`
(the derivative `∂/∂x` of the Weierstrass equation at `Q`), with junk value `0` at `0`. -/
def veluGx (E : WeierstrassCurve K) : E.toAffine.Point → K
  | .zero => 0
  | .some x y _ => 3 * x ^ 2 + 2 * E.a₂ * x + E.a₄ - E.a₁ * y

/-- Vélu's quantity `gʸ_Q = -(2y_Q + a₁x_Q + a₃)` attached to an affine point `Q`
(the derivative `-∂/∂y` of the Weierstrass equation at `Q`; it vanishes iff `Q` is
`2`-torsion), with junk value `0` at `0`. -/
def veluGy (E : WeierstrassCurve K) : E.toAffine.Point → K
  | .zero => 0
  | .some x y _ => -(2 * y + E.a₁ * x + E.a₃)

/-- **Vélu's `t`**, in choice-free per-point form: `t = Σ_{Q ∈ C∖{0}} gˣ_Q`.

The literature (Vélu; Washington §12.3) sums `v_Q` over representatives `R` of
`(C∖{0})/±` with `v_Q = gˣ_Q` for `2`-torsion `Q` and `v_Q = 2gˣ_Q - a₁gʸ_Q` otherwise.
This agrees with the sum here: `gʸ_{-Q} = -gʸ_Q` and `gˣ_{-Q} = gˣ_Q - a₁gʸ_Q`, so summing
`gˣ` over a two-element fibre `{Q, -Q}` gives exactly `2gˣ_Q - a₁gʸ_Q = v_Q`, while a
one-element fibre (i.e. `2`-torsion, `gʸ_Q = 0`) contributes `gˣ_Q = v_Q`. -/
noncomputable def veluT (E : WeierstrassCurve K) (C : AddSubgroup E.toAffine.Point) : K :=
  ∑ᶠ Q ∈ (C : Set E.toAffine.Point) \ {0}, E.veluGx Q

/-- **Vélu's `w`**, in choice-free per-point form:
`w = Σ_{Q ∈ C∖{0}} (x_Q·gˣ_Q - y_Q·gʸ_Q)`.

The literature sums `u_Q + x_Q v_Q` over representatives of `(C∖{0})/±`, where
`u_Q = (gʸ_Q)²`. This agrees with the sum here: over a two-element fibre `{Q, -Q}` the
`x·gˣ` part sums to `x_Q v_Q` as in `veluT`, and since
`y_{-Q}·gʸ_{-Q} = (-y_Q - a₁x_Q - a₃)(-gʸ_Q)`, the `-y·gʸ` part sums to
`-gʸ_Q(y_Q - y_{-Q}) = (gʸ_Q)² = u_Q`; a one-element fibre has `gʸ_Q = 0` and contributes
`x_Q gˣ_Q = u_Q + x_Q v_Q`. -/
noncomputable def veluW (E : WeierstrassCurve K) (C : AddSubgroup E.toAffine.Point) : K :=
  ∑ᶠ Q ∈ (C : Set E.toAffine.Point) \ {0},
    (Q.xCoord * E.veluGx Q - Q.yCoord * E.veluGy Q)

/-- **Vélu's quotient curve** `E/C` for a subgroup `C ⊆ E(K)`:
`⟨a₁, a₂, a₃, a₄ - 5t, a₆ - b₂t - 7w⟩` where `b₂ = a₁² + 4a₂`
[Vélu; Washington, Theorem 12.16]. (For infinite `C` the sums are junk (zero); all theorems
assume `[Finite C]`.) -/
noncomputable def veluQuotient (E : WeierstrassCurve K)
    (C : AddSubgroup E.toAffine.Point) : WeierstrassCurve K :=
  ⟨E.a₁, E.a₂, E.a₃, E.a₄ - 5 * E.veluT C, E.a₆ - E.b₂ * E.veluT C - 7 * E.veluW C⟩

/-- Sanity check: the quotient of `E` by the trivial subgroup is `E` itself. -/
@[simp]
theorem veluQuotient_bot (E : WeierstrassCurve K) :
    E.veluQuotient (⊥ : AddSubgroup E.toAffine.Point) = E := by
  ext <;> simp [veluQuotient, veluT, veluW]

/-- The `x`-coordinate of Vélu's isogeny, as a function on points of `E`:
`X(P) = x(P) + Σ_{Q ∈ C∖{0}} (x(P+Q) - x(Q))`, computed with the group law of `E`.
This is Vélu's defining formula for the invariant function `X`; his rational expression
`X = x + Σ_Q (v_Q/(x - x_Q) + u_Q/(x - x_Q)²)` is its closed form. Junk when `P ∈ C`. -/
noncomputable def veluX (E : WeierstrassCurve K) (C : AddSubgroup E.toAffine.Point)
    (P : E.toAffine.Point) : K :=
  P.xCoord + ∑ᶠ Q ∈ (C : Set E.toAffine.Point) \ {0}, ((P + Q).xCoord - Q.xCoord)

/-- The `y`-coordinate of Vélu's isogeny, as a function on points of `E`:
`Y(P) = y(P) + Σ_{Q ∈ C∖{0}} (y(P+Q) - y(Q))`. Junk when `P ∈ C`. -/
noncomputable def veluY (E : WeierstrassCurve K) (C : AddSubgroup E.toAffine.Point)
    (P : E.toAffine.Point) : K :=
  P.yCoord + ∑ᶠ Q ∈ (C : Set E.toAffine.Point) \ {0}, ((P + Q).yCoord - Q.yCoord)

/-- The Vélu quotient of an elliptic curve is elliptic (nonvanishing discriminant).
(`sorry` leaf.) -/
theorem isElliptic_veluQuotient (E : WeierstrassCurve K) [E.IsElliptic]
    (C : AddSubgroup E.toAffine.Point) [Finite C] : (E.veluQuotient C).IsElliptic := sorry

/-- For `P ∉ C`, the image `(X(P), Y(P))` of Vélu's isogeny is a nonsingular point of the
quotient curve. This is the computational heart of Vélu's theorem. (`sorry` leaf.) -/
theorem nonsingular_veluX_veluY (E : WeierstrassCurve K) [E.IsElliptic]
    (C : AddSubgroup E.toAffine.Point) [Finite C] {P : E.toAffine.Point} (hP : P ∉ C) :
    (E.veluQuotient C).toAffine.Nonsingular (E.veluX C P) (E.veluY C P) := sorry

open scoped Classical in
/-- The underlying function of Vélu's isogeny: `C ↦ 0`, and
`P ↦ (X(P), Y(P))` for `P ∉ C`. -/
noncomputable def veluMapFun (E : WeierstrassCurve K) [E.IsElliptic]
    (C : AddSubgroup E.toAffine.Point) [Finite C] (P : E.toAffine.Point) :
    (E.veluQuotient C).toAffine.Point :=
  if hP : P ∈ C then 0 else .some _ _ (nonsingular_veluX_veluY E C hP)

theorem veluMapFun_apply_of_mem (E : WeierstrassCurve K) [E.IsElliptic]
    (C : AddSubgroup E.toAffine.Point) [Finite C] {P : E.toAffine.Point} (hP : P ∈ C) :
    E.veluMapFun C P = 0 :=
  dif_pos hP

theorem veluMapFun_apply_of_notMem (E : WeierstrassCurve K) [E.IsElliptic]
    (C : AddSubgroup E.toAffine.Point) [Finite C] {P : E.toAffine.Point} (hP : P ∉ C) :
    E.veluMapFun C P = .some _ _ (nonsingular_veluX_veluY E C hP) :=
  dif_neg hP

/-- Vélu's isogeny is additive. This is the deepest leaf: on paper it follows from `(X, Y)`
being translation-invariant functions on `E`, so that `veluMapFun` is a morphism of curves
sending `0` to `0`, hence a group homomorphism. (`sorry` leaf.) -/
theorem veluMapFun_add (E : WeierstrassCurve K) [E.IsElliptic]
    (C : AddSubgroup E.toAffine.Point) [Finite C] (P R : E.toAffine.Point) :
    E.veluMapFun C (P + R) = E.veluMapFun C P + E.veluMapFun C R := sorry

/-- **Vélu's isogeny** `E → E/C`, bundled as a group homomorphism on `K`-points. The data is
real (`veluMapFun`); additivity is the `sorry` leaf `veluMapFun_add`. -/
noncomputable def veluMap (E : WeierstrassCurve K) [E.IsElliptic]
    (C : AddSubgroup E.toAffine.Point) [Finite C] :
    E.toAffine.Point →+ (E.veluQuotient C).toAffine.Point where
  toFun := E.veluMapFun C
  map_zero' := E.veluMapFun_apply_of_mem C (zero_mem C)
  map_add' := E.veluMapFun_add C

/-- The kernel of Vélu's isogeny is exactly `C`. **Proved**: points of `C` map to `0` by
definition, and points outside `C` map to affine points, which are nonzero. -/
theorem ker_veluMap (E : WeierstrassCurve K) [E.IsElliptic]
    (C : AddSubgroup E.toAffine.Point) [Finite C] : (E.veluMap C).ker = C := by
  ext P
  rw [AddMonoidHom.mem_ker]
  refine ⟨fun h => ?_, fun hP => E.veluMapFun_apply_of_mem C hP⟩
  by_contra hP
  rw [show E.veluMap C P = E.veluMapFun C P from rfl,
    E.veluMapFun_apply_of_notMem C hP] at h
  exact Affine.Point.some_ne_zero _ h

/-- Over a separably closed field, Vélu's isogeny is surjective on points: it is separable
(its kernel consists of honest points, so is étale) and separable isogenies are étale.
(`sorry` leaf.) -/
theorem surjective_veluMap (E : WeierstrassCurve K) [E.IsElliptic] [IsSepClosed K]
    (C : AddSubgroup E.toAffine.Point) [Finite C] :
    Function.Surjective (E.veluMap C) := sorry

/-- **First isomorphism theorem for the Vélu isogeny** over a separably closed field:
`E(K)/C ≃+ (E/C)(K)`. In particular the isogeny has degree `|C|`. Proved from the interface
above. -/
noncomputable def veluQuotientEquiv (E : WeierstrassCurve K) [E.IsElliptic] [IsSepClosed K]
    (C : AddSubgroup E.toAffine.Point) [Finite C] :
    (E.toAffine.Point ⧸ C) ≃+ (E.veluQuotient C).toAffine.Point :=
  (QuotientAddGroup.quotientAddEquivOfEq (E.ker_veluMap C).symm).trans
    (QuotientAddGroup.quotientKerEquivOfSurjective _ (E.surjective_veluMap C))

end Velu

/-! ### Layer 2: the Galois action on points -/

section GaloisAction

variable {k : Type*} [Field k]
variable {ksep : Type*} [Field ksep] [Algebra k ksep] [DecidableEq ksep]

/-- `Affine.Point.map` along an algebra homomorphism that is pointwise the identity is the
identity. -/
theorem Affine.Point.map_eq_self {E : WeierstrassCurve k} {f : ksep →ₐ[k] ksep}
    (hf : f = AlgHom.id k ksep) (P : (E⁄ksep).Point) : Affine.Point.map f P = P := by
  subst hf
  cases P <;> rfl

/-- **The Galois action of `Gal(kˢᵉᵖ/k)` on `E(kˢᵉᵖ)`** (the "mod-nothing Galois
representation"): `σ • P` is mathlib's `WeierstrassCurve.Affine.Point.map σ.toAlgHom P`.
Fully proved. -/
noncomputable instance (E : WeierstrassCurve k) :
    DistribMulAction (ksep ≃ₐ[k] ksep) (E⁄ksep).Point where
  smul σ P := Affine.Point.map σ.toAlgHom P
  one_smul P := Affine.Point.map_eq_self (AlgHom.ext fun _ => rfl) P
  mul_smul σ τ P := by
    change Affine.Point.map (σ * τ).toAlgHom P
      = Affine.Point.map σ.toAlgHom (Affine.Point.map τ.toAlgHom P)
    rw [Affine.Point.map_map,
      show σ.toAlgHom.comp τ.toAlgHom = (σ * τ).toAlgHom from AlgHom.ext fun _ => rfl]
  smul_zero σ := map_zero (Affine.Point.map σ.toAlgHom)
  smul_add σ P Q := map_add (Affine.Point.map σ.toAlgHom) P Q

@[simp]
theorem Affine.Point.algEquiv_smul_def {E : WeierstrassCurve k} (σ : ksep ≃ₐ[k] ksep)
    (P : (E⁄ksep).Point) : σ • P = Affine.Point.map σ.toAlgHom P :=
  rfl

/-- The `x`-coordinate commutes with the Galois action. Fully proved. -/
@[simp]
theorem Affine.Point.xCoord_smul {E : WeierstrassCurve k} (σ : ksep ≃ₐ[k] ksep)
    (P : (E⁄ksep).Point) : (σ • P).xCoord = σ P.xCoord := by
  cases P with
  | zero => exact (_root_.map_zero σ).symm
  | some x y h => rfl

/-- The `y`-coordinate commutes with the Galois action. Fully proved. -/
@[simp]
theorem Affine.Point.yCoord_smul {E : WeierstrassCurve k} (σ : ksep ≃ₐ[k] ksep)
    (P : (E⁄ksep).Point) : (σ • P).yCoord = σ P.yCoord := by
  cases P with
  | zero => exact (_root_.map_zero σ).symm
  | some x y h => rfl

/-- `veluGx` commutes with the Galois action: `gˣ` is a polynomial in the coordinates whose
coefficients come from `k`. Fully proved. -/
theorem veluGx_smul {E : WeierstrassCurve k} (σ : ksep ≃ₐ[k] ksep) (Q : (E⁄ksep).Point) :
    (E⁄ksep).veluGx (σ • Q) = σ ((E⁄ksep).veluGx Q) := by
  have hcoe : ∀ x : ksep, σ.toAlgHom x = σ x := fun _ => rfl
  have ha₁ : σ ((E⁄ksep).a₁) = (E⁄ksep).a₁ := σ.commutes E.a₁
  have ha₂ : σ ((E⁄ksep).a₂) = (E⁄ksep).a₂ := σ.commutes E.a₂
  have ha₄ : σ ((E⁄ksep).a₄) = (E⁄ksep).a₄ := σ.commutes E.a₄
  cases Q with
  | zero => exact (_root_.map_zero σ).symm
  | some x y h =>
    rw [show σ • Affine.Point.some x y h = Affine.Point.map σ.toAlgHom (.some x y h) from rfl,
      Affine.Point.map_some]
    simp only [veluGx, hcoe, map_sub, map_add, map_mul, map_pow, map_ofNat, ha₁, ha₂, ha₄]

/-- `veluGy` commutes with the Galois action. Fully proved. -/
theorem veluGy_smul {E : WeierstrassCurve k} (σ : ksep ≃ₐ[k] ksep) (Q : (E⁄ksep).Point) :
    (E⁄ksep).veluGy (σ • Q) = σ ((E⁄ksep).veluGy Q) := by
  have hcoe : ∀ x : ksep, σ.toAlgHom x = σ x := fun _ => rfl
  have ha₁ : σ ((E⁄ksep).a₁) = (E⁄ksep).a₁ := σ.commutes E.a₁
  have ha₃ : σ ((E⁄ksep).a₃) = (E⁄ksep).a₃ := σ.commutes E.a₃
  cases Q with
  | zero => exact (_root_.map_zero σ).symm
  | some x y h =>
    rw [show σ • Affine.Point.some x y h = Affine.Point.map σ.toAlgHom (.some x y h) from rfl,
      Affine.Point.map_some]
    simp only [veluGy, hcoe, map_neg, map_add, map_mul, map_ofNat, ha₁, ha₃]

/-- The kernel of a Galois-equivariant homomorphism on `kˢᵉᵖ`-points is Galois-stable.
Fully proved. (In the faithful form of the statement, equivariance itself is
a consequence of the map being defined over `k`; here it is taken as a hypothesis.) -/
theorem Affine.Point.map_mem_ker {E E' : WeierstrassCurve k}
    (φ : (E⁄ksep).Point →+ (E'⁄ksep).Point)
    (hφ : ∀ (σ : ksep ≃ₐ[k] ksep) (P : (E⁄ksep).Point),
      φ (Affine.Point.map σ.toAlgHom P) = Affine.Point.map σ.toAlgHom (φ P))
    (σ : ksep ≃ₐ[k] ksep) {P : (E⁄ksep).Point} (hP : P ∈ φ.ker) :
    Affine.Point.map σ.toAlgHom P ∈ φ.ker := by
  rw [AddMonoidHom.mem_ker] at hP ⊢
  rw [hφ, hP]
  exact map_zero _

end GaloisAction

/-! ### Layer 2: Galois descent -/

section Descent

variable {k : Type*} [Field k]
variable {ksep : Type*} [Field ksep] [Algebra k ksep] [IsSepClosure k ksep]

/-- **Galois descent for Weierstrass curves.** A Weierstrass curve over `kˢᵉᵖ` whose
coefficients are fixed by every element of `Gal(kˢᵉᵖ/k)` is the base change of a curve over
`k`. Fully proved, via `InfiniteGalois.mem_range_algebraMap_iff_fixed`. -/
theorem exists_baseChange_eq_of_forall_map_eq (W : WeierstrassCurve ksep)
    (hW : ∀ σ : ksep ≃ₐ[k] ksep, W.map (σ : ksep →+* ksep) = W) :
    ∃ W₀ : WeierstrassCurve k, W₀⁄ksep = W := by
  have fix : ∀ x : ksep, (∀ σ : ksep ≃ₐ[k] ksep, σ x = x) →
      ∃ b : k, algebraMap k ksep b = x := fun x hx =>
    (InfiniteGalois.mem_range_algebraMap_iff_fixed x).mpr hx
  have coeff : ∀ (σ : ksep ≃ₐ[k] ksep) (g : WeierstrassCurve ksep → ksep),
      g (W.map (σ : ksep →+* ksep)) = σ (g W) → σ (g W) = g W := fun σ g hg => by
    rw [← hg, hW σ]
  obtain ⟨b₁, hb₁⟩ := fix W.a₁ fun σ => coeff σ (·.a₁) (map_a₁ ..)
  obtain ⟨b₂, hb₂⟩ := fix W.a₂ fun σ => coeff σ (·.a₂) (map_a₂ ..)
  obtain ⟨b₃, hb₃⟩ := fix W.a₃ fun σ => coeff σ (·.a₃) (map_a₃ ..)
  obtain ⟨b₄, hb₄⟩ := fix W.a₄ fun σ => coeff σ (·.a₄) (map_a₄ ..)
  obtain ⟨b₆, hb₆⟩ := fix W.a₆ fun σ => coeff σ (·.a₆) (map_a₆ ..)
  exact ⟨⟨b₁, b₂, b₃, b₄, b₆⟩, by ext <;> simp [baseChange, hb₁, hb₂, hb₃, hb₄, hb₆]⟩

omit [IsSepClosure k ksep] in
/-- Ellipticity descends along base change to a field extension. Fully proved. -/
theorem isElliptic_of_baseChange (W₀ : WeierstrassCurve k)
    (h : (W₀⁄ksep).IsElliptic) : W₀.IsElliptic := by
  rw [isElliptic_iff, isUnit_iff_ne_zero] at h ⊢
  intro h0
  rw [show (W₀⁄ksep).Δ = algebraMap k ksep W₀.Δ from map_Δ .., h0, map_zero] at h
  exact h rfl

variable [DecidableEq ksep]

omit [IsSepClosure k ksep] in
/-- **Galois-fixedness of the Vélu quotient.** If `C ⊆ E(kˢᵉᵖ)` is Galois-stable then the
Vélu coefficients — the sums `veluT`, `veluW` over the coordinates of the points of
`C ∖ {0}` — are fixed by `Gal(kˢᵉᵖ/k)`: each `σ` permutes `C ∖ {0}` and commutes with the
polynomial summands, since the `a_i` of `E⁄kˢᵉᵖ` come from `k`. Fully proved. -/
theorem veluQuotient_map_eq_of_galoisStable (E : WeierstrassCurve k) [E.IsElliptic]
    (C : AddSubgroup (E⁄ksep).Point) [Finite C]
    (hC : ∀ σ : ksep ≃ₐ[k] ksep, ∀ P ∈ C, Affine.Point.map σ.toAlgHom P ∈ C)
    (σ : ksep ≃ₐ[k] ksep) :
    ((E⁄ksep).veluQuotient C).map (σ : ksep →+* ksep) = (E⁄ksep).veluQuotient C := by
  have hcoe : ∀ x : ksep, (σ : ksep →+* ksep) x = σ x := fun _ => rfl
  -- the Galois action permutes `C ∖ {0}`
  have hstab : ∀ τ : ksep ≃ₐ[k] ksep,
      (fun Q => τ • Q) '' ((C : Set (E⁄ksep).Point) \ {0}) ⊆
        (C : Set (E⁄ksep).Point) \ {0} := by
    rintro τ _ ⟨Q, ⟨hQC, hQ0⟩, rfl⟩
    refine ⟨hC τ Q hQC, fun h0 => hQ0 ?_⟩
    simp only [Set.mem_singleton_iff] at h0 ⊢
    exact MulAction.injective τ (h0.trans (smul_zero τ).symm)
  have himg : (fun Q => σ • Q) '' ((C : Set (E⁄ksep).Point) \ {0}) =
      (C : Set (E⁄ksep).Point) \ {0} :=
    Set.Subset.antisymm (hstab σ) fun Q hQ =>
      ⟨σ⁻¹ • Q, hstab σ⁻¹ ⟨Q, hQ, rfl⟩, smul_inv_smul σ Q⟩
  -- `σ` passes through finite sums over `C ∖ {0}` at the cost of reindexing by `σ • ·`
  have push : ∀ f : (E⁄ksep).Point → ksep,
      σ (∑ᶠ Q ∈ (C : Set (E⁄ksep).Point) \ {0}, f Q) =
        ∑ᶠ Q ∈ (C : Set (E⁄ksep).Point) \ {0}, σ (f Q) := by
    intro f
    rw [AddEquivClass.map_finsum σ]
    exact finsum_congr fun Q => AddEquivClass.map_finsum σ _
  have reindex : ∀ f : (E⁄ksep).Point → ksep,
      (∑ᶠ Q ∈ (C : Set (E⁄ksep).Point) \ {0}, f (σ • Q)) =
        ∑ᶠ Q ∈ (C : Set (E⁄ksep).Point) \ {0}, f Q := by
    intro f
    rw [← finsum_mem_image (f := f) ((MulAction.injective σ).injOn), himg]
  -- the two Vélu sums are fixed
  have hT : σ ((E⁄ksep).veluT C) = (E⁄ksep).veluT C := by
    rw [veluT, push]
    rw [show (∑ᶠ Q ∈ (C : Set (E⁄ksep).Point) \ {0}, σ ((E⁄ksep).veluGx Q)) =
        ∑ᶠ Q ∈ (C : Set (E⁄ksep).Point) \ {0}, (E⁄ksep).veluGx (σ • Q) from
      finsum_congr fun Q => finsum_congr fun _ => (veluGx_smul σ Q).symm]
    exact reindex _
  have hw : σ ((E⁄ksep).veluW C) = (E⁄ksep).veluW C := by
    rw [veluW, push]
    rw [show (∑ᶠ Q ∈ (C : Set (E⁄ksep).Point) \ {0},
          σ (Q.xCoord * (E⁄ksep).veluGx Q - Q.yCoord * (E⁄ksep).veluGy Q)) =
        ∑ᶠ Q ∈ (C : Set (E⁄ksep).Point) \ {0},
          ((σ • Q).xCoord * (E⁄ksep).veluGx (σ • Q)
            - (σ • Q).yCoord * (E⁄ksep).veluGy (σ • Q)) from
      finsum_congr fun Q => finsum_congr fun _ => by
        rw [map_sub, map_mul, map_mul, Affine.Point.xCoord_smul, Affine.Point.yCoord_smul,
          veluGx_smul, veluGy_smul]]
    exact reindex fun Q => Q.xCoord * (E⁄ksep).veluGx Q - Q.yCoord * (E⁄ksep).veluGy Q
  -- the coefficients of `E⁄kˢᵉᵖ` come from `k`, hence are fixed
  have ha₁ : σ ((E⁄ksep).a₁) = (E⁄ksep).a₁ := σ.commutes E.a₁
  have ha₂ : σ ((E⁄ksep).a₂) = (E⁄ksep).a₂ := σ.commutes E.a₂
  have ha₃ : σ ((E⁄ksep).a₃) = (E⁄ksep).a₃ := σ.commutes E.a₃
  have ha₄ : σ ((E⁄ksep).a₄) = (E⁄ksep).a₄ := σ.commutes E.a₄
  have ha₆ : σ ((E⁄ksep).a₆) = (E⁄ksep).a₆ := σ.commutes E.a₆
  have hb₂ : σ ((E⁄ksep).b₂) = (E⁄ksep).b₂ := by
    simp only [b₂, map_add, map_mul, map_pow, map_ofNat, ha₁, ha₂]
  ext <;>
    simp only [veluQuotient, map_a₁, map_a₂, map_a₃, map_a₄, map_a₆, hcoe, map_sub, map_mul,
      map_ofNat, ha₁, ha₂, ha₃, ha₄, ha₆, hb₂, hT, hw]

/-- **Quotient of an elliptic curve by a finite Galois-stable subgroup.**
If `C ⊆ E(kˢᵉᵖ)` is a finite Galois-stable subgroup, there is an elliptic curve `E'` over
`k` — whose base change to `kˢᵉᵖ` is *the Vélu quotient curve* — and a surjective
homomorphism `φ : E(kˢᵉᵖ) →+ E'(kˢᵉᵖ)` with `ker φ = C` which, away from `C`, is given by
*the Vélu coordinate functions* `veluX`, `veluY`.

The two coherence clauses pin `E'` and `φ` to the concrete Vélu data, so the statement
asserts exactly "the quotient curve descends to `k` and the quotient isogeny maps to it" —
no degenerate witnesses are possible. **Proved** from the Vélu interface and the descent
lemmas above. -/
theorem exists_pointsHom_surjective_ker_eq (E : WeierstrassCurve k) [E.IsElliptic]
    (C : AddSubgroup (E⁄ksep).Point) [Finite C]
    (hC : ∀ σ : ksep ≃ₐ[k] ksep, ∀ P ∈ C, Affine.Point.map σ.toAlgHom P ∈ C) :
    ∃ (E' : WeierstrassCurve k) (_ : E'.IsElliptic)
      (φ : (E⁄ksep).Point →+ (E'⁄ksep).Point),
      (E'⁄ksep) = (E⁄ksep).veluQuotient C ∧
      (∀ P : (E⁄ksep).Point, P ∉ C →
        (φ P).xCoord = (E⁄ksep).veluX C P ∧ (φ P).yCoord = (E⁄ksep).veluY C P) ∧
      Function.Surjective φ ∧ φ.ker = C := by
  haveI : (E⁄ksep).IsElliptic := inferInstanceAs ((E.map (algebraMap k ksep)).IsElliptic)
  haveI : IsSepClosed ksep := IsSepClosure.sep_closed k
  obtain ⟨E', hE'⟩ := exists_baseChange_eq_of_forall_map_eq ((E⁄ksep).veluQuotient C)
    (veluQuotient_map_eq_of_galoisStable E C hC)
  have hell : E'.IsElliptic := by
    refine isElliptic_of_baseChange (ksep := ksep) E' ?_
    rw [hE']
    exact isElliptic_veluQuotient (E⁄ksep) C
  have H : ∃ φ : (E⁄ksep).Point →+ ((E⁄ksep).veluQuotient C).toAffine.Point,
      (∀ P : (E⁄ksep).Point, P ∉ C →
        (φ P).xCoord = (E⁄ksep).veluX C P ∧ (φ P).yCoord = (E⁄ksep).veluY C P) ∧
      Function.Surjective φ ∧ φ.ker = C := by
    refine ⟨(E⁄ksep).veluMap C, fun P hP => ?_, (E⁄ksep).surjective_veluMap C,
      (E⁄ksep).ker_veluMap C⟩
    rw [show (E⁄ksep).veluMap C P = (E⁄ksep).veluMapFun C P from rfl,
      (E⁄ksep).veluMapFun_apply_of_notMem C hP]
    exact ⟨rfl, rfl⟩
  rw [← hE'] at H
  obtain ⟨φ, hφ, hsurj, hker⟩ := H
  exact ⟨E', hell, φ, hE', hφ, hsurj, hker⟩

end Descent

end WeierstrassCurve
