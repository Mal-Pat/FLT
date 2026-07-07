module

public import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
public import Mathlib.FieldTheory.Galois.Infinite
public import Mathlib.FieldTheory.IsSepClosed
public import Mathlib.GroupTheory.QuotientGroup.Basic

/-!

# Quotient of an elliptic curve by a finite Galois-stable subgroup: proof scaffold

Companion to `EllipticQuotient.lean`, which states the goal faithfully (with the rational
functions over `k` witnessing that the quotient map is an algebraic map defined over `k`) and
with zero new definitions. This file is the *proof decomposition*: it factors the theorem
into a Vélu layer over an arbitrary field and a Galois-descent layer, proves every piece of
glue that is provable against current mathlib, and isolates the genuinely open work into
clearly-named `sorry` leaves.

## Layer 1 (Vélu, over an arbitrary field `K`)
For a finite subgroup `C ⊆ E(K)`, Vélu's formulas [Vélu, *Isogénies entre courbes
elliptiques*] produce a curve `E.veluQuotient C` and a homomorphism `E.veluMap C` on points
with kernel exactly `C`, surjective when `K` is separably closed. The five `sorry`s here
(`veluQuotient`, `isElliptic_veluQuotient`, `veluMap`, `ker_veluMap`, `surjective_veluMap`)
are the mathematical core; everything after them is proved. The first isomorphism theorem
`E(K)/C ≃+ (E/C)(K)` (`veluQuotientEquiv`) is **proved** from the interface.

## Layer 2 (Galois action and descent to `k`)
* The action of `Gal(kˢᵉᵖ/k)` on `E(kˢᵉᵖ)` as a `DistribMulAction` instance (**proved**):
  `σ • P` is `Affine.Point.map σ.toAlgHom P` — "the mod-nothing Galois representation".
* `Affine.Point.map_mem_ker` (**proved**): the kernel of a Galois-equivariant homomorphism on
  points is Galois-stable.
* `exists_baseChange_eq_of_forall_map_eq` (**proved**): a Weierstrass curve over `kˢᵉᵖ` whose
  coefficients are fixed by `Gal(kˢᵉᵖ/k)` descends to `k`. This is the Galois-descent
  engine, via `InfiniteGalois.mem_range_algebraMap_iff_fixed` (mathlib has
  `IsSepClosure.isGalois`, so `IsGalois k ksep` is automatic).
* `isElliptic_of_baseChange` (**proved**): ellipticity descends along base change.
* `veluQuotient_map_eq_of_galoisStable` (`sorry` leaf): the Vélu coefficients are symmetric
  functions of the coordinates of `C ∖ {0}`, so if `C` is Galois-stable they are
  Galois-fixed. This is Vélu functoriality plus finite combinatorics; it is the only descent
  ingredient left open.
* `exists_pointsHom_surjective_ker_eq` (**proved** from the above): the points-level main
  theorem — for `C ⊆ E(kˢᵉᵖ)` finite and Galois-stable there is an elliptic `E'/k` and a
  surjective `φ : E(kˢᵉᵖ) →+ E'(kˢᵉᵖ)` with `ker φ = C`.

## Relation to the faithful statement
The endpoint remains `WeierstrassCurve.exists_quotient_by_finite_galoisStable_addSubgroup`
in `EllipticQuotient.lean`, which in addition demands the defining rational functions over
`k`. To reach it from this scaffold, the Vélu layer must additionally expose its coordinate
functions (they are rational functions over `K` by construction) and the descent layer must
descend them (their reduced numerators/denominators are Galois-fixed, hence over `k`); this
upgrade is deliberately not attempted here. A points-level `Isogeny` structure (as in earlier
drafts) is intentionally avoided: without the algebraic witness it under-specifies the
quotient — e.g. over a separably closed base every abstract group-theoretic section would
qualify — and with the witness it would duplicate the faithful statement.

Everything not `sorry`d below is proved; the `sorry`s are exactly: the Vélu data and its
three properties (5), and Galois-fixedness of the Vélu coefficients (1).
-/

@[expose] public section

open scoped WeierstrassCurve.Affine -- `(E⁄K).Point` notation for the group of `K`-points

namespace WeierstrassCurve

/-! ### Layer 1: Vélu's construction over an arbitrary field -/

section Velu

-- let K be a field (`DecidableEq` is needed for the group law on points)
variable {K : Type*} [Field K] [DecidableEq K]

/-- **Vélu's quotient curve** `E/C` for a finite subgroup `C ⊆ E(K)`. Writing `t Q`, `u Q` for
Vélu's quantities attached to each nonzero `Q ∈ C` and `t = Σ t Q`, `w = Σ (u Q + x Q * t Q)`
(sums over representatives of `(C ∖ {0})/±`), the curve is
`⟨a₁, a₂, a₃, a₄ - 5t, a₆ - (a₁² + 4a₂)t - 7w⟩`. (`sorry` leaf: construction.) -/
noncomputable def veluQuotient (E : WeierstrassCurve K)
    (C : AddSubgroup E.toAffine.Point) [Finite C] : WeierstrassCurve K := sorry

/-- **Vélu's isogeny** `E → E/C` on `K`-points: away from `C` it sends `(x, y)` to
`(x + Σ_Q (t Q/(x - x Q) + u Q/(x - x Q)²), …)`, and sends `C` to `0`. That this is a
homomorphism of groups is the deepest of the `sorry` leaves. -/
noncomputable def veluMap (E : WeierstrassCurve K)
    (C : AddSubgroup E.toAffine.Point) [Finite C] :
    E.toAffine.Point →+ (E.veluQuotient C).toAffine.Point := sorry

variable (E : WeierstrassCurve K) (C : AddSubgroup E.toAffine.Point) [Finite C]

/-- The Vélu quotient of an elliptic curve is elliptic (nonvanishing discriminant).
(`sorry` leaf.) -/
theorem isElliptic_veluQuotient [E.IsElliptic] : (E.veluQuotient C).IsElliptic := sorry

/-- The kernel of Vélu's isogeny is exactly `C`. (`sorry` leaf.) -/
theorem ker_veluMap [E.IsElliptic] : (E.veluMap C).ker = C := sorry

/-- Over a separably closed field, Vélu's isogeny is surjective on points: it is separable
(its kernel consists of honest points, so is étale) and separable isogenies are étale.
(`sorry` leaf.) -/
theorem surjective_veluMap [E.IsElliptic] [IsSepClosed K] :
    Function.Surjective (E.veluMap C) := sorry

/-- **First isomorphism theorem for the Vélu isogeny** over a separably closed field:
`E(K)/C ≃+ (E/C)(K)`. In particular the isogeny has degree `|C|`. Proved from the interface
above. -/
noncomputable def veluQuotientEquiv [E.IsElliptic] [IsSepClosed K] :
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

/-- The kernel of a Galois-equivariant homomorphism on `kˢᵉᵖ`-points is Galois-stable.
Fully proved. (In the faithful statement of `EllipticQuotient.lean`, equivariance itself is
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

/-- **Galois-fixedness of the Vélu quotient.** If `C ⊆ E(kˢᵉᵖ)` is Galois-stable then the
Vélu coefficients — symmetric functions of the coordinates of the points of `C ∖ {0}` — are
fixed by `Gal(kˢᵉᵖ/k)`. This is functoriality of Vélu's formulas in the base field together
with the stability hypothesis, and is the only descent ingredient left open. (`sorry`
leaf.) -/
theorem veluQuotient_map_eq_of_galoisStable (E : WeierstrassCurve k) [E.IsElliptic]
    (C : AddSubgroup (E⁄ksep).Point) [Finite C]
    (hC : ∀ σ : ksep ≃ₐ[k] ksep, ∀ P ∈ C, Affine.Point.map σ.toAlgHom P ∈ C)
    (σ : ksep ≃ₐ[k] ksep) :
    ((E⁄ksep).veluQuotient C).map (σ : ksep →+* ksep) = (E⁄ksep).veluQuotient C := sorry

/-- **Quotient of an elliptic curve by a finite Galois-stable subgroup, points-level form.**
If `C ⊆ E(kˢᵉᵖ)` is a finite Galois-stable subgroup, there are an elliptic curve `E'` over
`k` and a surjective homomorphism `φ : E(kˢᵉᵖ) →+ E'(kˢᵉᵖ)` with `ker φ = C`.

**Proved** from the Vélu interface and the descent lemmas above; the faithful version (with
the rational functions over `k` witnessing algebraicity of `φ`) is
`WeierstrassCurve.exists_quotient_by_finite_galoisStable_addSubgroup` in
`EllipticQuotient.lean`. -/
theorem exists_pointsHom_surjective_ker_eq (E : WeierstrassCurve k) [E.IsElliptic]
    (C : AddSubgroup (E⁄ksep).Point) [Finite C]
    (hC : ∀ σ : ksep ≃ₐ[k] ksep, ∀ P ∈ C, Affine.Point.map σ.toAlgHom P ∈ C) :
    ∃ (E' : WeierstrassCurve k) (_ : E'.IsElliptic)
      (φ : (E⁄ksep).Point →+ (E'⁄ksep).Point),
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
      Function.Surjective φ ∧ φ.ker = C :=
    ⟨(E⁄ksep).veluMap C, (E⁄ksep).surjective_veluMap C, (E⁄ksep).ker_veluMap C⟩
  rw [← hE'] at H
  exact ⟨E', hell, H⟩

end Descent

end WeierstrassCurve
