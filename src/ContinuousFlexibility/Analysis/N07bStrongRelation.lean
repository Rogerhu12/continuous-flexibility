import ContinuousFlexibility.Analysis.N07bInteriorGreen

/-!
# Strong physical solutions satisfy the canonical weak relation

The coefficients are assumed smooth only in the open physical annulus,
with their actual angular periodicity stated separately. These hypotheses
are not claimed to be fields of N03.

For the scalar inverse the compatibility scalar is zero. The remaining
column needs no separate regularity hypothesis: after multiplication by a
test, the strong equation expresses its scalar multiple as a difference
of two integrable smooth products. This remains valid when that scalar
vanishes.

This module uses the full-period version of PerturbedCanonicalRelation.
It identifies the physical weak equation; it does not assert membership
in the fixed reference graph.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set MeasureTheory
open ContinuousFlexibility.Statements
open scoped ContDiff

/-- A real scalar commutes with the iterated physical pairing. This
identity is valid for arbitrary functions, including the zero scalar. -/
theorem n07b_integral_radialAngularMean_const_mul (D : ReferenceData)
    (c : ℝ) (f : PolarPoint → ℝ) :
    (∫ r in D.a..D.b, radialAngularMean (fun θ => c * f (r, θ))) =
      c * ∫ r in D.a..D.b, radialAngularMean (fun θ => f (r, θ)) := by
  calc
    _ = ∫ r in D.a..D.b, c * radialAngularMean (fun θ => f (r, θ)) := by
      apply intervalIntegral.integral_congr
      intro r _
      change (2 * Real.pi)⁻¹ * (∫ θ in (0 : ℝ)..2 * Real.pi, c * f (r, θ)) =
        c * ((2 * Real.pi)⁻¹ * ∫ θ in (0 : ℝ)..2 * Real.pi, f (r, θ))
      rw [intervalIntegral.integral_const_mul]
      ring
    _ = _ := intervalIntegral.integral_const_mul c _

/-- The strong scalar equation gives the actual full-period weak equation.
No regularity of the unmultiplied column is needed. -/
theorem n07b_strong_physical_pairing_of_pi_periodic
    {D : ReferenceData} (hab : D.a < D.b)
    {L : SymmetricCoefficients} {u f q : PolarPoint → ℝ} {μ : ℝ}
    (ha : ContDiffOn ℝ ∞ L.a (annularOpen D))
    (hb : ContDiffOn ℝ ∞ L.b (annularOpen D))
    (hc : ContDiffOn ℝ ∞ L.c (annularOpen D))
    (hu : ContDiff ℝ ∞ u)
    (hf : ContDiffOn ℝ ∞ f (annularOpen D))
    (hBp : ∀ r ∈ radialCore D, Function.Periodic (fun θ => L.b (r, θ)) Real.pi)
    (hCp : ∀ r ∈ radialCore D, Function.Periodic (fun θ => L.c (r, θ)) Real.pi)
    (hup : Function.Periodic u (0, Real.pi))
    (hstrong : ∀ p ∈ annularOpen D,
      divergenceOperator L u p + μ * q p = f p)
    {φ : PolarPoint → ℝ} (hφ : RadialTest D φ) :
    (∫ r in D.a..D.b, radialAngularMean (fun θ =>
      u (r, θ) * divergenceOperator L φ (r, θ))) +
      μ * (∫ r in D.a..D.b, radialAngularMean (fun θ => q (r, θ) * φ (r, θ))) =
        ∫ r in D.a..D.b, radialAngularMean (fun θ => f (r, θ) * φ (r, θ)) := by
  have hopen : IsOpen (annularOpen D) := isOpen_Ioo.prod isOpen_univ
  have hs := n07b_radialTest_tsupport_subset hφ
  have hDu : ContDiffOn ℝ ∞ (divergenceOperator L u) (annularOpen D) :=
    n07b_contDiffOn_divergenceOperator hopen ha hb hc hu.contDiffOn
  let A : PolarPoint → ℝ := fun p => f p * φ p
  let B : PolarPoint → ℝ := fun p => divergenceOperator L u p * φ p
  let Q : PolarPoint → ℝ := fun p => q p * φ p
  have hA : Continuous A :=
    (n07b_contDiff_mul_of_tsupport_subset hopen hf hφ.1 hs).continuous
  have hB : Continuous B :=
    (n07b_contDiff_mul_of_tsupport_subset hopen hDu hφ.1 hs).continuous
  have heq : (fun p => μ * Q p) = (fun p => A p - B p) := by
    funext p
    by_cases hp : p ∈ annularOpen D
    · dsimp only [A, B, Q]
      rw [← hstrong p hp]
      ring
    · have hzero : φ p = 0 :=
        image_eq_zero_of_notMem_tsupport (fun h => hp (hs h))
      simp only [A, B, Q, hzero, mul_zero, sub_self]
  have hcolumn :
      μ * (∫ r in D.a..D.b, radialAngularMean (fun θ => Q (r, θ))) =
        (∫ r in D.a..D.b, radialAngularMean (fun θ => A (r, θ))) -
          ∫ r in D.a..D.b, radialAngularMean (fun θ => B (r, θ)) := by
    calc
      _ = ∫ r in D.a..D.b, radialAngularMean (fun θ => μ * Q (r, θ)) :=
        (n07b_integral_radialAngularMean_const_mul D μ Q).symm
      _ = ∫ r in D.a..D.b, radialAngularMean (fun θ => A (r, θ) - B (r, θ)) := by
        apply intervalIntegral.integral_congr
        intro r _
        apply congrArg radialAngularMean
        funext θ
        exact congrFun heq (r, θ)
      _ = _ := n07b_integral_radialAngularMean_sub D hA hB
  have hgreen := n07b_interior_physical_green_of_pi_periodic
    hab ha hb hc hu hBp hCp hup hφ
  dsimp only [A, B, Q] at hcolumn
  rw [hgreen]
  linarith

/-- A represented, normalized strong solution with zero compatibility
scalar satisfies the repaired perturbed canonical relation. The source
and unknown here are the actual physical representatives. -/
theorem n07b_perturbedCanonicalRelation_of_strong
    {D : ReferenceData} {S : PhysicalSpacesData} {C : NonlinearGeometryData S}
    {K : CanonicalData S} {L : ReturnCorrectionData S}
    {z : AnnularState S × ℝ} {U : CanonicalUnknown S K}
    {F : CanonicalSequence S K} {η f : PolarPoint → ℝ}
    (hab : D.a < D.b)
    (ha : ContDiffOn ℝ ∞ (L.coefficients z).a (annularOpen D))
    (hb : ContDiffOn ℝ ∞ (L.coefficients z).b (annularOpen D))
    (hc : ContDiffOn ℝ ∞ (L.coefficients z).c (annularOpen D))
    (hη : ContDiff ℝ ∞ η)
    (hf : ContDiffOn ℝ ∞ f (annularOpen D))
    (hBp : ∀ r ∈ radialCore D,
      Function.Periodic (fun θ => (L.coefficients z).b (r, θ)) Real.pi)
    (hCp : ∀ r ∈ radialCore D,
      Function.Periodic (fun θ => (L.coefficients z).c (r, θ)) Real.pi)
    (hηp : Function.Periodic η (0, Real.pi))
    (hfp : Function.Periodic f (0, Real.pi))
    (hrep : HasCanonicalRepresentation D S C K z U F η f)
    (hrow : referenceRow D η = 0) (hcompat : U.2.2.2 = 0)
    (hstrong : ∀ p ∈ annularOpen D,
      divergenceOperator (L.coefficients z) η p +
        U.2.2.1 * nuColumnField D S C z p = f p) :
    PerturbedCanonicalRelation D S C K L z U F := by
  refine ⟨η, f, hrep, hηp, hfp, hrow, ?_⟩
  intro φ hφ
  change (∫ r in D.a..D.b, radialAngularMean (fun θ =>
      η (r, θ) * divergenceOperator (L.coefficients z) φ (r, θ))) +
    U.2.2.1 * (∫ r in D.a..D.b, radialAngularMean (fun θ =>
      nuColumnField D S C z (r, θ) * φ (r, θ))) +
    U.2.2.2 * (∫ r in D.a..D.b, radialAngularMean (fun θ =>
      (S.height (3 / 4 : ℝ)).decode S.psi (r, θ) * φ (r, θ))) =
    ∫ r in D.a..D.b, radialAngularMean (fun θ => f (r, θ) * φ (r, θ))
  rw [hcompat, zero_mul, add_zero]
  exact n07b_strong_physical_pairing_of_pi_periodic
    hab ha hb hc hη hf hBp hCp hηp hstrong hφ

end ContinuousFlexibility.Analysis
