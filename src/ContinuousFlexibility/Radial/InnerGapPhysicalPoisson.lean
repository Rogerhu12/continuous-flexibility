module

public import ContinuousFlexibility.Radial.InnerGapPoissonDomain
public import ContinuousFlexibility.Radial.InnerGapPhysicalWeak
public import ContinuousFlexibility.Radial.InnerGapWeakFlux

/-!
# Actual positive-gap Poisson equations and canonical weak flux

The Poisson pair satisfies the homogeneous physical equation against
every test in the common H¹ zero-endpoint domain. The full outward
matrix is then the weak flux computed using the fixed affine hats:
Poisson columns and affine hats differ by actual zero-endpoint tests.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Radial

open Set MeasureTheory Filter ContinuousFlexibility.Statements
open scoped ContDiff InnerProductSpace

theorem innerGapEnergyPair_eq_physicalPair (D : ReferenceData)
    (hw : ContDiff ℝ ∞ D.w) {a b : ℝ} (ha : 0 < a)
    (hcore : Ioo a b ⊆ radialCore D) (hpos : ∀ r ∈ Icc a b, 0 < D.w r)
    (j : ℝ) (φ : ℝ → ℝ) (hφ : ContDiff ℝ ∞ φ) (u d : RadialModeL2 D)
    (hu : (u : ℝ → ℝ) =ᵐ[radialHilbertMeasure D] (Ioo a b).indicator φ)
    (hd : (d : ℝ → ℝ) =ᵐ[radialHilbertMeasure D]
      (Ioo a b).indicator (innerGapGradientField φ)) :
    innerGapEnergyPair D hw ha hcore hpos j φ hφ =
      WithLp.toLp 2 (d, innerGapPotentialMultiplier D hw hpos j u) := by
  apply (WithLp.prodContinuousLinearEquiv 2 ℝ (RadialModeL2 D) (RadialModeL2 D)).injective
  apply Prod.ext
  · simp only [WithLp.prodContinuousLinearEquiv_apply, WithLp.ofLp_fst, WithLp.toLp_fst]
    exact Lp.ext ((innerGapEnergyPair_fst_ae D hw ha hcore hpos j φ hφ).trans hd.symm)
  · simp only [WithLp.prodContinuousLinearEquiv_apply, WithLp.ofLp_snd, WithLp.toLp_snd]
    apply Lp.ext
    filter_upwards [innerGapEnergyPair_snd_ae D hw ha hcore hpos j φ hφ,
      innerGapPotentialMultiplier_ae D hw hpos j u, hu] with r hE hM hU
    rw [hE, hM, hU]
    by_cases hr : r ∈ Ioo a b
    · simp only [indicator_of_mem hr, innerGapPotentialField, innerGapPotentialWeight]
    · simp only [indicator_of_notMem hr, innerGapPotentialWeight, mul_zero]

theorem innerGapPoissonH1_energy (D : ReferenceData) (hw : ContDiff ℝ ∞ D.w)
    {a b : ℝ} (ha : 0 < a) (hcore : Ioo a b ⊆ radialCore D)
    (hpos : ∀ r ∈ Icc a b, 0 < D.w r) (j : ℝ)
    (p : Fin 2 → ℝ → ℝ) (hp : ∀ i, ContDiff ℝ ∞ (p i))
    (ξ : EuclideanSpace ℝ (Fin 2)) :
    innerGapEnergyPair D hw ha hcore hpos j (innerGapPoisson p ξ)
        (innerGapPoisson_contDiff p hp ξ) =
      WithLp.toLp 2
        ((innerGapPoissonH1 D hw.continuous ha hcore hpos p hp ξ).2,
         innerGapPotentialMultiplier D hw hpos j
           (innerGapPoissonH1 D hw.continuous ha hcore hpos p hp ξ).1) :=
  innerGapEnergyPair_eq_physicalPair D hw ha hcore hpos j _ _ _ _
    (innerGapPoissonH1_value_ae D hw.continuous ha hcore hpos p hp ξ)
    (innerGapPoissonH1_gradient_ae D hw.continuous ha hcore hpos p hp ξ)

theorem innerGapPoissonH1Unit_energy (D : ReferenceData) (hw : ContDiff ℝ ∞ D.w)
    {a b : ℝ} (ha : 0 < a) (hcore : Ioo a b ⊆ radialCore D)
    (hpos : ∀ r ∈ Icc a b, 0 < D.w r) (j : ℝ)
    (p : Fin 2 → ℝ → ℝ) (hp : ∀ i, ContDiff ℝ ∞ (p i)) (i : Fin 2) :
    innerGapEnergyPair D hw ha hcore hpos j (p i) (hp i) =
      WithLp.toLp 2
        ((innerGapPoissonH1Unit D hw.continuous ha hcore hpos p hp i).2,
         innerGapPotentialMultiplier D hw hpos j
           (innerGapPoissonH1Unit D hw.continuous ha hcore hpos p hp i).1) :=
  innerGapEnergyPair_eq_physicalPair D hw ha hcore hpos j _ _ _ _
    (innerGapPoissonH1Unit_value_ae D hw.continuous ha hcore hpos p hp i)
    (innerGapPoissonH1Unit_gradient_ae D hw.continuous ha hcore hpos p hp i)

theorem innerGapFormSpace_homogeneous_orthogonal (D : ReferenceData)
    (hw : ContDiff ℝ ∞ D.w) {a b j : ℝ} (hab : a ≤ b) (ha : 0 < a)
    (hcore : Ioo a b ⊆ radialCore D) (hpos : ∀ r ∈ Icc a b, 0 < D.w r)
    (hslope : ∀ r ∈ Icc a b, 0 ≤ r * deriv D.w r / D.w r)
    (φ : ℝ → ℝ) (hφ : ContDiff ℝ ∞ φ)
    (heq : ∀ r ∈ Icc a b, radialJacobi (j ^ 2) D.w φ r = 0)
    (q : InnerGapEnergyTriple D) (hq : q ∈ innerGapFormSpace D j a b) :
    ⟪q.snd, innerGapEnergyPair D hw ha hcore hpos j φ hφ⟫_ℝ = 0 := by
  have he := innerGapFormSpace_green_test D hw hab ha hcore hpos hslope j φ hφ q hq
  have hz : innerRadialIntervalToLp D hw.continuous ha hcore
      (fun r hr => (hpos r (Ioo_subset_Icc_self hr)).le) (innerGapTestSource D.w j φ)
      (innerGapTestSource_continuousOn ha hw hφ hpos j) = 0 := by
    apply Lp.eq_zero_iff_ae_eq_zero.mpr
    filter_upwards [innerRadialIntervalToLp_ae D hw.continuous ha hcore
      (fun r hr => (hpos r (Ioo_subset_Icc_self hr)).le) (innerGapTestSource D.w j φ)
      (innerGapTestSource_continuousOn ha hw hφ hpos j)] with r hr
    rw [hr]
    by_cases hmem : r ∈ Ioo a b
    · simp only [indicator_of_mem hmem, innerGapTestSource,
        heq r (Ioo_subset_Icc_self hmem), mul_zero, Pi.zero_apply]
    · simp only [indicator_of_notMem hmem, Pi.zero_apply]
  simpa only [hz, inner_zero_right] using he

/-- The actual Poisson field satisfies the common physical weak
equation for every closed-domain test. -/
theorem innerGapPoissonH1_weakResidual (D : ReferenceData)
    (hw : ContDiff ℝ ∞ D.w) {a b j : ℝ} (hab : a ≤ b) (ha : 0 < a)
    (hcore : Ioo a b ⊆ radialCore D) (hpos : ∀ r ∈ Icc a b, 0 < D.w r)
    (hslope : ∀ r ∈ Icc a b, 0 ≤ r * deriv D.w r / D.w r)
    (p : Fin 2 → ℝ → ℝ) (hp : ∀ i, ContDiff ℝ ∞ (p i))
    (heq : ∀ i r, r ∈ Icc a b → radialJacobi (j ^ 2) D.w (p i) r = 0)
    (ξ : EuclideanSpace ℝ (Fin 2)) (r : InnerRadialH1Pair D)
    (hr : r ∈ innerRadialH1Zero D a b) :
    innerRadialWeakResidual D
      (innerGapPoissonH1 D hw.continuous ha hcore hpos p hp ξ)
      (innerGapPotentialMultiplier D hw hpos j
        (innerGapPotentialMultiplier D hw hpos j
          (innerGapPoissonH1 D hw.continuous ha hcore hpos p hp ξ).1)) 0 0 0 r = 0 := by
  let M := innerGapPotentialMultiplier D hw hpos j
  let P := innerGapPoissonH1 D hw.continuous ha hcore hpos p hp ξ
  have he := innerGapFormSpace_homogeneous_orthogonal D hw hab ha hcore hpos hslope
    (innerGapPoisson p ξ) (innerGapPoisson_contDiff p hp ξ)
    (innerGapPoisson_homogeneous hw p hp heq ξ)
    (innerGapPotentialLift D M r) (innerGapPotentialLift_mem D hw hpos j r hr)
  rw [innerGapPoissonH1_energy] at he
  have hzero : ⟪r.2, P.2⟫_ℝ + ⟪M r.1, M P.1⟫_ℝ = 0 := by
    simpa only [innerGapPotentialLift_apply, WithLp.toLp_snd, WithLp.prod_inner_apply,
      WithLp.ofLp_fst, WithLp.ofLp_snd, WithLp.toLp_fst] using he
  rw [innerRadialWeakResidual_apply, innerGapPotentialMultiplier_square_inner]
  simp only [zero_mul, add_zero, inner_zero_left, sub_zero]
  exact (congrArg₂ (· + ·) (real_inner_comm P.2 r.2)
    (real_inner_comm (M P.1) (M r.1))).symm.trans hzero

/-- The physical residual on a Poisson test is exactly the previously
constructed weak outgoing conormal coordinate. -/
theorem innerGapWeakResidual_poissonUnit (D : ReferenceData)
    (hw : ContDiff ℝ ∞ D.w) {a b : ℝ} (ha : 0 < a)
    (hcore : Ioo a b ⊆ radialCore D) (hpos : ∀ r ∈ Icc a b, 0 < D.w r)
    (j : ℝ) (p : Fin 2 → ℝ → ℝ) (hp : ∀ i, ContDiff ℝ ∞ (p i))
    (q : InnerGapEnergyTriple D)
    (hpotential : q.snd.snd = innerGapPotentialMultiplier D hw hpos j q.fst)
    (F : RadialModeL2 D) (i : Fin 2) :
    innerRadialWeakResidual D (q.fst, q.snd.fst)
      (innerGapPotentialMultiplier D hw hpos j
        (innerGapPotentialMultiplier D hw hpos j q.fst)) F 0 0
      (innerGapPoissonH1Unit D hw.continuous ha hcore hpos p hp i) =
        innerGapWeakFlux D hw ha hcore hpos j p hp q F i := by
  rw [innerGapWeakFlux_apply, innerGapPoissonH1Unit_energy]
  simp only [innerRadialWeakResidual_apply, zero_mul, add_zero, WithLp.prod_inner_apply,
    WithLp.ofLp_fst, WithLp.ofLp_snd, WithLp.toLp_fst, WithLp.toLp_snd,
    hpotential, innerGapPotentialMultiplier_square_inner, innerGapPoissonH1Unit]

/-- Fixed affine hats compute the same conormal flux. Their difference
from the actual Poisson tests belongs to the actual zero-endpoint
domain, so this equality follows from the local physical equation. -/
theorem innerGapWeakResidual_affineUnit (D : ReferenceData)
    (hw : ContDiff ℝ ∞ D.w) {a b : ℝ} (hab : a < b) (ha : 0 < a)
    (hcore : Ioo a b ⊆ radialCore D) (hpos : ∀ r ∈ Icc a b, 0 < D.w r)
    (j : ℝ) (p : Fin 2 → ℝ → ℝ) (hp : ∀ i, ContDiff ℝ ∞ (p i))
    (hb : ∀ i k, p k (innerGapEndpoint a b i) = if k = i then 1 else 0)
    (q : InnerGapEnergyTriple D)
    (hpotential : q.snd.snd = innerGapPotentialMultiplier D hw hpos j q.fst)
    (F : RadialModeL2 D)
    (hweak : ∀ r ∈ innerRadialH1Zero D a b,
      innerRadialWeakResidual D (q.fst, q.snd.fst)
        (innerGapPotentialMultiplier D hw hpos j
          (innerGapPotentialMultiplier D hw hpos j q.fst)) F 0 0 r = 0)
    (i : Fin 2) :
    innerRadialWeakResidual D (q.fst, q.snd.fst)
      (innerGapPotentialMultiplier D hw hpos j
        (innerGapPotentialMultiplier D hw hpos j q.fst)) F 0 0
      (innerRadialAffineUnitPair D hw.continuous ha hcore hpos i) =
        innerGapWeakFlux D hw ha hcore hpos j p hp q F i := by
  have hdiff := hweak
    (innerGapPoissonH1Unit D hw.continuous ha hcore hpos p hp i -
      innerRadialAffineUnitPair D hw.continuous ha hcore hpos i)
    (innerGapPoissonH1Unit_sub_affine D hw.continuous ha hcore hpos p hp hab hb i)
  rw [map_sub] at hdiff
  exact (sub_eq_zero.mp hdiff).symm.trans
    (innerGapWeakResidual_poissonUnit D hw ha hcore hpos j p hp q hpotential F i)

end ContinuousFlexibility.Radial
