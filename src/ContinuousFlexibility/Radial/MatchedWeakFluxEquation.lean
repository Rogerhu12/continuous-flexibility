import ContinuousFlexibility.Analysis.IntervalWeakPrimitive
import ContinuousFlexibility.Radial.MatchedModeSeparatedTests
import ContinuousFlexibility.Radial.MatchingKernel

/-!
# The physical modal equation from the actual weak flux

The variation-of-parameters representative has a weak derivative for its
true flux. Integration by parts gives the second-order equation, and the
existing interval closure retains every test in the frozen modal graph.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open Set Filter MeasureTheory
open scoped Topology ContDiff
open ContinuousFlexibility.Statements ContinuousFlexibility.Analysis

theorem matchedWeakFlux_principal {a b : ℝ} (hab : a < b)
    {u w g : ℝ → ℝ} (hu : ContDiffOn ℝ 1 u (Ioo a b))
    (hw : ContDiff ℝ ∞ w)
    (hweak : HasIntervalWeakDerivative a b (fun x => w x * deriv u x) g)
    {ψ : ℝ → ℝ} (hψ : ContDiff ℝ ∞ ψ) (hcψ : HasCompactSupport ψ)
    (hsψ : tsupport ψ ⊆ Ioo a b) :
    (∫ x, u x * deriv (fun y => w y * deriv ψ y) x) = ∫ x, g x * ψ x := by
  obtain ⟨l, r, hal, hlr, hrb, hs⟩ := interval_compact_subset_Ioo hab hcψ hsψ
  let q : ℝ → ℝ := fun x => w x * deriv ψ x
  have hq : ContDiff ℝ ∞ q := hw.mul (contDiff_infty_iff_deriv.mp hψ).2
  have hqsub : tsupport q ⊆ tsupport ψ :=
    tsupport_mul_subset_right.trans tsupport_deriv_subset
  have hP : Function.support (fun x => u x * deriv q x) ⊆ Ioc l r := by
    intro x hx
    exact Ioo_subset_Ioc_self (hs (hqsub (support_deriv_subset
      ((mul_ne_zero_iff.mp hx).2))))
  have hF : Function.support (fun x => (w x * deriv u x) * deriv ψ x) ⊆ Ioc l r := by
    intro x hx
    exact Ioo_subset_Ioc_self (hs (support_deriv_subset ((mul_ne_zero_iff.mp hx).2)))
  have hG : Function.support (fun x => g x * ψ x) ⊆ Ioc l r := by
    intro x hx
    exact Ioo_subset_Ioc_self (hs ((subset_tsupport ψ) ((mul_ne_zero_iff.mp hx).2)))
  have huc : ContDiffOn ℝ 1 u (uIcc l r) := by
    rw [uIcc_of_le hlr.le]
    exact hu.mono (fun x hx => ⟨hal.trans_le hx.1, hx.2.trans_lt hrb⟩)
  have hqc : ContDiffOn ℝ 1 q (uIcc l r) := (hq.of_le (by simp)).contDiffOn
  have hql : q l = 0 := by
    dsimp only [q]
    rw [deriv_of_notMem_tsupport (fun h => (lt_irrefl l) (hs h).1), mul_zero]
  have hqr : q r = 0 := by
    dsimp only [q]
    rw [deriv_of_notMem_tsupport (fun h => (lt_irrefl r) (hs h).2), mul_zero]
  have hparts := huc.absolutelyContinuousOnInterval.integral_mul_deriv_eq_deriv_mul
    hqc.absolutelyContinuousOnInterval
  simp only [hql, hqr, mul_zero, sub_zero, zero_sub] at hparts
  have hflux : (∫ x in l..r, deriv u x * q x) =
      ∫ x in l..r, (w x * deriv u x) * deriv ψ x := by
    apply intervalIntegral.integral_congr
    intro x _
    dsimp only [q]
    ring
  rw [hflux] at hparts
  have he := hweak ψ hψ hcψ hsψ
  rw [← intervalIntegral.integral_eq_integral_of_support_subset hF,
    ← intervalIntegral.integral_eq_integral_of_support_subset hG] at he
  change (∫ x, u x * deriv q x) = ∫ x, g x * ψ x
  rw [← intervalIntegral.integral_eq_integral_of_support_subset hP,
    ← intervalIntegral.integral_eq_integral_of_support_subset hG]
  linarith only [hparts, he]

/-- A C¹ representative with the actual principal flux equation satisfies
the entire original modal test class on the interval. -/
theorem modeLocalEquation_of_weakFlux {D : ReferenceData}
    (hD : IsAccumulatingProfile D) (hB : RadialTrueBorder D)
    {j : ℕ} {U F : RadialModePair D} {a b : ℝ} (hab : a < b)
    (hcore : Ioo a b ⊆ radialCore D) {u : ℝ → ℝ}
    (hu : ContDiffOn ℝ 1 u (Ioo a b))
    (hrep : (U.1 : ℝ → ℝ) =ᵐ[(radialHilbertMeasure D).restrict (Ioo a b)] u)
    (hweak : HasIntervalWeakDerivative a b (fun x => D.w x * deriv u x)
      (matchingPrincipalSource D j U F)) :
    ModeLocalEquation D j (Ioo a b) U F := by
  apply modeLocalEquation_of_compactInterval hD hB hab
  intro ψ hψ hcψ hsψ
  obtain ⟨l, r, hal, hlr, hrb, hs⟩ := interval_compact_subset_Ioo hab hcψ hsψ
  have hsub : Icc l r ⊆ radialCore D :=
    fun x hx => hcore ⟨hal.trans_le hx.1, hx.2.trans_lt hrb⟩
  have hsubo : Ioo l r ⊆ radialCore D := Ioo_subset_Icc_self.trans hsub
  have hsubu : uIcc l r ⊆ Icc D.a D.b := by
    rw [uIcc_of_le hlr.le]
    exact hsub.trans Ioo_subset_Icc_self
  have hsprod (f : ℝ → ℝ) : Function.support (fun x => f x * ψ x) ⊆ Ioo l r :=
    fun x hx => hs ((subset_tsupport ψ) ((mul_ne_zero_iff.mp hx).2))
  have hsJ : Function.support (fun x => U.1 x *
      radialJacobi ((j : ℝ) ^ 2) D.w ψ x) ⊆ Ioo l r :=
    fun x hx => hs (matchingJacobi_support_subset hD hψ j ((mul_ne_zero_iff.mp hx).2))
  have hsP : Function.support (fun x => U.1 x *
      deriv (fun y => D.w y * deriv ψ y) x) ⊆ Ioo l r :=
    fun x hx => hs (matchingPrincipal_support_subset hD hψ ((mul_ne_zero_iff.mp hx).2))
  have hw : ContDiff ℝ ∞ D.w := (matchingProfileGeometry hD).2.2.1.1
  have hp := matchedWeakFlux_principal hab hu hw hweak hψ hcψ hsψ
  have hrepv := (matching_restrict_ae_iff hD measurableSet_Ioo hcore).mp hrep
  have hpair : (∫ x, U.1 x * deriv (fun y => D.w y * deriv ψ y) x) =
      ∫ x, u x * deriv (fun y => D.w y * deriv ψ y) x := by
    apply integral_congr_ae
    filter_upwards [ae_imp_of_ae_restrict hrepv] with x hx
    by_cases hxs : x ∈ tsupport ψ
    · rw [hx (hsψ hxs)]
    · have hz : deriv (fun y => D.w y * deriv ψ y) x = 0 :=
        Function.notMem_support.mp
          (fun h => hxs (matchingPrincipal_support_subset hD hψ h))
      rw [hz, mul_zero, mul_zero]
  have he := hpair.trans hp
  rw [← intervalIntegral.integral_eq_integral_of_support_subset
      (hsP.trans Ioo_subset_Ioc_self),
    ← intervalIntegral.integral_eq_integral_of_support_subset
      ((hsprod (matchingPrincipalSource D j U F)).trans Ioo_subset_Ioc_self)] at he
  rw [matchingInterval_eq_subinterval hsubo hsJ,
    matchingInterval_eq_subinterval hsubo (hsprod (referenceColumn D)),
    matchingInterval_eq_subinterval hsubo
      (hsprod (fun x => matchingDensity D x * F.1 x))]
  have hUi := matchingMode_intervalIntegrable hD U.1 hlr.le hsub
  have hFi := matchingMode_intervalIntegrable hD F.1 hlr.le hsub
  have hdψ : ContDiff ℝ ∞ (deriv ψ) := (contDiff_infty_iff_deriv.mp hψ).2
  have hpc : Continuous (deriv (fun x => D.w x * deriv ψ x)) :=
    ((contDiff_infty_iff_deriv.mp (hw.mul hdψ)).2).continuous
  have hiP := hUi.mul_continuousOn hpc.continuousOn
  have hiq := (hUi.continuousOn_mul
    ((matchingPotential_continuousOn hD j).mono hsubu)).mul_continuousOn
      hψ.continuous.continuousOn
  have hic : IntervalIntegrable (fun x => referenceColumn D x * ψ x) volume l r :=
    (((matchingColumn_continuousOn hD hB).mono hsubu).mul
      hψ.continuous.continuousOn).intervalIntegrable
  have hiρ := (hFi.continuousOn_mul
    ((matchingDensity_continuousOn hD).mono hsubu)).mul_continuousOn
      hψ.continuous.continuousOn
  have hsource : (fun x => matchingPrincipalSource D j U F x * ψ x) =
      fun x => (matchingPotential D j x * U.1 x) * ψ x +
        U.2 * (referenceColumn D x * ψ x) - matchingDensity D x * F.1 x * ψ x := by
    funext x
    dsimp only [matchingPrincipalSource]
    ring
  rw [hsource, intervalIntegral.integral_sub (hiq.add (hic.const_mul U.2)) hiρ,
    intervalIntegral.integral_add hiq (hic.const_mul U.2),
    intervalIntegral.integral_const_mul] at he
  have hJacobi : (fun x => U.1 x * radialJacobi ((j : ℝ) ^ 2) D.w ψ x) =
      fun x => U.1 x * deriv (fun y => D.w y * deriv ψ y) x -
        (matchingPotential D j x * U.1 x) * ψ x := by
    funext x
    dsimp only [radialJacobi, matchingPotential]
    ring
  rw [hJacobi, intervalIntegral.integral_sub hiP hiq]
  linarith only [he]

end ContinuousFlexibility.Radial
