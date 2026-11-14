module

public import ContinuousFlexibility.Radial.ModeTestIntegrability
public import Mathlib.MeasureTheory.Function.LocallyIntegrable

/-!
# Ordinary local integrability of modal weak solutions

On every compact subinterval of the radial core the positive Hilbert
density has a continuous reciprocal. Thus modal L² functions and the
right hand side of the principal divergence equation are locally L¹
with respect to ordinary Lebesgue measure.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Radial

open Set Filter MeasureTheory
open scoped Topology ContDiff RealInnerProductSpace InnerProductSpace
open ContinuousFlexibility.Statements

theorem matchingMode_integrableOn_compact {D : ReferenceData}
    (hD : IsAccumulatingProfile D) (U : RadialModeL2 D)
    {K : Set ℝ} (hK : IsCompact K) (hsub : K ⊆ radialCore D) :
    IntegrableOn (fun r => U r) K volume := by
  letI : IsFiniteMeasure (radialHilbertMeasure D) := radialHilbertMeasure_isFinite hD
  have hU : Integrable (fun r => U r) (radialHilbertMeasure D) :=
    MemLp.integrable (by norm_num) (Lp.memLp U)
  have hiCore : IntegrableOn (fun r => matchingDensity D r * U r) (radialCore D) volume :=
    (matchingDensity_integrable_iff hD _).mp hU
  have hi : IntegrableOn (fun r => matchingDensity D r * U r) K volume :=
    hiCore.mono_set hsub
  have hc : ContinuousOn (fun r => (matchingDensity D r)⁻¹) K := by
    apply ((matchingDensity_continuousOn hD).mono
      (hsub.trans Ioo_subset_Icc_self)).inv₀
    intro r hr
    exact (matchingDensity_pos hD (hsub hr)).ne'
  apply (hi.mul_continuousOn hc hK).congr
  filter_upwards [ae_restrict_mem hK.measurableSet] with r hr
  have hn := (matchingDensity_pos hD (hsub hr)).ne'
  field_simp [hn]
  <;> ring

theorem matchingMode_intervalIntegrable {D : ReferenceData}
    (hD : IsAccumulatingProfile D) (U : RadialModeL2 D) {l h : ℝ}
    (hlh : l ≤ h) (hsub : Icc l h ⊆ radialCore D) :
    IntervalIntegrable (fun r => U r) volume l h :=
  (intervalIntegrable_iff_integrableOn_Icc_of_le hlh).mpr
    (matchingMode_integrableOn_compact hD U isCompact_Icc hsub)

theorem matchingColumn_continuousOn {D : ReferenceData}
    (hD : IsAccumulatingProfile D) (hB : RadialTrueBorder D) :
    ContinuousOn (referenceColumn D) (Icc D.a D.b) := by
  have hg := matchingProfileGeometry hD
  have hw : ContDiff ℝ ∞ D.w := hg.2.2.1.1
  have hφ : ContDiff ℝ ∞ D.phi := hg.2.2.2.1.1
  have hwχ : ContDiff ℝ ∞ (fun r => D.w r * D.chi r) := hw.mul hB.1
  have hdφ : ContDiff ℝ ∞ (deriv D.phi) := (contDiff_infty_iff_deriv.mp hφ).2
  have hdwχ : ContDiff ℝ ∞ (deriv (fun r => D.w r * D.chi r)) :=
    (contDiff_infty_iff_deriv.mp hwχ).2
  have hp : ContDiff ℝ ∞
      (deriv (fun r => (D.w r * D.chi r) * deriv D.phi r)) :=
    (contDiff_infty_iff_deriv.mp (hwχ.mul hdφ)).2
  change ContinuousOn
    (fun r => deriv (fun t => (D.w t * D.chi t) * deriv D.phi t) r -
      4 * deriv (fun t => D.w t * D.chi t) r / r * D.phi r)
    (Icc D.a D.b)
  apply hp.continuous.continuousOn.sub
  apply ContinuousOn.mul _ hφ.continuous.continuousOn
  apply (continuous_const.mul hdwχ.continuous).continuousOn.div
    continuous_id.continuousOn
  intro r hr
  exact ne_of_gt (lt_of_lt_of_le hg.1 hr.1)

theorem matchingColumn_intervalIntegrable {D : ReferenceData}
    (hD : IsAccumulatingProfile D) (hB : RadialTrueBorder D)
    {ψ : ℝ → ℝ} (hψ : Continuous ψ) :
    IntervalIntegrable (fun r => referenceColumn D r * ψ r) volume D.a D.b :=
  ((matchingColumn_continuousOn hD hB).mul hψ.continuousOn).intervalIntegrable_of_Icc
    (matchingProfileGeometry hD).2.1.le

def matchingPotential (D : ReferenceData) (j : ℕ) (r : ℝ) : ℝ :=
  (j : ℝ) ^ 2 * deriv D.w r / r

theorem matchingPotential_continuousOn {D : ReferenceData}
    (hD : IsAccumulatingProfile D) (j : ℕ) :
    ContinuousOn (matchingPotential D j) (Icc D.a D.b) := by
  have hg := matchingProfileGeometry hD
  have hdw : ContDiff ℝ ∞ (deriv D.w) :=
    (contDiff_infty_iff_deriv.mp hg.2.2.1.1).2
  apply (continuous_const.mul hdw.continuous).continuousOn.div
    continuous_id.continuousOn
  intro r hr
  exact ne_of_gt (lt_of_lt_of_le hg.1 hr.1)

/-- The ordinary source in the divergence equation `(w u')' = g`. -/
def matchingPrincipalSource (D : ReferenceData) (j : ℕ)
    (U F : RadialModePair D) (r : ℝ) : ℝ :=
  matchingPotential D j r * U.1 r +
    U.2 * referenceColumn D r - matchingDensity D r * F.1 r

theorem matchingPrincipalSource_integrableOn_compact {D : ReferenceData}
    (hD : IsAccumulatingProfile D) (hB : RadialTrueBorder D)
    (j : ℕ) (U F : RadialModePair D) {K : Set ℝ}
    (hK : IsCompact K) (hsub : K ⊆ radialCore D) :
    IntegrableOn (matchingPrincipalSource D j U F) K volume := by
  have hsub' := hsub.trans Ioo_subset_Icc_self
  have hu := matchingMode_integrableOn_compact hD U.1 hK hsub
  have hf := matchingMode_integrableOn_compact hD F.1 hK hsub
  have hq := hu.continuousOn_mul ((matchingPotential_continuousOn hD j).mono hsub') hK
  have hc0 : IntegrableOn (referenceColumn D) K volume :=
    ((matchingColumn_continuousOn hD hB).mono hsub').integrableOn_compact hK
  have hc := hc0.const_mul U.2
  have hρ := hf.continuousOn_mul ((matchingDensity_continuousOn hD).mono hsub') hK
  exact (hq.add hc).sub hρ

theorem matchingPrincipalSource_intervalIntegrable {D : ReferenceData}
    (hD : IsAccumulatingProfile D) (hB : RadialTrueBorder D)
    (j : ℕ) (U F : RadialModePair D) {l h : ℝ}
    (hlh : l ≤ h) (hsub : Icc l h ⊆ radialCore D) :
    IntervalIntegrable (matchingPrincipalSource D j U F) volume l h :=
  (intervalIntegrable_iff_integrableOn_Icc_of_le hlh).mpr
    (matchingPrincipalSource_integrableOn_compact hD hB j U F isCompact_Icc hsub)

/-- Support localization does not require integrability hypotheses. -/
theorem matchingInterval_eq_subinterval {D : ReferenceData} {l h : ℝ}
    {f : ℝ → ℝ} (hsub : Ioo l h ⊆ radialCore D)
    (hs : Function.support f ⊆ Ioo l h) :
    (∫ r in D.a..D.b, f r) = ∫ r in l..h, f r := by
  rw [intervalIntegral.integral_eq_integral_of_support_subset
      (hs.trans (hsub.trans Ioo_subset_Ioc_self)),
    intervalIntegral.integral_eq_integral_of_support_subset
      (hs.trans Ioo_subset_Ioc_self)]

theorem matchingJacobi_support_subset {D : ReferenceData} (hD : IsAccumulatingProfile D)
    {ψ : ℝ → ℝ} (hψ : ContDiff ℝ ∞ ψ) (j : ℕ) :
    Function.support (radialJacobi ((j : ℝ) ^ 2) D.w ψ) ⊆ tsupport ψ := by
  intro r hr
  by_contra h
  have h₀ : ψ r = 0 := image_eq_zero_of_notMem_tsupport h
  have h₁ : deriv ψ r = 0 := deriv_of_notMem_tsupport h
  have h₂ : deriv (deriv ψ) r = 0 :=
    deriv_of_notMem_tsupport (fun hh => h (tsupport_deriv_subset hh))
  exact hr (by rw [matchingJacobi_expansion hD hψ, h₀, h₁, h₂]; ring)

theorem matchingPrincipal_support_subset {D : ReferenceData} (hD : IsAccumulatingProfile D)
    {ψ : ℝ → ℝ} (hψ : ContDiff ℝ ∞ ψ) :
    Function.support (deriv (fun r => D.w r * deriv ψ r)) ⊆ tsupport ψ := by
  intro r hr
  by_contra h
  have hw : ContDiff ℝ ∞ D.w := (matchingProfileGeometry hD).2.2.1.1
  have hdψ : ContDiff ℝ ∞ (deriv ψ) := (contDiff_infty_iff_deriv.mp hψ).2
  have h₁ : deriv ψ r = 0 := deriv_of_notMem_tsupport h
  have h₂ : deriv (deriv ψ) r = 0 :=
    deriv_of_notMem_tsupport (fun hh => h (tsupport_deriv_subset hh))
  exact hr (by
    rw [deriv_fun_mul (hw.differentiable (by simp) r) (hdψ.differentiable (by simp) r),
      h₁, h₂]
    ring)

/-- The frozen radial equation gives the ordinary distributional principal
equation on every compact subinterval. This is the input for local weak
ODE regularity. -/
theorem modeLocalEquation_principal_on_compact {D : ReferenceData}
    (hD : IsAccumulatingProfile D) (hB : RadialTrueBorder D)
    {j : ℕ} {J : Set ℝ} {U F : RadialModePair D}
    (hEq : ModeLocalEquation D j J U F) {l h : ℝ}
    (hlh : l ≤ h) (hsub : Icc l h ⊆ radialCore D) (hJ : Ioo l h ⊆ J)
    {ψ : ℝ → ℝ} (hψ : ContDiff ℝ ∞ ψ) (hc : HasCompactSupport ψ)
    (hs : tsupport ψ ⊆ Ioo l h) :
    (∫ r in l..h, U.1 r * deriv (fun t => D.w t * deriv ψ t) r) =
      ∫ r in l..h, matchingPrincipalSource D j U F r * ψ r := by
  have hsubo : Ioo l h ⊆ radialCore D := Ioo_subset_Icc_self.trans hsub
  have hψs : Function.support ψ ⊆ Ioo l h :=
    (show Function.support ψ ⊆ tsupport ψ from subset_closure).trans hs
  have hsψ (f : ℝ → ℝ) :
      Function.support (fun r => f r * ψ r) ⊆ Ioo l h := by
    intro r hr
    exact hψs ((mul_ne_zero_iff.mp hr).2)
  have hsL :
      Function.support (fun r => U.1 r * radialJacobi ((j : ℝ) ^ 2) D.w ψ r) ⊆
        Ioo l h := by
    intro r hr
    exact hs (matchingJacobi_support_subset hD hψ j ((mul_ne_zero_iff.mp hr).2))
  have he := hEq ψ hψ hc (hψs.trans hJ)
  change (∫ r in D.a..D.b, U.1 r * radialJacobi ((j : ℝ) ^ 2) D.w ψ r) -
    U.2 * (∫ r in D.a..D.b, referenceColumn D r * ψ r) =
    -(∫ r in D.a..D.b, matchingDensity D r * F.1 r * ψ r) at he
  rw [matchingInterval_eq_subinterval hsubo hsL,
    matchingInterval_eq_subinterval hsubo (hsψ (referenceColumn D)),
    matchingInterval_eq_subinterval hsubo (hsψ (fun r => matchingDensity D r * F.1 r))]
    at he
  have hsubu : uIcc l h ⊆ Icc D.a D.b := by
    rw [uIcc_of_le hlh]
    exact hsub.trans Ioo_subset_Icc_self
  have hu := matchingMode_intervalIntegrable hD U.1 hlh hsub
  have hf := matchingMode_intervalIntegrable hD F.1 hlh hsub
  have hw : ContDiff ℝ ∞ D.w := (matchingProfileGeometry hD).2.2.1.1
  have hdψ : ContDiff ℝ ∞ (deriv ψ) := (contDiff_infty_iff_deriv.mp hψ).2
  have hp : Continuous (deriv (fun r => D.w r * deriv ψ r)) :=
    ((contDiff_infty_iff_deriv.mp (hw.mul hdψ)).2).continuous
  have hiP := hu.mul_continuousOn hp.continuousOn
  have hiq := hu.continuousOn_mul ((matchingPotential_continuousOn hD j).mono hsubu)
  have hiqψ := hiq.mul_continuousOn hψ.continuous.continuousOn
  have hic : IntervalIntegrable (fun r => referenceColumn D r * ψ r) volume l h :=
    (((matchingColumn_continuousOn hD hB).mono hsubu).mul
      hψ.continuous.continuousOn).intervalIntegrable
  have hiρ := hf.continuousOn_mul ((matchingDensity_continuousOn hD).mono hsubu)
  have hiρψ := hiρ.mul_continuousOn hψ.continuous.continuousOn
  have hfun :
      (fun r => U.1 r * radialJacobi ((j : ℝ) ^ 2) D.w ψ r) =
        (fun r => U.1 r * deriv (fun t => D.w t * deriv ψ t) r -
          (matchingPotential D j r * U.1 r) * ψ r) := by
    funext r
    dsimp only [radialJacobi, matchingPotential]
    ring
  rw [hfun, intervalIntegral.integral_sub hiP hiqψ] at he
  calc
    (∫ r in l..h, U.1 r * deriv (fun t => D.w t * deriv ψ t) r) =
        (∫ r in l..h, (matchingPotential D j r * U.1 r) * ψ r) +
          U.2 * (∫ r in l..h, referenceColumn D r * ψ r) -
            (∫ r in l..h, matchingDensity D r * F.1 r * ψ r) := by
      linarith only [he]
    _ = ∫ r in l..h, (matchingPotential D j r * U.1 r) * ψ r +
        U.2 * (referenceColumn D r * ψ r) -
          matchingDensity D r * F.1 r * ψ r := by
      rw [intervalIntegral.integral_sub (hiqψ.add (hic.const_mul U.2)) hiρψ,
        intervalIntegral.integral_add hiqψ (hic.const_mul U.2),
        intervalIntegral.integral_const_mul]
    _ = _ := by
      congr 1
      funext r
      dsimp only [matchingPrincipalSource]
      ring

end ContinuousFlexibility.Radial
