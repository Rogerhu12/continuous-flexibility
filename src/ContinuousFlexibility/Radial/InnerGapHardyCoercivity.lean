module

public import ContinuousFlexibility.Radial.RadialPositiveHardy
public import ContinuousFlexibility.Radial.InnerGapDirichlet

/-!
# Hardy coercivity on the actual closed gap energy domain

The physical Hardy inequality first applies to the genuine smooth
zero-Dirichlet core. Its continuous coordinate-norm formulation passes
to the same closed form domain already used by the gap inverse.
The resulting inverse bound is independent of the positive slope
chosen to construct that inverse.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Radial

open Real Set MeasureTheory Filter ContinuousFlexibility.Statements
open scoped ContDiff InnerProductSpace

theorem innerGap_deriv_nonneg_of_slope {w : ℝ → ℝ} {a b s : ℝ}
    (ha : 0 < a) (hs : 0 ≤ s) (hpos : ∀ r ∈ Icc a b, 0 < w r)
    (hslope : ∀ r ∈ Icc a b, s ≤ r * deriv w r / w r) :
    ∀ r ∈ Icc a b, 0 ≤ deriv w r := by
  intro r hr
  have h := mul_nonneg (hs.trans (hslope r hr)) (hpos r hr).le
  rw [div_mul_cancel₀ _ (hpos r hr).ne'] at h
  exact (mul_nonneg_iff_of_pos_left (ha.trans_le hr.1)).mp h

/-- The two derivative coordinates and the value coordinate are those
of the actual smooth radial test function, in the original measure. -/
theorem innerGapEnergyCore_hardy (D : ReferenceData) (hw : ContDiff ℝ ∞ D.w)
    {a b j : ℝ} (hab : a ≤ b) (ha : 0 < a)
    (hcore : Ioo a b ⊆ radialCore D) (hpos : ∀ r ∈ Icc a b, 0 < D.w r)
    (hwp : ∀ r ∈ Icc a b, 0 ≤ deriv D.w r) (hj : (1 / 2 : ℝ) ≤ j ^ 2)
    (q : InnerGapEnergyTriple D) (hq : q ∈ InnerGapEnergyCore D j a b) :
    (1 / 48 : ℝ) * ‖q.fst‖ ^ 2 ≤ ‖q.snd‖ ^ 2 := by
  rcases hq with ⟨u, hu, _, hsupport, hu₀, hu₁, hu₂⟩
  have hvalue : q.fst = innerRadialIntervalToLp D hw.continuous ha hcore
      (fun r hr => (hpos r (Ioo_subset_Icc_self hr)).le) u hu.continuous.continuousOn :=
    Lp.ext (hu₀.trans (innerRadialIntervalToLp_ae D hw.continuous ha hcore
      (fun r hr => (hpos r (Ioo_subset_Icc_self hr)).le) u hu.continuous.continuousOn).symm)
  have hgrad : q.snd.fst = (innerGapEnergyPair D hw ha hcore hpos j u hu).fst :=
    Lp.ext (hu₁.trans (innerGapEnergyPair_fst_ae D hw ha hcore hpos j u hu).symm)
  have hpot : q.snd.snd = (innerGapEnergyPair D hw ha hcore hpos j u hu).snd :=
    Lp.ext (hu₂.trans (innerGapEnergyPair_snd_ae D hw ha hcore hpos j u hu).symm)
  have henergy : ‖q.snd‖ ^ 2 = ‖innerGapEnergyPair D hw ha hcore hpos j u hu‖ ^ 2 := by
    simp only [WithLp.prod_norm_sq_eq_of_L2, hgrad, hpot]
  have hzero : u a = 0 :=
    image_eq_zero_of_notMem_tsupport (fun hh => (lt_irrefl a) (hsupport hh).1)
  have hslope : ∀ r ∈ Icc a b, 0 ≤ r * deriv D.w r / D.w r :=
    fun r hr => div_nonneg (mul_nonneg (ha.trans_le hr.1).le (hwp r hr)) (hpos r hr).le
  rw [hvalue, henergy, innerRadialIntervalToLp_norm_sq D hw.continuous hab,
    innerGapEnergyPair_norm_sq D hw hab ha hcore hpos hslope]
  have hh : innerRadialGapMass D.w u a b ≤
      48 * innerRadialGapEnergy D.w u j a b + 24 * (D.w a / a) * u a ^ 2 := by
    unfold innerRadialGapMass innerRadialGapEnergy
    exact radialPositiveHardy_mass_le_energy_left hab ha hw hu
      (fun r hr => (hpos r hr).le) hwp hj
  rw [hzero, zero_pow (by decide : 2 ≠ 0), mul_zero, add_zero] at hh
  linarith only [hh]

/-- Hardy coercivity holds on the same complete physical form domain,
with no new representative or derivative interpretation. -/
theorem innerGapFormSpace_hardy (D : ReferenceData) (hw : ContDiff ℝ ∞ D.w)
    {a b j : ℝ} (hab : a ≤ b) (ha : 0 < a)
    (hcore : Ioo a b ⊆ radialCore D) (hpos : ∀ r ∈ Icc a b, 0 < D.w r)
    (hwp : ∀ r ∈ Icc a b, 0 ≤ deriv D.w r) (hj : (1 / 2 : ℝ) ≤ j ^ 2)
    (q : InnerGapEnergyTriple D) (hq : q ∈ innerGapFormSpace D j a b) :
    (1 / 48 : ℝ) * ‖q.fst‖ ^ 2 ≤ ‖q.snd‖ ^ 2 := by
  have hf : Continuous (fun q : InnerGapEnergyTriple D => q.fst) :=
    (WithLp.fstL 2 ℝ (RadialModeL2 D) (InnerGapEnergyPair D)).continuous
  have hg : Continuous (fun q : InnerGapEnergyTriple D => q.snd) :=
    (WithLp.sndL 2 ℝ (RadialModeL2 D) (InnerGapEnergyPair D)).continuous
  have hclosed : IsClosed {q : InnerGapEnergyTriple D |
      (1 / 48 : ℝ) * ‖q.fst‖ ^ 2 ≤ ‖q.snd‖ ^ 2} :=
    isClosed_le (continuous_const.mul (hf.norm.pow 2)) (hg.norm.pow 2)
  apply (closure_minimal ?_ hclosed) ((mem_innerGapFormSpace D j a b q).mp hq)
  intro z hz
  exact innerGapEnergyCore_hardy D hw hab ha hcore hpos hwp hj z hz

/-- The already constructed physical gap inverse has a uniform norm
bound. The auxiliary slope affects its construction, but not this bound. -/
theorem innerGapDirichletInverse_norm_le_hardy (D : ReferenceData)
    (hw : ContDiff ℝ ∞ D.w) {a b j s : ℝ}
    (hab : a ≤ b) (ha : 0 < a) (hj : 0 < j) (hs : 0 < s)
    (hcore : Ioo a b ⊆ radialCore D) (hpos : ∀ r ∈ Icc a b, 0 < D.w r)
    (hslope : ∀ r ∈ Icc a b, s ≤ r * deriv D.w r / D.w r)
    (hjhalf : (1 / 2 : ℝ) ≤ j ^ 2) :
    ‖innerGapDirichletInverse D hw hab ha hj hs hcore hpos hslope‖ ≤ 48 := by
  have h := innerGapForm_isCoercive D hw hab ha hj hs hcore hpos hslope
  have hwp := innerGap_deriv_nonneg_of_slope ha hs.le hpos hslope
  have hb := innerCoerciveGradientInverse_norm_le (E := innerGapFormSpace D j a b)
    (H := RadialModeL2 D) (Z := InnerGapEnergyPair D)
    (innerGapFormFunction D j a b) (innerGapFormEnergy D j a b) h
    (δ := (1 / 48 : ℝ)) (by norm_num) (fun q => by
      rw [innerGapFormFunction_apply, innerGapFormEnergy_apply]
      exact innerGapFormSpace_hardy D hw hab ha hcore hpos hwp hjhalf q q.property)
  simpa only [innerGapDirichletInverse, one_div, inv_inv] using hb

end ContinuousFlexibility.Radial
