import ContinuousFlexibility.Statements.Nonlinear
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.Deriv.Support
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts

/-!
# First variation of the optical travel angle

On one negative component, a compactly supported logarithmic perturbation
changes the radicand by an affine function of the parameter. A uniform
positive margin on the support permits differentiation under the integral.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open Set Filter MeasureTheory
open scoped ContDiff Topology Interval

def opticalSpeed (w : ℝ → ℝ) (r : ℝ) : ℝ :=
  Real.sqrt (-deriv w r / (r * w r))

def opticalTravel (w : ℝ → ℝ) (l h : ℝ) : ℝ :=
  ∫ r in l..h, opticalSpeed w r

def opticalLogPerturbation (w χ : ℝ → ℝ) (t r : ℝ) : ℝ :=
  w r * Real.exp (t * χ r)

private theorem opticalSpeed_logPerturbation {w χ : ℝ → ℝ}
    {t r : ℝ} (hw : DifferentiableAt ℝ w r) (hχ : DifferentiableAt ℝ χ r)
    (hr : r ≠ 0) (hwr : w r ≠ 0) :
    opticalSpeed (opticalLogPerturbation w χ t) r =
      Real.sqrt (-deriv w r / (r * w r) + t * (-deriv χ r / r)) := by
  have hp := (hw.hasDerivAt.mul ((hχ.hasDerivAt.const_mul t).exp)).deriv
  change deriv (fun s => w s * Real.exp (t * χ s)) r = _ at hp
  unfold opticalSpeed
  change Real.sqrt (-deriv (fun s => w s * Real.exp (t * χ s)) r /
    (r * (w r * Real.exp (t * χ r)))) = _
  rw [hp]
  congr 1
  field_simp [hr, hwr, (Real.exp_pos (t * χ r)).ne']
  ring

/-- The exact log-perturbed travel integral is differentiable at the reference profile. -/
theorem hasDerivAt_opticalTravel_logPerturbation {w χ : ℝ → ℝ} {l a b h : ℝ}
    (hl : 0 < l) (hla : l < a) (hab : a < b) (hbh : b < h)
    (hw : ContDiff ℝ ∞ w) (hχ : ContDiff ℝ ∞ χ)
    (hpos : ∀ r ∈ Icc l h, 0 < w r) (hneg : ∀ r ∈ Ioo l h, deriv w r < 0)
    (hsupp : tsupport χ ⊆ Ioo a b) :
    HasDerivAt (fun t => opticalTravel (opticalLogPerturbation w χ t) l h)
      (∫ r in l..h, -deriv χ r / (2 * r * opticalSpeed w r)) 0 := by
  let Q (r : ℝ) := -deriv w r / (r * w r)
  let B (r : ℝ) := -deriv χ r / r
  let F (t r : ℝ) := Real.sqrt (Q r + t * B r)
  let G (t r : ℝ) := B r / (2 * F t r)
  have hlh : l < h := hla.trans (hab.trans hbh)
  have hsub : Icc a b ⊆ Ioo l h := fun _ hr => ⟨hla.trans_le hr.1, hr.2.trans_lt hbh⟩
  have hQpos (r : ℝ) (hr : r ∈ Icc a b) : 0 < Q r :=
    div_pos (neg_pos.mpr (hneg r (hsub hr)))
      (mul_pos (hl.trans (hsub hr).1) (hpos r (Ioo_subset_Icc_self (hsub hr))))
  have hwd := (contDiff_infty_iff_deriv.mp hw).2.continuous
  have hχd := (contDiff_infty_iff_deriv.mp hχ).2.continuous
  have hQc : ContinuousOn Q (Icc l h) :=
    hwd.neg.continuousOn.div (continuous_id.mul hw.continuous).continuousOn
      (fun r hr => (mul_pos (hl.trans_le hr.1) (hpos r hr)).ne')
  have hBc : ContinuousOn B (Icc a b) :=
    hχd.neg.continuousOn.div continuous_id.continuousOn
      (fun r hr => (hl.trans (hsub hr).1).ne')
  have hne : (Icc a b).Nonempty := nonempty_Icc.mpr hab.le
  obtain ⟨rmin, hrmin, hmin⟩ := isCompact_Icc.exists_isMinOn hne
    (hQc.mono (fun _ hr => Ioo_subset_Icc_self (hsub hr)))
  obtain ⟨rmax, hrmax, hmax⟩ := isCompact_Icc.exists_isMaxOn hne hBc.abs
  let q := Q rmin
  let M := |B rmax|
  let δ := q / (2 * (M + 1))
  have hq : 0 < q := hQpos rmin hrmin
  have hM : 0 ≤ M := abs_nonneg _
  have hd : 0 < δ := div_pos hq (by positivity)
  have hδM : δ * M ≤ q / 2 := by
    have heq : δ * (M + 1) = q / 2 := by
      dsimp only [δ]
      rw [← div_div, div_mul_cancel₀ _ (show M + 1 ≠ 0 by positivity)]
    calc
      δ * M ≤ δ * (M + 1) := mul_le_mul_of_nonneg_left (by linarith) hd.le
      _ = _ := heq
  have hrad (t r : ℝ) (ht : t ∈ Icc (-δ) δ) (hr : r ∈ Icc a b) : 0 < Q r + t * B r := by
    have hprod : |t * B r| ≤ q / 2 := by
      rw [abs_mul]
      exact (mul_le_mul (abs_le.mpr ht) (hmax hr) (abs_nonneg _) hd.le).trans hδM
    have hbase : q ≤ Q r := hmin hr
    linarith only [hprod, neg_abs_le (t * B r), hbase, hq]
  let K := Icc (-δ) δ ×ˢ Icc a b
  have hK : IsCompact K := isCompact_Icc.prod isCompact_Icc
  have hzero : (0 : ℝ) ∈ Icc (-δ) δ := ⟨neg_nonpos.mpr hd.le, hd.le⟩
  have hKne : K.Nonempty := ⟨(0, a), hzero, le_rfl, hab.le⟩
  have hBk : ContinuousOn (fun p : ℝ × ℝ => B p.2) K :=
    hBc.comp continuous_snd.continuousOn (fun _ hp => hp.2)
  have hFk : ContinuousOn (fun p : ℝ × ℝ => F p.1 p.2) K := by
    have hQk : ContinuousOn (fun p : ℝ × ℝ => Q p.2) K :=
      hQc.comp continuous_snd.continuousOn (fun _ hp => Ioo_subset_Icc_self (hsub hp.2))
    exact Real.continuous_sqrt.comp_continuousOn
      (hQk.add (continuous_fst.continuousOn.mul hBk))
  have hGk : ContinuousOn (fun p : ℝ × ℝ => ‖G p.1 p.2‖) K :=
    (hBk.div (continuousOn_const.mul hFk) (fun p hp =>
      (mul_pos zero_lt_two (Real.sqrt_pos.mpr (hrad p.1 p.2 hp.1 hp.2))).ne')).norm
  obtain ⟨pmax, _, hGmax⟩ := hK.exists_isMaxOn hKne hGk
  let N := ‖G pmax.1 pmax.2‖
  have hN : 0 ≤ N := norm_nonneg _
  have hBzero (r : ℝ) (hr : r ∉ Icc a b) : B r = 0 := by
    have hnot : r ∉ tsupport χ := fun hs => hr (Ioo_subset_Icc_self (hsupp hs))
    simp only [B, deriv_of_notMem_tsupport hnot, neg_zero, zero_div]
  let U := Ioo (-δ) δ
  have hU : U ∈ 𝓝 (0 : ℝ) := Ioo_mem_nhds (neg_neg_of_pos hd) hd
  have hderiv (r t : ℝ) (ht : t ∈ U) : HasDerivAt (fun s => F s r) (G t r) t := by
    by_cases hr : r ∈ Icc a b
    · have hlin : HasDerivAt (fun s : ℝ => Q r + s * B r) (B r) t := by
        simpa only [id_eq, one_mul] using (((hasDerivAt_id t).mul_const (B r)).const_add (Q r))
      exact hlin.sqrt (hrad t r (Ioo_subset_Icc_self ht) hr).ne'
    · have heq : (fun s => F s r) = fun _ => Real.sqrt (Q r) := by
        funext s
        simp only [F, hBzero r hr, mul_zero, add_zero]
      rw [heq]
      simpa only [G, hBzero r hr, zero_div] using (hasDerivAt_const t (Real.sqrt (Q r)))
  have hbound (r t : ℝ) (ht : t ∈ U) : ‖G t r‖ ≤ N := by
    by_cases hr : r ∈ Icc a b
    · exact hGmax (show (t, r) ∈ K from ⟨Ioo_subset_Icc_self ht, hr⟩)
    · simpa only [G, hBzero r hr, zero_div, norm_zero] using hN
  let μ := volume.restrict (Ioc l h)
  let : IsFiniteMeasure μ := ⟨by simp [μ, Real.volume_Ioc]⟩
  have hQm : Measurable Q := hwd.neg.measurable.div (measurable_id.mul hw.continuous.measurable)
  have hBm : Measurable B := hχd.neg.measurable.div measurable_id
  have hFm (t : ℝ) : Measurable (F t) :=
    Real.continuous_sqrt.measurable.comp (hQm.add (measurable_const.mul hBm))
  have hGm : AEStronglyMeasurable (G 0) μ :=
    (hBm.div (measurable_const.mul (hFm 0))).aestronglyMeasurable
  have hFi : Integrable (F 0) μ := by
    have hc : ContinuousOn (F 0) (Icc l h) := by
      simpa only [F, zero_mul, add_zero, Function.comp_def] using
        Real.continuous_sqrt.comp_continuousOn hQc
    have hi := hc.intervalIntegrable_of_Icc (μ := volume) hlh.le
    exact hi.1
  have hInt := (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := μ) (F := F) (F' := G) (bound := fun _ => N) hU
    (Eventually.of_forall fun t => (hFm t).aestronglyMeasurable) hFi hGm
    (Eventually.of_forall hbound) (integrable_const N) (Eventually.of_forall hderiv)).2
  change HasDerivAt (fun t => ∫ r in Ioc l h, F t r) (∫ r in Ioc l h, G 0 r) 0 at hInt
  simp_rw [← intervalIntegral.integral_of_le hlh.le] at hInt
  have heq : (fun t => opticalTravel (opticalLogPerturbation w χ t) l h) =
      fun t => ∫ r in l..h, F t r := by
    funext t
    apply intervalIntegral.integral_congr
    intro r hr
    rw [uIcc_of_le hlh.le] at hr
    exact opticalSpeed_logPerturbation (hw.differentiable (by simp) r)
      (hχ.differentiable (by simp) r) (hl.trans_le hr.1).ne' (hpos r hr).ne'
  rw [heq]
  convert hInt using 1
  apply intervalIntegral.integral_congr
  intro r _
  simp only [G, F, B, opticalSpeed, Q, zero_mul, add_zero, div_div, mul_assoc, mul_left_comm r 2]

def opticalInverseFlux (w : ℝ → ℝ) (r : ℝ) : ℝ := (r * opticalSpeed w r)⁻¹

theorem contDiffOn_opticalInverseFlux {w : ℝ → ℝ} {l h : ℝ}
    (hl : 0 < l) (hw : ContDiff ℝ ∞ w) (hpos : ∀ r ∈ Ioo l h, 0 < w r)
    (hneg : ∀ r ∈ Ioo l h, deriv w r < 0) : ContDiffOn ℝ ∞ (opticalInverseFlux w) (Ioo l h) := by
  have hQpos (r : ℝ) (hr : r ∈ Ioo l h) : 0 < -deriv w r / (r * w r) :=
    div_pos (neg_pos.mpr (hneg r hr)) (mul_pos (hl.trans hr.1) (hpos r hr))
  have hQ : ContDiffOn ℝ ∞ (fun r => -deriv w r / (r * w r)) (Ioo l h) :=
    (contDiff_infty_iff_deriv.mp hw).2.neg.contDiffOn.div (contDiff_id.mul hw).contDiffOn
      (fun r hr => (mul_pos (hl.trans hr.1) (hpos r hr)).ne')
  have hv : ContDiffOn ℝ ∞ (opticalSpeed w) (Ioo l h) := hQ.sqrt (fun r hr => (hQpos r hr).ne')
  exact (contDiff_id.contDiffOn.mul hv).inv (fun r hr =>
    (mul_pos (hl.trans hr.1) (Real.sqrt_pos.mpr (hQpos r hr))).ne')

private theorem integral_eq_on_support_interval {f : ℝ → ℝ} {l a b h : ℝ}
    (hla : l ≤ a) (hab : a ≤ b) (hbh : b ≤ h)
    (hf : ContinuousOn f (Icc a b)) (hzero : ∀ r, r ∉ Ioo a b → f r = 0) :
    (∫ r in l..h, f r) = ∫ r in a..b, f r := by
  have hL : EqOn f (fun _ => 0) (uIcc l a) := by
    intro r hr
    rw [uIcc_of_le hla] at hr
    exact hzero r (fun hx => (not_lt_of_ge hr.2) hx.1)
  have hR : EqOn f (fun _ => 0) (uIcc b h) := by
    intro r hr
    rw [uIcc_of_le hbh] at hr
    exact hzero r (fun hx => (not_lt_of_ge hr.1) hx.2)
  have hiL : IntervalIntegrable f volume l a :=
    (intervalIntegrable_congr (hL.mono uIoc_subset_uIcc)).mpr intervalIntegrable_const
  have hiR : IntervalIntegrable f volume b h :=
    (intervalIntegrable_congr (hR.mono uIoc_subset_uIcc)).mpr intervalIntegrable_const
  have hi := hf.intervalIntegrable_of_Icc (μ := volume) hab
  have hL0 : (∫ r in l..a, f r) = 0 := by
    rw [intervalIntegral.integral_congr hL, intervalIntegral.integral_zero]
  have hR0 : (∫ r in b..h, f r) = 0 := by
    rw [intervalIntegral.integral_congr hR, intervalIntegral.integral_zero]
  rw [← intervalIntegral.integral_add_adjacent_intervals (hiL.trans hi) hiR,
    ← intervalIntegral.integral_add_adjacent_intervals hiL hi, hL0, hR0, zero_add, add_zero]

/-- On a compact interior collar, the first variation also has its integrated form. -/
theorem opticalTravel_variation_integral_by_parts {w χ : ℝ → ℝ} {l a b h : ℝ}
    (hl : 0 < l) (hla : l < a) (hab : a < b) (hbh : b < h)
    (hw : ContDiff ℝ ∞ w) (hχ : ContDiff ℝ ∞ χ)
    (hpos : ∀ r ∈ Icc l h, 0 < w r) (hneg : ∀ r ∈ Ioo l h, deriv w r < 0)
    (hsupp : tsupport χ ⊆ Ioo a b) :
    (∫ r in l..h, -deriv χ r / (2 * r * opticalSpeed w r)) =
      (1 / 2 : ℝ) * ∫ r in a..b, deriv (opticalInverseFlux w) r * χ r := by
  have hsub : Icc a b ⊆ Ioo l h := fun _ hr => ⟨hla.trans_le hr.1, hr.2.trans_lt hbh⟩
  have hF := contDiffOn_opticalInverseFlux hl hw (fun r hr => hpos r (Ioo_subset_Icc_self hr)) hneg
  have hFc := hF.continuousOn.mono hsub
  have hFd : ContinuousOn (deriv (opticalInverseFlux w)) (Icc a b) :=
    ((hF.deriv_of_isOpen isOpen_Ioo (by simp : (0 : ℕ∞ω) + 1 ≤ ∞)).continuousOn).mono hsub
  have hχd := (contDiff_infty_iff_deriv.mp hχ).2.continuous.continuousOn (s := Icc a b)
  have hFχd : ContinuousOn (fun r => opticalInverseFlux w r * deriv χ r) (Icc a b) := hFc.mul hχd
  have hFoff (r : ℝ) (hr : r ∉ Ioo a b) : opticalInverseFlux w r * deriv χ r = 0 := by
    rw [deriv_of_notMem_tsupport (fun hs => hr (hsupp hs)), mul_zero]
  have hEq : (∫ r in l..h, -deriv χ r / (2 * r * opticalSpeed w r)) =
      -(1 / 2 : ℝ) * ∫ r in l..h, opticalInverseFlux w r * deriv χ r := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro r _
    unfold opticalInverseFlux
    simp only [div_eq_mul_inv, mul_assoc, mul_inv_rev]
    ring
  have hFderiv (r : ℝ) (hr : r ∈ uIcc a b) :
      HasDerivAt (opticalInverseFlux w) (deriv (opticalInverseFlux w) r) r := by
    rw [uIcc_of_le hab.le] at hr
    exact ((hF.contDiffAt (isOpen_Ioo.mem_nhds (hsub hr))).differentiableAt (by simp)).hasDerivAt
  have hparts := intervalIntegral.integral_mul_deriv_eq_deriv_mul hFderiv
    (fun r _ => (hχ.differentiable (by simp) r).hasDerivAt)
    (hFd.intervalIntegrable_of_Icc hab.le) (hχd.intervalIntegrable_of_Icc hab.le)
  have hχa : χ a = 0 := image_eq_zero_of_notMem_tsupport fun hs => (lt_irrefl a) (hsupp hs).1
  have hχb : χ b = 0 := image_eq_zero_of_notMem_tsupport fun hs => (lt_irrefl b) (hsupp hs).2
  rw [hEq, integral_eq_on_support_interval hla.le hab.le hbh.le hFχd hFoff,
    hparts, hχa, hχb]
  ring

/-- A strict sign of the inverse-flux derivative on an interior collar yields
a compactly supported smooth control with unit optical travel derivative. -/
theorem exists_normalized_opticalControl {w : ℝ → ℝ} {l a b h : ℝ}
    (hl : 0 < l) (hla : l < a) (hab : a < b) (hbh : b < h)
    (hw : ContDiff ℝ ∞ w) (hpos : ∀ r ∈ Icc l h, 0 < w r)
    (hneg : ∀ r ∈ Ioo l h, deriv w r < 0)
    (hsign : (∀ r ∈ Icc a b, 0 < deriv (opticalInverseFlux w) r) ∨
      (∀ r ∈ Icc a b, deriv (opticalInverseFlux w) r < 0)) :
    ∃ χ : ℝ → ℝ, ContDiff ℝ ∞ χ ∧ HasCompactSupport χ ∧ tsupport χ ⊆ Ioo a b ∧
      HasDerivAt (fun t => opticalTravel (opticalLogPerturbation w χ t) l h) 1 0 := by
  let m := (a + b) / 2
  let R := (b - a) / 4
  have hR : 0 < R := div_pos (sub_pos.mpr hab) (by norm_num)
  let f : ContDiffBump m := ⟨R / 2, R, half_pos hR, half_lt_self hR⟩
  have hfc : ContDiff ℝ ∞ (f : ℝ → ℝ) := f.contDiff
  have hsupp : tsupport (f : ℝ → ℝ) ⊆ Ioo a b := by
    rw [f.tsupport_eq]
    intro r hr
    have hdist : |r - m| ≤ R := by
      simpa only [Metric.mem_closedBall, Real.dist_eq] using hr
    have hd := abs_le.mp hdist
    constructor <;> dsimp only [m, R] at hd ⊢ <;> linarith only [hd.1, hd.2, hab]
  have hm : m ∈ Icc a b := by
    constructor <;> dsimp only [m] <;> linarith only [hab]
  have hfm : f m = 1 := f.one_of_mem_closedBall (Metric.mem_closedBall_self (half_pos hR).le)
  let u := opticalInverseFlux w
  let J := ∫ r in a..b, deriv u r * f r
  have hu := contDiffOn_opticalInverseFlux hl hw (fun r hr => hpos r (Ioo_subset_Icc_self hr)) hneg
  have huc : ContinuousOn (deriv u) (Icc a b) :=
    (hu.deriv_of_isOpen isOpen_Ioo (by simp : (0 : ℕ∞ω) + 1 ≤ ∞)).continuousOn.mono
      (fun _ hr => ⟨hla.trans_le hr.1, hr.2.trans_lt hbh⟩)
  have hJc : ContinuousOn (fun r => deriv u r * f r) (Icc a b) :=
    huc.mul hfc.continuous.continuousOn
  have hJ : J ≠ 0 := by
    rcases hsign with hp | hn
    · have hj : 0 < J := intervalIntegral.integral_pos hab hJc
        (fun r hr => mul_nonneg (hp r (Ioc_subset_Icc_self hr)).le (f.nonneg' r))
        ⟨m, hm, by rw [hfm, mul_one]; exact hp m hm⟩
      exact hj.ne'
    · have hj : 0 < ∫ r in a..b, -(deriv u r * f r) := intervalIntegral.integral_pos hab hJc.neg
        (fun r hr => neg_nonneg.mpr
          (mul_nonpos_of_nonpos_of_nonneg (hn r (Ioc_subset_Icc_self hr)).le (f.nonneg' r)))
        ⟨m, hm, by rw [hfm, mul_one]; exact neg_pos.mpr (hn m hm)⟩
      rw [intervalIntegral.integral_neg, neg_pos] at hj
      exact hj.ne
  let d := (1 / 2 : ℝ) * J
  have hd : d ≠ 0 := mul_ne_zero (by norm_num) hJ
  let χ (r : ℝ) := d⁻¹ * f r
  have hχ : ContDiff ℝ ∞ χ := contDiff_const.mul hfc
  have hχsupp : tsupport χ ⊆ Ioo a b := tsupport_mul_subset_right.trans hsupp
  have hχcompact : HasCompactSupport χ := isCompact_Icc.of_isClosed_subset isClosed_closure
    (hχsupp.trans Ioo_subset_Icc_self)
  refine ⟨χ, hχ, hχcompact, hχsupp, ?_⟩
  have h := hasDerivAt_opticalTravel_logPerturbation hl hla hab hbh hw hχ hpos hneg hχsupp
  rw [opticalTravel_variation_integral_by_parts hl hla hab hbh hw hχ hpos hneg hχsupp] at h
  have heq : (∫ r in a..b, deriv u r * χ r) = d⁻¹ * J := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro r _
    unfold χ
    ring
  change HasDerivAt _ ((1 / 2 : ℝ) * ∫ r in a..b, deriv u r * χ r) 0 at h
  rw [heq, ← mul_left_comm, show (1 / 2 : ℝ) * J = d from rfl, inv_mul_cancel₀ hd] at h
  exact h

end ContinuousFlexibility.Statements
