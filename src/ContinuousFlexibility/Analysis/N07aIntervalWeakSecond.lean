import ContinuousFlexibility.Analysis.N07aIntervalPrimitiveLp
import ContinuousFlexibility.Analysis.IntervalWeakDivergence
import ContinuousFlexibility.Analysis.L2BoundedMultiplier

/-!
# Recovering the actual second weak derivative on a regular radial interval

The first weak derivative and the scalar divergence equation determine the
weak flux. Division by the actual nonvanishing leading coefficient then
produces a genuine L² second derivative. Only coefficient bounds are used;
no regularity of a chosen L² representative is assumed.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter MeasureTheory
open scoped ContDiff Topology

private theorem n07a_interval_pairing_congr {f g φ : ℝ → ℝ}
    (hfg : f =ᵐ[volume.restrict (Ioo (0 : ℝ) 1)] g)
    (hs : tsupport φ ⊆ Ioo (0 : ℝ) 1) :
    (∫ x, f x * φ x) = ∫ x, g x * φ x := by
  have h := (ae_restrict_iff' measurableSet_Ioo).mp hfg
  apply integral_congr_ae
  filter_upwards [h] with x hx
  by_cases hxin : x ∈ Ioo (0 : ℝ) 1
  · rw [hx hxin]
  · rw [image_eq_zero_of_notMem_tsupport (fun ht => hxin (hs ht)), mul_zero, mul_zero]

/-- The derivative relation depends only on the two prescribed interval
L² representatives. -/
theorem n07a_intervalWeakDerivative_congr {f f' g g' : ℝ → ℝ}
    (hf : f =ᵐ[volume.restrict (Ioo (0 : ℝ) 1)] f')
    (hg : g =ᵐ[volume.restrict (Ioo (0 : ℝ) 1)] g')
    (h : HasIntervalWeakDerivative 0 1 f g) :
    HasIntervalWeakDerivative 0 1 f' g' := by
  intro φ hφ hc hs
  rw [← n07a_interval_pairing_congr hf (tsupport_deriv_subset.trans hs),
    ← n07a_interval_pairing_congr hg hs]
  exact h φ hφ hc hs

/-- The actual second-order weak equation and the first derivative imply
the first-order weak identity for the conormal flux. -/
theorem n07a_interval_weak_flux {a : ℝ → ℝ}
    (ha : ContDiffOn ℝ ∞ a (Ioo (0 : ℝ) 1))
    (u d H : N07aIntervalL2) (hud : HasIntervalWeakDerivative 0 1 u d)
    (heq : ∀ φ : ℝ → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ →
      tsupport φ ⊆ Ioo (0 : ℝ) 1 →
        (∫ x, u x * deriv (fun y => a y * deriv φ y) x) = ∫ x, H x * φ x) :
    HasIntervalWeakDerivative 0 1 (fun x => a x * d x) H := by
  intro φ hφ hc hs
  have hφd := (contDiff_infty_iff_deriv.mp hφ).2
  have hψs : tsupport (fun y => a y * deriv φ y) ⊆ Ioo (0 : ℝ) 1 :=
    tsupport_mul_subset_right.trans (tsupport_deriv_subset.trans hs)
  have hψ : ContDiff ℝ ∞ (fun y => a y * deriv φ y) :=
    contDiff_of_contDiffOn_of_tsupport_subset isOpen_Ioo (ha.mul hφd.contDiffOn) hψs
  have ht := hud _ hψ hc.deriv.mul_left hψs
  have he := heq φ hφ hc hs
  have hex : (∫ x, (a x * d x) * deriv φ x) = ∫ x, d x * (a x * deriv φ x) := by
    apply integral_congr_ae
    exact Eventually.of_forall fun _ => by ring
  rw [hex]
  linarith

/-- Uniform value bounds give multiplication on the actual interval class. -/
private theorem n07a_interval_mul_memLp {χ : ℝ → ℝ}
    (hχ : AEStronglyMeasurable χ (volume.restrict (Ioo (0 : ℝ) 1)))
    {A : ℝ} (hA : ∀ x ∈ Ioo (0 : ℝ) 1, |χ x| ≤ A) (u : N07aIntervalL2) :
    MemLp (fun x => χ x * u x) 2 (volume.restrict (Ioo (0 : ℝ) 1)) :=
  l2Multiplier_memLp _ hχ ((ae_restrict_mem measurableSet_Ioo).mono hA) u

/-- The weak flux identity recovers an actual second derivative. The
explicit frequency-free estimate here is used only to establish the
second-derivative graph; the uniform degenerate energy estimate is proved
separately by approximation. -/
theorem n07a_interval_secondWeak_of_flux {a : ℝ → ℝ}
    (ha : ContDiffOn ℝ ∞ a (Ioo (0 : ℝ) 1))
    (han : ∀ x ∈ Ioo (0 : ℝ) 1, a x ≠ 0)
    (A : ℝ) (hA : 0 ≤ A)
    (hai : ∀ x ∈ Ioo (0 : ℝ) 1, |(a x)⁻¹| ≤ A)
    (had : ∀ x ∈ Ioo (0 : ℝ) 1, |deriv a x| ≤ A)
    (d H : N07aIntervalL2)
    (hflux : HasIntervalWeakDerivative 0 1 (fun x => a x * d x) H) :
    ∃ dd : N07aIntervalL2, HasIntervalWeakDerivative 0 1 d dd ∧
      (dd : ℝ → ℝ) =ᵐ[volume.restrict (Ioo (0 : ℝ) 1)]
        (fun x => (H x - deriv a x * d x) / a x) ∧
      ‖dd‖ ≤ A * ‖H‖ + A ^ 2 * ‖d‖ := by
  let μ := volume.restrict (Ioo (0 : ℝ) 1)
  let χ : ℝ → ℝ := fun x => (a x)⁻¹
  let ψ : ℝ → ℝ := fun x => deriv a x / a x
  have hχs : ContDiffOn ℝ ∞ χ (Ioo (0 : ℝ) 1) := ha.inv han
  have hdas : ContDiffOn ℝ ∞ (deriv a) (Ioo (0 : ℝ) 1) :=
    ha.deriv_of_isOpen isOpen_Ioo (by simp)
  have hψs : ContDiffOn ℝ ∞ ψ (Ioo (0 : ℝ) 1) := hdas.div ha han
  have hχm : AEStronglyMeasurable χ μ := hχs.continuousOn.aestronglyMeasurable measurableSet_Ioo
  have hψm : AEStronglyMeasurable ψ μ := hψs.continuousOn.aestronglyMeasurable measurableSet_Ioo
  have hψb (x : ℝ) (hx : x ∈ Ioo (0 : ℝ) 1) : |ψ x| ≤ A ^ 2 := by
    dsimp only [ψ]
    rw [div_eq_mul_inv, abs_mul]
    simpa only [pow_two] using mul_le_mul (had x hx) (hai x hx) (abs_nonneg _) hA
  let Mi := l2BoundedMultiplier μ hχm ((ae_restrict_mem measurableSet_Ioo).mono hai)
  let Md := l2BoundedMultiplier μ hψm ((ae_restrict_mem measurableSet_Ioo).mono hψb)
  let dd := Mi H - Md d
  have hdd : (dd : ℝ → ℝ) =ᵐ[μ] (fun x => (H x - deriv a x * d x) / a x) := by
    filter_upwards [Lp.coeFn_sub (Mi H) (Md d),
      l2BoundedMultiplier_ae μ hχm ((ae_restrict_mem measurableSet_Ioo).mono hai) H,
      l2BoundedMultiplier_ae μ hψm ((ae_restrict_mem measurableSet_Ioo).mono hψb) d]
      with x hx hi hd
    simp only [Pi.sub_apply] at hx
    rw [hx, hi, hd]
    dsimp only [χ, ψ]
    ring
  have hiLp : MemLp (fun x => χ x * H x) 2 μ := n07a_interval_mul_memLp hχm hai H
  have hdLp : MemLp (fun x => ψ x * d x) 2 μ := n07a_interval_mul_memLp hψm hψb d
  have hweak : HasIntervalWeakDerivative 0 1 d (fun x => χ x * H x - ψ x * d x) := by
    intro φ hφ hc hs
    let test : ℝ → ℝ := fun x => φ x / a x
    have hts : tsupport test ⊆ tsupport φ := by
      simpa only [test, div_eq_mul_inv] using
        (tsupport_mul_subset_left (f := φ) (g := fun x => (a x)⁻¹))
    have ht : ContDiff ℝ ∞ test :=
      contDiff_div_of_tsupport_subset isOpen_Ioo hφ ha han hs
    have htc : HasCompactSupport test := hc.mono' ((subset_tsupport test).trans hts)
    have htest := hflux test ht htc (hts.trans hs)
    have hpoint (x : ℝ) :
        (a x * d x) * deriv test x = d x * deriv φ x - (ψ x * d x) * φ x := by
      by_cases hx : x ∈ Ioo (0 : ℝ) 1
      · have hadx := ((ha.contDiffAt (isOpen_Ioo.mem_nhds hx)).differentiableAt (by simp)).hasDerivAt
        have hquot := ((hφ.differentiable (by simp) x).hasDerivAt.div hadx (han x hx)).deriv
        have htesteq : test = φ / a :=
          funext fun y => (Pi.div_apply φ a y).symm
        rw [htesteq, hquot]
        dsimp only [ψ]
        field_simp [han x hx]
      · have hφx : φ x = 0 := image_eq_zero_of_notMem_tsupport (fun hh => hx (hs hh))
        have hdφx : deriv φ x = 0 :=
          image_eq_zero_of_notMem_tsupport (fun hh => hx (hs (tsupport_deriv_subset hh)))
        have hdt : deriv test x = 0 :=
          image_eq_zero_of_notMem_tsupport (fun hh => hx (hs (hts (tsupport_deriv_subset hh))))
        rw [hφx, hdφx, hdt]
        ring
    have hleft : (∫ x, (a x * d x) * deriv test x) =
        (∫ x, d x * deriv φ x) - ∫ x, (ψ x * d x) * φ x := by
      simp_rw [hpoint]
      exact integral_sub
        (interval_integrable_mul_test (IntegrableOn.locallyIntegrableOn
          ((Lp.memLp d).integrable (by norm_num)))
          (contDiff_infty_iff_deriv.mp hφ).2.continuous hc.deriv (tsupport_deriv_subset.trans hs))
        (interval_integrable_mul_test (IntegrableOn.locallyIntegrableOn
          (hdLp.integrable (by norm_num)))
          hφ.continuous hc hs)
    have hright : (∫ x, H x * test x) = ∫ x, (χ x * H x) * φ x := by
      apply integral_congr_ae
      exact Eventually.of_forall fun x => by dsimp only [test, χ]; ring
    rw [hleft, hright] at htest
    simp_rw [sub_mul]
    rw [integral_sub
      (interval_integrable_mul_test (IntegrableOn.locallyIntegrableOn
        (hiLp.integrable (by norm_num)))
        hφ.continuous hc hs)
      (interval_integrable_mul_test (IntegrableOn.locallyIntegrableOn
        (hdLp.integrable (by norm_num)))
        hφ.continuous hc hs)]
    linarith
  refine ⟨dd, ?_, hdd, ?_⟩
  · apply n07a_intervalWeakDerivative_congr (EventuallyEq.refl _ _) _ hweak
    filter_upwards [hdd] with x hx
    rw [hx]
    dsimp only [χ, ψ]
    ring
  · calc
      ‖dd‖ ≤ ‖Mi H‖ + ‖Md d‖ := norm_sub_le _ _
      _ ≤ A * ‖H‖ + A ^ 2 * ‖d‖ := add_le_add
        (((Mi.le_opNorm H).trans (mul_le_mul_of_nonneg_right
          (norm_l2BoundedMultiplier_le μ hχm hA ((ae_restrict_mem measurableSet_Ioo).mono hai))
          (norm_nonneg H))))
        (((Md.le_opNorm d).trans (mul_le_mul_of_nonneg_right
          (norm_l2BoundedMultiplier_le μ hψm (sq_nonneg A)
            ((ae_restrict_mem measurableSet_Ioo).mono hψb)) (norm_nonneg d))))

end ContinuousFlexibility.Analysis
