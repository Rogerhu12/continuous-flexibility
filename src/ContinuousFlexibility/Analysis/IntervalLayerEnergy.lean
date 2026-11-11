import ContinuousFlexibility.Analysis.IntervalCaccioppoli

/-!
# Caccioppoli on a measurable endpoint layer

The equation and its C¹ representative live on the full open interval.
The energy identity is supported by the cutoff and can consequently be
integrated over any measurable subset containing its topological support.
Coefficient bounds are required only on that subset.
-/

open Set Filter MeasureTheory
open scoped ContDiff Topology

namespace ContinuousFlexibility.Analysis

noncomputable section

set_option backward.isDefEq.respectTransparency false

theorem interval_cutoff_caccioppoli_on_set {a b : ℝ} (hab : a < b)
    {s : Set ℝ} (hs : MeasurableSet s) (hsI : s ⊆ Ioo a b)
    {u w f c χ : ℝ → ℝ} (hu : ContDiffOn ℝ 1 u (Ioo a b))
    (hw : ContinuousOn w (Ioo a b)) (hc : ContinuousOn c (Ioo a b))
    (hfloc : LocallyIntegrableOn f (Ioo a b) volume)
    (hf : MemLp f 2 (volume.restrict s)) (hu₂ : MemLp u 2 (volume.restrict s))
    (hχ : ContDiff ℝ ∞ χ) (hχc : HasCompactSupport χ)
    (hχs : tsupport χ ⊆ s) {K L j : ℝ} (hK : 1 ≤ K) (hL : 1 ≤ L)
    (hcoef : ∀ x ∈ s, 1 / K ≤ w x ∧ w x ≤ K ∧ |χ x| ≤ 1 ∧
      |deriv χ x| ≤ L ∧ |c x| ≤ K)
    (x₀ : ℝ) (hx₀ : x₀ ∈ Ioo a b) (q : ℝ)
    (hflux : ∀ x ∈ Ioo a b, w x * deriv u x =
      intervalLocalPrimitive (fun y => f y + j ^ 2 * c y * u y) x₀ x + q) :
    (∫ x in s, χ x ^ 2 * deriv u x ^ 2) ≤
      7 * K ^ 2 * L ^ 2 * ((∫ x in s, f x ^ 2) +
        (1 + j ^ 2) * (∫ x in s, u x ^ 2)) := by
  have hχI : tsupport χ ⊆ Ioo a b := hχs.trans hsI
  have hpot : ContinuousOn (fun x => j ^ 2 * c x * u x) (Ioo a b) :=
    (continuousOn_const.mul hc).mul hu.continuousOn
  have hloc : LocallyIntegrableOn
      (fun x => f x + j ^ 2 * c x * u x) (Ioo a b) volume :=
    hfloc.add (hpot.locallyIntegrableOn (μ := volume) measurableSet_Ioo)
  have hud : ContinuousOn (deriv u) (Ioo a b) :=
    continuousOn_deriv_of_contDiffOn_one_Ioo hu
  have hχd : Continuous (deriv χ) := (contDiff_infty_iff_deriv.mp hχ).2.continuous
  have hEcore : ContinuousOn (fun x => w x * χ x * deriv u x ^ 2) (Ioo a b) :=
    (hw.mul hχ.continuous.continuousOn).mul (hud.pow 2)
  have hEi : Integrable (fun x => w x * χ x ^ 2 * deriv u x ^ 2) := by
    have hi := integrable_mul_test_of_locallyIntegrableOn_Ioo
      (hEcore.locallyIntegrableOn (μ := volume) measurableSet_Ioo) hχ.continuous hχc hχI
    exact hi.congr (Eventually.of_forall fun x => by ring)
  have hDcore : ContinuousOn (fun x => χ x * deriv u x ^ 2) (Ioo a b) :=
    hχ.continuous.continuousOn.mul (hud.pow 2)
  have hDi : Integrable (fun x => χ x ^ 2 * deriv u x ^ 2) := by
    have hi := integrable_mul_test_of_locallyIntegrableOn_Ioo
      (hDcore.locallyIntegrableOn (μ := volume) measurableSet_Ioo) hχ.continuous hχc hχI
    exact hi.congr (Eventually.of_forall fun x => by ring)
  have hXcore : ContinuousOn
      (fun x => w x * deriv χ x * u x * deriv u x) (Ioo a b) :=
    ((hw.mul hχd.continuousOn).mul hu.continuousOn).mul hud
  have hXi : Integrable (fun x => w x * χ x * deriv χ x * u x * deriv u x) := by
    have hi := integrable_mul_test_of_locallyIntegrableOn_Ioo
      (hXcore.locallyIntegrableOn (μ := volume) measurableSet_Ioo) hχ.continuous hχc hχI
    exact hi.congr (Eventually.of_forall fun x => by ring)
  obtain ⟨hψ, hψc, hψs⟩ := interval_cutoff_square_mul_test hu hχ hχc hχI
  have hHi : Integrable
      (fun x => (f x + j ^ 2 * c x * u x) * (χ x ^ 2 * u x)) :=
    integrable_mul_test_of_locallyIntegrableOn_Ioo hloc hψ.continuous hψc hψs
  have hEeq : (∫ x in s, w x * χ x ^ 2 * deriv u x ^ 2) =
      ∫ x, w x * χ x ^ 2 * deriv u x ^ 2 := by
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro x hx
    have hz : χ x = 0 := image_eq_zero_of_notMem_tsupport (fun hh => hx (hχs hh))
    simp only [hz, zero_pow (by decide : 2 ≠ 0), mul_zero, zero_mul]
  have hXeq : (∫ x in s, w x * χ x * deriv χ x * u x * deriv u x) =
      ∫ x, w x * χ x * deriv χ x * u x * deriv u x := by
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro x hx
    have hz : χ x = 0 := image_eq_zero_of_notMem_tsupport (fun hh => hx (hχs hh))
    simp only [hz, mul_zero, zero_mul]
  have hHeq : (∫ x in s, (f x + j ^ 2 * c x * u x) * (χ x ^ 2 * u x)) =
      ∫ x, (f x + j ^ 2 * c x * u x) * (χ x ^ 2 * u x) := by
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro x hx
    have hz : χ x = 0 := image_eq_zero_of_notMem_tsupport (fun hh => hx (hχs hh))
    simp only [hz, zero_pow (by decide : 2 ≠ 0), mul_zero, zero_mul]
  have heq : (∫ x in s, w x * χ x ^ 2 * deriv u x ^ 2) =
      -(∫ x in s, (f x + j ^ 2 * c x * u x) * (χ x ^ 2 * u x)) -
        2 * (∫ x in s, w x * χ x * deriv χ x * u x * deriv u x) := by
    rw [hEeq, hHeq, hXeq]
    exact interval_cutoff_energy_identity hab hu hw hloc hχ hχc hχI x₀ hx₀ q hflux
  have hf₂ : Integrable (fun x => f x ^ 2) (volume.restrict s) := hf.integrable_sq
  have hu₂' : Integrable (fun x => u x ^ 2) (volume.restrict s) := hu₂.integrable_sq
  exact cutoff_caccioppoli_of_energy_identity (volume.restrict s) hK hL
    ((ae_restrict_mem hs).mono fun x hx => hcoef x hx)
    hEi.integrableOn hDi.integrableOn hXi.integrableOn hHi.integrableOn hf₂ hu₂' heq

end

end ContinuousFlexibility.Analysis
