import ContinuousFlexibility.Radial.BufferIntervalTrace
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts

/-!
# Gluing genuine fields at a buffer cut

The weak derivative of a piecewise classical field is computed by integration
by parts on the two sides of the cut. Matching values remove the first-order
boundary term. A jump in the first derivative gives the exact point-source
coefficient for the Schrödinger equation.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open Real Set Filter MeasureTheory
open ContinuousFlexibility.Statements
open scoped Topology ContDiff RealInnerProductSpace InnerProductSpace

def bufferCutGlue (c : ℝ) (uL uR : ℝ → ℝ) (x : ℝ) : ℝ :=
  if x ≤ c then uL x else uR x

@[simp] theorem bufferCutGlue_of_le (c : ℝ) (uL uR : ℝ → ℝ) {x : ℝ} (hx : x ≤ c) :
    bufferCutGlue c uL uR x = uL x := if_pos hx

theorem bufferCutGlue_of_lt (c : ℝ) (uL uR : ℝ → ℝ) {x : ℝ} (hx : c < x) :
    bufferCutGlue c uL uR x = uR x := if_neg (not_le.mpr hx)

/-- The actual `L²` class of a glued field, formed with measurable indicators. -/
def bufferCutGlueL2 (c : ℝ) (uL uR : RadialL2) : RadialL2 :=
  bufferL2Indicator (Iic c) measurableSet_Iic uL +
    bufferL2Indicator (Ioi c) measurableSet_Ioi uR

theorem bufferCutGlueL2_coeFn (c : ℝ) (uL uR : RadialL2) :
    (bufferCutGlueL2 c uL uR : ℝ → ℝ) =ᵐ[volume]
      bufferCutGlue c (uL : ℝ → ℝ) (uR : ℝ → ℝ) := by
  filter_upwards [Lp.coeFn_add (bufferL2Indicator (Iic c) measurableSet_Iic uL)
    (bufferL2Indicator (Ioi c) measurableSet_Ioi uR),
    bufferL2Indicator_coeFn (Iic c) measurableSet_Iic uL,
    bufferL2Indicator_coeFn (Ioi c) measurableSet_Ioi uR] with x hadd hL hR
  change (bufferL2Indicator (Iic c) measurableSet_Iic uL +
    bufferL2Indicator (Ioi c) measurableSet_Ioi uR) x = _
  rw [hadd]
  simp only [Pi.add_apply]
  rw [hL, hR]
  by_cases hx : x ≤ c
  · simp [bufferCutGlue, hx, not_lt.mpr hx]
  · simp [bufferCutGlue, hx, lt_of_not_ge hx]

theorem bufferCutGlueL2_ae (c : ℝ) {uL uR : RadialL2} {UL UR : ℝ → ℝ}
    (hL : (uL : ℝ → ℝ) =ᵐ[volume] UL) (hR : (uR : ℝ → ℝ) =ᵐ[volume] UR) :
    (bufferCutGlueL2 c uL uR : ℝ → ℝ) =ᵐ[volume] bufferCutGlue c UL UR := by
  filter_upwards [bufferCutGlueL2_coeFn c uL uR, hL, hR] with x hx hLx hRx
  rw [hx]
  by_cases hxc : x ≤ c <;> simp [bufferCutGlue, hxc, hLx, hRx]

/-- Compact testing turns the whole-line piecewise integral into two ordinary
finite interval integrals. -/
theorem bufferCutGlue_integral_mul {f g ψ : ℝ → ℝ} {a c b : ℝ}
    (hac : a < c) (hcb : c < b) (hf : LocallyIntegrable f volume)
    (hg : LocallyIntegrable g volume) (hψ : Continuous ψ) (hcψ : HasCompactSupport ψ)
    (hzψ : ∀ x, x ∉ Ioo a b → ψ x = 0) :
    (∫ x : ℝ, bufferCutGlue c f g x * ψ x) =
      (∫ x in a..c, f x * ψ x) + ∫ x in c..b, g x * ψ x := by
  have hfI : Integrable (fun x => f x * ψ x) volume := by
    simpa only [smul_eq_mul] using hf.integrable_smul_right_of_hasCompactSupport hψ hcψ
  have hgI : Integrable (fun x => g x * ψ x) volume := by
    simpa only [smul_eq_mul] using hg.integrable_smul_right_of_hasCompactSupport hψ hcψ
  have hsplit : (∫ x : ℝ, bufferCutGlue c f g x * ψ x) =
      (∫ x in Iic c, f x * ψ x) + ∫ x in Ioi c, g x * ψ x := by
    calc
      _ = ∫ x : ℝ, (Iic c).piecewise (fun x => f x * ψ x) (fun x => g x * ψ x) x := by
        apply integral_congr_ae
        filter_upwards [] with x
        by_cases hx : x ≤ c <;> simp [bufferCutGlue, Set.piecewise, hx]
      _ = _ := by
        simpa only [compl_Iic] using integral_piecewise measurableSet_Iic
          hfI.integrableOn hgI.integrableOn
  have hleft : (∫ x in Iic c, f x * ψ x) = ∫ x in a..c, f x * ψ x := by
    rw [intervalIntegral.integral_of_le hac.le]
    apply setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_Iic
      (fun x hx => hx.2)
    intro x hx
    rw [hzψ x (fun hxi => hx.2 ⟨hxi.1, hx.1⟩), mul_zero]
  have hright : (∫ x in Ioi c, g x * ψ x) = ∫ x in c..b, g x * ψ x := by
    rw [intervalIntegral.integral_of_le hcb.le]
    apply setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_Ioi
      (fun x hx => hx.1)
    intro x hx
    rw [hzψ x (fun hxi => hx.2 ⟨hx.1, hxi.2.le⟩), mul_zero]
  rw [hsplit, hleft, hright]

/-- The exact first-order jump formula. The functions themselves need only
be continuous; their classical derivative is required on the open sides of
the cut, and the derivative data are merely locally integrable. -/
theorem bufferCutGlue_weakPairing {uL uR dL dR : ℝ → ℝ} (c : ℝ)
    (huL : Continuous uL) (huR : Continuous uR)
    (hdL : LocallyIntegrable dL volume) (hdR : LocallyIntegrable dR volume)
    (hleft : ∀ x < c, HasDerivAt uL (dL x) x)
    (hright : ∀ x, c < x → HasDerivAt uR (dR x) x)
    (φ : ℝ → ℝ) (hφ : ContDiff ℝ ∞ φ) (hcφ : HasCompactSupport φ) :
    (∫ x : ℝ, bufferCutGlue c uL uR x * deriv φ x) =
      (uL c - uR c) * φ c - ∫ x : ℝ, bufferCutGlue c dL dR x * φ x := by
  obtain ⟨R, hR⟩ := hcφ.isCompact.isBounded.subset_closedBall (0 : ℝ)
  let a : ℝ := -(|R| + |c|) - 1
  let b : ℝ := |R| + |c| + 1
  have hac : a < c := by dsimp [a]; linarith [abs_nonneg R, neg_abs_le c]
  have hcb : c < b := by dsimp [b]; linarith [abs_nonneg R, le_abs_self c]
  have hsupport : tsupport φ ⊆ Ioo a b := by
    intro x hx
    have hbound : |x| ≤ R := by
      simpa only [Real.dist_eq, sub_zero] using Metric.mem_closedBall.mp (hR hx)
    have hbounds := abs_le.mp (hbound.trans (le_abs_self R))
    exact ⟨by dsimp [a]; linarith [hbounds.1, abs_nonneg c],
      by dsimp [b]; linarith [hbounds.2, abs_nonneg c]⟩
  have hφzero (x : ℝ) (hx : x ∉ Ioo a b) : φ x = 0 :=
    image_eq_zero_of_notMem_tsupport (fun hm => hx (hsupport hm))
  have hφ'zero (x : ℝ) (hx : x ∉ Ioo a b) : deriv φ x = 0 :=
    deriv_of_notMem_tsupport (fun hm => hx (hsupport hm))
  have hφ' : ContDiff ℝ ∞ (deriv φ) := (contDiff_infty_iff_deriv.mp hφ).2
  have hφa : φ a = 0 := hφzero a (by simp)
  have hφb : φ b = 0 := hφzero b (by simp)
  have hL := intervalIntegral.integral_mul_deriv_eq_deriv_mul_of_hasDerivAt
    (a := a) (b := c) huL.continuousOn hφ.continuous.continuousOn
    (fun x hx => hleft x (by simpa only [min_eq_left hac.le, max_eq_right hac.le] using hx.2))
    (fun x _ => (hφ.differentiable (by simp) x).hasDerivAt)
    (buffer_locallyIntegrable_intervalIntegrable hdL a c)
    (hφ'.continuous.intervalIntegrable a c)
  have hR' := intervalIntegral.integral_mul_deriv_eq_deriv_mul_of_hasDerivAt
    (a := c) (b := b) huR.continuousOn hφ.continuous.continuousOn
    (fun x hx => hright x (by simpa only [min_eq_left hcb.le, max_eq_right hcb.le] using hx.1))
    (fun x _ => (hφ.differentiable (by simp) x).hasDerivAt)
    (buffer_locallyIntegrable_intervalIntegrable hdR c b)
    (hφ'.continuous.intervalIntegrable c b)
  rw [hφa, mul_zero, sub_zero] at hL
  rw [hφb, mul_zero, zero_sub] at hR'
  rw [bufferCutGlue_integral_mul hac hcb huL.locallyIntegrable huR.locallyIntegrable
    hφ'.continuous hcφ.deriv hφ'zero,
    bufferCutGlue_integral_mul hac hcb hdL hdR hφ.continuous hcφ hφzero,
    hL, hR']
  ring

/-- Matching true traces remove the jump term and give the genuine weak
derivative of the glued `L²` field. -/
theorem bufferCutGlue_weakDerivative {u d : RadialL2} {uL uR dL dR : ℝ → ℝ} (c : ℝ)
    (huL : Continuous uL) (huR : Continuous uR)
    (hdL : LocallyIntegrable dL volume) (hdR : LocallyIntegrable dR volume)
    (hleft : ∀ x < c, HasDerivAt uL (dL x) x)
    (hright : ∀ x, c < x → HasDerivAt uR (dR x) x)
    (hmatch : uL c = uR c)
    (hu : (u : ℝ → ℝ) =ᵐ[volume] bufferCutGlue c uL uR)
    (hd : (d : ℝ → ℝ) =ᵐ[volume] bufferCutGlue c dL dR) :
    WeakRadialDerivative u d := by
  intro φ hφ hcφ
  have hpair := bufferCutGlue_weakPairing c huL huR hdL hdR hleft hright φ hφ hcφ
  rw [hmatch, sub_self, zero_mul, zero_sub] at hpair
  calc
    _ = ∫ x : ℝ, bufferCutGlue c uL uR x * deriv φ x := by
      apply integral_congr_ae
      filter_upwards [hu] with x hx using congrArg (fun v : ℝ => v * deriv φ x) hx
    _ = -(∫ x : ℝ, bufferCutGlue c dL dR x * φ x) := hpair
    _ = _ := by
      congr 1
      apply integral_congr_ae
      filter_upwards [hd] with x hx using congrArg (fun v : ℝ => v * φ x) hx.symm

theorem bufferCutGlueL2_weakDerivative {uL uR dL dR : RadialL2}
    {UL UR DL DR : ℝ → ℝ} (c : ℝ)
    (hUL : Continuous UL) (hUR : Continuous UR)
    (hDL : LocallyIntegrable DL volume) (hDR : LocallyIntegrable DR volume)
    (hleft : ∀ x < c, HasDerivAt UL (DL x) x)
    (hright : ∀ x, c < x → HasDerivAt UR (DR x) x)
    (hmatch : UL c = UR c)
    (huL : (uL : ℝ → ℝ) =ᵐ[volume] UL) (huR : (uR : ℝ → ℝ) =ᵐ[volume] UR)
    (hdL : (dL : ℝ → ℝ) =ᵐ[volume] DL) (hdR : (dR : ℝ → ℝ) =ᵐ[volume] DR) :
    WeakRadialDerivative (bufferCutGlueL2 c uL uR) (bufferCutGlueL2 c dL dR) :=
  bufferCutGlue_weakDerivative c hUL hUR hDL hDR hleft hright hmatch
    (bufferCutGlueL2_ae c huL huR) (bufferCutGlueL2_ae c hdL hdR)

/-- Potential weights commute with the actual measurable gluing operation. -/
theorem bufferCutGlueL2_weight_ae (V : ℝ → ℝ) (c : ℝ) {uL uR qL qR : RadialL2}
    (hL : (qL : ℝ → ℝ) =ᵐ[volume] fun x => sqrt (1 + |V x|) * uL x)
    (hR : (qR : ℝ → ℝ) =ᵐ[volume] fun x => sqrt (1 + |V x|) * uR x) :
    (bufferCutGlueL2 c qL qR : ℝ → ℝ) =ᵐ[volume]
      fun x => sqrt (1 + |V x|) * bufferCutGlueL2 c uL uR x := by
  filter_upwards [bufferCutGlueL2_coeFn c qL qR, bufferCutGlueL2_coeFn c uL uR, hL, hR]
    with x hq hu hLx hRx
  rw [hq, hu]
  by_cases hx : x ≤ c <;> simp [bufferCutGlue, hx, hLx, hRx]

/-- The compact-test energy identity, with the genuine derivative jump as
the coefficient of point evaluation. -/
theorem bufferCutGlue_delta_energy {V : ℝ → ℝ} (hV : Continuous V)
    {u d f : RadialL2} {dL dR rL rR : ℝ → ℝ} (c : ℝ)
    (hdL : Continuous dL) (hdR : Continuous dR)
    (hrL : LocallyIntegrable rL volume) (hrR : LocallyIntegrable rR volume)
    (hleft : ∀ x < c, HasDerivAt dL (rL x) x)
    (hright : ∀ x, c < x → HasDerivAt dR (rR x) x)
    (hd : (d : ℝ → ℝ) =ᵐ[volume] bufferCutGlue c dL dR)
    (hr : bufferCutGlue c rL rR =ᵐ[volume] fun x => V x * u x - f x)
    (φ : ℝ → ℝ) (hφ : ContDiff ℝ ∞ φ) (hcφ : HasCompactSupport φ) :
    (∫ x : ℝ, d x * deriv φ x) + (∫ x : ℝ, V x * u x * φ x) =
      (∫ x : ℝ, f x * φ x) + (dL c - dR c) * φ c := by
  have hpair := bufferCutGlue_weakPairing c hdL hdR hrL hrR hleft hright φ hφ hcφ
  have hdeq : (∫ x : ℝ, d x * deriv φ x) =
      ∫ x : ℝ, bufferCutGlue c dL dR x * deriv φ x := by
    apply integral_congr_ae
    filter_upwards [hd] with x hx using congrArg (fun v : ℝ => v * deriv φ x) hx
  have hVu : LocallyIntegrable (fun x => V x * u x) volume :=
    MeasureTheory.LocallyIntegrable.continuous_mul hV
      ((Lp.memLp u).locallyIntegrable (by norm_num))
  have hVuφ : Integrable (fun x => V x * u x * φ x) volume := by
    simpa only [smul_eq_mul] using hVu.integrable_smul_right_of_hasCompactSupport
      hφ.continuous hcφ
  have hfφ : Integrable (fun x => f x * φ x) volume :=
    (Lp.memLp f).integrable_mul (hφ.continuous.memLp_of_hasCompactSupport hcφ)
  have hreq : (∫ x : ℝ, bufferCutGlue c rL rR x * φ x) =
      (∫ x : ℝ, V x * u x * φ x) - ∫ x : ℝ, f x * φ x := by
    rw [← integral_sub hVuφ hfφ]
    apply integral_congr_ae
    filter_upwards [hr] with x hx
    rw [hx]
    ring
  rw [← hdeq, hreq] at hpair
  linarith

/-- The distributional Schrödinger identity for a piecewise classical
field. The source is the actual `L²` function, with a single point source
equal to the left derivative minus the right derivative. -/
theorem bufferCutGlue_delta_schrodinger {V : ℝ → ℝ} (hV : Continuous V)
    {u d f : RadialL2} (hud : WeakRadialDerivative u d)
    {dL dR rL rR : ℝ → ℝ} (c : ℝ)
    (hdL : Continuous dL) (hdR : Continuous dR)
    (hrL : LocallyIntegrable rL volume) (hrR : LocallyIntegrable rR volume)
    (hleft : ∀ x < c, HasDerivAt dL (rL x) x)
    (hright : ∀ x, c < x → HasDerivAt dR (rR x) x)
    (hd : (d : ℝ → ℝ) =ᵐ[volume] bufferCutGlue c dL dR)
    (hr : bufferCutGlue c rL rR =ᵐ[volume] fun x => V x * u x - f x)
    (φ : ℝ → ℝ) (hφ : ContDiff ℝ ∞ φ) (hcφ : HasCompactSupport φ) :
    (∫ x : ℝ, u x * (-deriv (deriv φ) x + V x * φ x)) =
      (∫ x : ℝ, f x * φ x) + (dL c - dR c) * φ c := by
  have henergy := bufferCutGlue_delta_energy hV c hdL hdR hrL hrR
    hleft hright hd hr φ hφ hcφ
  have hφ' := (contDiff_infty_iff_deriv.mp hφ).2
  have hφ'' := (contDiff_infty_iff_deriv.mp hφ').2
  have hweak := hud (deriv φ) hφ' hcφ.deriv
  have hI : Integrable (fun x : ℝ => u x * deriv (deriv φ) x) volume :=
    (Lp.memLp u).integrable_mul (hφ''.continuous.memLp_of_hasCompactSupport hcφ.deriv.deriv)
  have hVu : LocallyIntegrable (fun x => V x * u x) volume :=
    MeasureTheory.LocallyIntegrable.continuous_mul hV
      ((Lp.memLp u).locallyIntegrable (by norm_num))
  have hJ : Integrable (fun x => V x * u x * φ x) volume := by
    simpa only [smul_eq_mul] using hVu.integrable_smul_right_of_hasCompactSupport
      hφ.continuous hcφ
  calc
    _ = -(∫ x : ℝ, u x * deriv (deriv φ) x) + ∫ x : ℝ, V x * u x * φ x := by
      rw [← integral_neg, ← integral_add hI.neg hJ]
      apply integral_congr_ae
      filter_upwards [] with x
      ring
    _ = _ := by rw [hweak, neg_neg]; exact henergy

end ContinuousFlexibility.Radial
