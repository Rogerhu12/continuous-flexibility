import ContinuousFlexibility.Radial.TailResolventClassical
import Mathlib.MeasureTheory.Function.LpSeminorm.Indicator

/-!
# The Friedrichs entrance trace

On a regular initial interval, the identity
`(c - a) U a = ∫ U - ∫ (c - x) U'` expresses the entrance trace by two
continuous functionals on the weighted energy space. The identity vanishes
on every compact-interior core function, hence on the entire closed form.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open Set Filter MeasureTheory Real
open scoped Topology ContDiff InnerProductSpace
open ContinuousFlexibility.Statements

/-- The coefficient representing an ordinary integral on an initial
interval as an inner product in the weighted space. -/
def tailEntranceWeight (T : DeepTailData) (c : ℝ) (r : ℝ → ℝ) : ℝ → ℝ :=
  (Ioc T.entrance c).indicator (fun x => r x / T.p x)

/-- The regular endpoint makes every continuous local coefficient an actual
weighted `L²` vector, even when the total tail measure is infinite. -/
theorem tailEntranceWeight_memLp {T : DeepTailData} {c : ℝ} {r : ℝ → ℝ}
    (hp : ContDiffOn ℝ ∞ T.p (Ioo T.entrance T.endpoint))
    (hpos : ∀ x ∈ Ioo T.entrance T.endpoint, 0 < T.p x)
    (hpNear : ContinuousOn T.p (Icc T.entrance c))
    (hposNear : ∀ x ∈ Icc T.entrance c, 0 < T.p x)
    (hr : ContinuousOn r (Icc T.entrance c)) :
    MemLp (tailEntranceWeight T c r) 2 (deepTailMeasure T) := by
  have hdiv : ContinuousOn (fun x => r x / T.p x) (Icc T.entrance c) :=
    hr.div hpNear (fun x hx => (hposNear x hx).ne')
  have hmeas : AEStronglyMeasurable (tailEntranceWeight T c r) (deepTailMeasure T) :=
    (aestronglyMeasurable_indicator_iff measurableSet_Ioc).mpr
      ((hdiv.mono Ioc_subset_Icc_self).aestronglyMeasurable measurableSet_Ioc)
  apply (memLp_two_iff_integrable_sq hmeas).mpr
  apply (tail_integrable_density_iff hp hpos _).mpr
  have hcont : ContinuousOn (fun x => T.p x * (r x / T.p x) ^ 2)
      (Icc T.entrance c) := hpNear.fun_mul (hdiv.fun_pow 2)
  have hi : IntegrableOn (fun x => T.p x * (r x / T.p x) ^ 2)
      (Ioc T.entrance c) volume :=
    (hcont.integrableOn_compact isCompact_Icc).mono_set Ioc_subset_Icc_self
  have hIndicator : Integrable ((Ioc T.entrance c).indicator
      (fun x => T.p x * (r x / T.p x) ^ 2)) volume :=
    (integrable_indicator_iff measurableSet_Ioc).mpr hi
  have he : (fun x => T.p x * (tailEntranceWeight T c r x) ^ 2) =
      (Ioc T.entrance c).indicator (fun x => T.p x * (r x / T.p x) ^ 2) := by
    funext x
    by_cases hx : x ∈ Ioc T.entrance c
    · simp only [tailEntranceWeight, indicator_of_mem hx]
    · simp only [tailEntranceWeight, indicator_of_notMem hx, zero_pow (by norm_num : (2 : ℕ) ≠ 0),
        mul_zero]
  rw [he]
  exact hIndicator.integrableOn

/-- The local integral is a continuous functional on the full weighted
Hilbert space. -/
def tailEntrancePairing (T : DeepTailData) (c : ℝ) (r : ℝ → ℝ)
    (hr : MemLp (tailEntranceWeight T c r) 2 (deepTailMeasure T)) :
    DeepTailL2 T →L[ℝ] ℝ :=
  innerSL ℝ (hr.toLp (tailEntranceWeight T c r))

theorem tailEntrancePairing_apply {T : DeepTailData} {c : ℝ} {r U : ℝ → ℝ}
    (hp : ContDiffOn ℝ ∞ T.p (Ioo T.entrance T.endpoint))
    (hpos : ∀ x ∈ Ioo T.entrance T.endpoint, 0 < T.p x)
    (hac : T.entrance ≤ c) (hcb : c < T.endpoint)
    (hr : MemLp (tailEntranceWeight T c r) 2 (deepTailMeasure T))
    (u : DeepTailL2 T) (hu : (u : ℝ → ℝ) =ᵐ[deepTailMeasure T] U) :
    tailEntrancePairing T c r hr u = ∫ x in T.entrance..c, U x * r x := by
  have hs : Function.support ((Ioc T.entrance c).indicator r) ⊆
      Ioo T.entrance T.endpoint := by
    intro x hx
    by_cases hxin : x ∈ Ioc T.entrance c
    · exact ⟨hxin.1, hxin.2.trans_lt hcb⟩
    · exact False.elim (hx (indicator_of_notMem hxin r))
  rw [tailEntrancePairing, innerSL_apply_apply, L2.inner_def]
  calc
    (∫ x, ⟪(hr.toLp (tailEntranceWeight T c r)) x, u x⟫_ℝ ∂deepTailMeasure T) =
        ∫ x, U x * (((Ioc T.entrance c).indicator r) x / T.p x) ∂deepTailMeasure T := by
      apply integral_congr_ae
      filter_upwards [MemLp.coeFn_toLp hr, hu] with x hweight hx
      rw [hweight, hx]
      by_cases hxin : x ∈ Ioc T.entrance c
      · simp only [tailEntranceWeight, indicator_of_mem hxin, RCLike.inner_apply,
          conj_trivial, mul_comm]
      · simp only [tailEntranceWeight, indicator_of_notMem hxin, RCLike.inner_apply,
          conj_trivial, zero_div, zero_mul, mul_zero]
    _ = ∫ x, U x * ((Ioc T.entrance c).indicator r) x :=
      tail_integral_div_test hp hpos hs U
    _ = ∫ x, (Ioc T.entrance c).indicator (fun x => U x * r x) x := by
      apply integral_congr_ae
      exact Eventually.of_forall fun x => by
        by_cases hx : x ∈ Ioc T.entrance c
        · simp only [indicator_of_mem hx]
        · simp only [indicator_of_notMem hx, mul_zero]
    _ = ∫ x in T.entrance..c, U x * r x := by
      rw [integral_indicator measurableSet_Ioc, intervalIntegral.integral_of_le hac]

/-- The elementary trace identity needs differentiability only inside the
interval and continuity of the function and derivative at the endpoints. -/
theorem interval_entrance_trace_identity {a c : ℝ} (hac : a ≤ c) {U D : ℝ → ℝ}
    (hU : ContinuousOn U (Icc a c)) (hD : ContinuousOn D (Icc a c))
    (hder : ∀ x ∈ Ioo a c, HasDerivAt U (D x) x) :
    (∫ x in a..c, U x) - (∫ x in a..c, (c - x) * D x) = (c - a) * U a := by
  have hW : ContinuousOn (fun x => (c - x) * U x) (Icc a c) :=
    (continuousOn_const.fun_sub continuousOn_id).fun_mul hU
  have hV : ContinuousOn (fun x => (c - x) * D x) (Icc a c) :=
    (continuousOn_const.fun_sub continuousOn_id).fun_mul hD
  have hUi : IntervalIntegrable U volume a c := hU.intervalIntegrable_of_Icc hac
  have hVi : IntervalIntegrable (fun x => (c - x) * D x) volume a c :=
    hV.intervalIntegrable_of_Icc hac
  have hWd (x : ℝ) (hx : x ∈ Ioo a c) :
      HasDerivAt (fun y => (c - y) * U y) (-U x + (c - x) * D x) x := by
    have h := ((hasDerivAt_const x c).fun_sub (hasDerivAt_id x)).fun_mul (hder x hx)
    simpa only [zero_sub, neg_one_mul] using h
  have hi : IntervalIntegrable (fun x => -U x + (c - x) * D x) volume a c :=
    hUi.neg.add hVi
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hac hW hWd hi
  rw [intervalIntegral.integral_add hUi.neg hVi, intervalIntegral.integral_neg] at hFTC
  simp only [sub_self, zero_mul, zero_sub] at hFTC
  linarith only [hFTC]

/-- The zero entrance trace passes from compact core functions to the closed
energy form by continuity of the two local pairings. This interface requires
no pointwise representative of a form-domain element. -/
theorem tailFormLift_entrance_integral_identity {T : DeepTailData} {c endCut : ℝ}
    (hp : ContDiffOn ℝ ∞ T.p (Ioo T.entrance T.endpoint))
    (hpos : ∀ x ∈ Ioo T.entrance T.endpoint, 0 < T.p x)
    (hac : T.entrance < c) (hcb : c < T.endpoint)
    (hpNear : ContinuousOn T.p (Icc T.entrance c))
    (hposNear : ∀ x ∈ Icc T.entrance c, 0 < T.p x)
    {u d : DeepTailL2 T} (hud : (u, d) ∈ TailFormLift T endCut) :
    (∫ x in T.entrance..c, u x) = ∫ x in T.entrance..c, (c - x) * d x := by
  have hA : MemLp (tailEntranceWeight T c (fun _ => 1)) 2 (deepTailMeasure T) :=
    tailEntranceWeight_memLp hp hpos hpNear hposNear continuousOn_const
  have hB : MemLp (tailEntranceWeight T c (fun x => c - x)) 2 (deepTailMeasure T) :=
    tailEntranceWeight_memLp hp hpos hpNear hposNear
      (continuousOn_const.sub continuousOn_id)
  let A := tailEntrancePairing T c (fun _ => 1) hA
  let B := tailEntrancePairing T c (fun x => c - x) hB
  have hclosed : IsClosed {z : DeepTailL2 T × DeepTailL2 T | A z.1 = B z.2} :=
    isClosed_eq (A.continuous.comp continuous_fst) (B.continuous.comp continuous_snd)
  have hcore : TailEnergyCore T endCut ⊆
      {z : DeepTailL2 T × DeepTailL2 T | A z.1 = B z.2} := by
    rintro z ⟨φ, hφ, hc, hs, hu, hd⟩
    have hφa : φ T.entrance = 0 := image_eq_zero_of_notMem_tsupport
      (fun h => (lt_irrefl T.entrance) (hs h).1)
    have hdφ : ContDiff ℝ ∞ (deriv φ) := (contDiff_infty_iff_deriv.mp hφ).2
    have htrace := interval_entrance_trace_identity hac.le
      hφ.continuous.continuousOn hdφ.continuous.continuousOn
      (fun x _ => (hφ.differentiable (by simp) x).hasDerivAt)
    rw [hφa, mul_zero] at htrace
    change A z.1 = B z.2
    dsimp only [A, B]
    rw [tailEntrancePairing_apply hp hpos hac.le hcb hA z.1 hu,
      tailEntrancePairing_apply hp hpos hac.le hcb hB z.2 hd]
    simpa only [mul_one, mul_comm] using sub_eq_zero.mp htrace
  have hpair : A u = B d := (closure_minimal hcore hclosed) hud
  dsimp only [A, B] at hpair
  rw [tailEntrancePairing_apply hp hpos hac.le hcb hA u EventuallyEq.rfl,
    tailEntrancePairing_apply hp hpos hac.le hcb hB d EventuallyEq.rfl] at hpair
  simpa only [mul_one, mul_comm] using hpair

/-- Every classical representative of a closed-form element has zero
entrance value. The representative is not assumed to have zero trace. -/
theorem tailFormLift_classical_entrance_eq_zero {T : DeepTailData} {c endCut : ℝ}
    (hp : ContDiffOn ℝ ∞ T.p (Ioo T.entrance T.endpoint))
    (hpos : ∀ x ∈ Ioo T.entrance T.endpoint, 0 < T.p x)
    (hac : T.entrance < c) (hcb : c < T.endpoint)
    (hpNear : ContinuousOn T.p (Icc T.entrance c))
    (hposNear : ∀ x ∈ Icc T.entrance c, 0 < T.p x)
    {u d : DeepTailL2 T} {U D : ℝ → ℝ}
    (hud : (u, d) ∈ TailFormLift T endCut)
    (hU : ContinuousOn U (Icc T.entrance c))
    (hD : ContinuousOn D (Icc T.entrance c))
    (hu : (u : ℝ → ℝ) =ᵐ[deepTailMeasure T] U)
    (hd : (d : ℝ → ℝ) =ᵐ[deepTailMeasure T] D)
    (hder : ∀ x ∈ Ioo T.entrance c, HasDerivAt U (D x) x) : U T.entrance = 0 := by
  have hform := tailFormLift_entrance_integral_identity hp hpos hac hcb hpNear hposNear hud
  have huVol := (ae_restrict_iff' measurableSet_Ioo).mp
    ((tail_ae_eq_iff_volume hp hpos).mp hu)
  have hdVol := (ae_restrict_iff' measurableSet_Ioo).mp
    ((tail_ae_eq_iff_volume hp hpos).mp hd)
  have hUint : (∫ x in T.entrance..c, u x) = ∫ x in T.entrance..c, U x := by
    apply intervalIntegral.integral_congr_ae
    filter_upwards [huVol] with x hx hxin
    rw [uIoc_of_le hac.le] at hxin
    exact hx ⟨hxin.1, hxin.2.trans_lt hcb⟩
  have hDint : (∫ x in T.entrance..c, (c - x) * d x) =
      ∫ x in T.entrance..c, (c - x) * D x := by
    apply intervalIntegral.integral_congr_ae
    filter_upwards [hdVol] with x hx hxin
    rw [uIoc_of_le hac.le] at hxin
    rw [hx ⟨hxin.1, hxin.2.trans_lt hcb⟩]
  rw [hUint, hDint] at hform
  have htrace := interval_entrance_trace_identity hac.le hU hD hder
  rw [hform, sub_self] at htrace
  exact (mul_eq_zero.mp htrace.symm).resolve_left (sub_pos.mpr hac).ne'

/-- The first-order function/flux representatives satisfy the required
zero entrance boundary condition as soon as both extend continuously there. -/
theorem tailResolvent_classical_entrance_eq_zero {T : DeepTailData}
    (hT : DeepTailHypotheses T) {c endCut : ℝ}
    (hac : T.entrance < c) (hcb : c < T.endpoint)
    {u d : DeepTailL2 T} {U Q : ℝ → ℝ}
    (hud : (u, d) ∈ TailFormLift T endCut)
    (hU : ContinuousOn U (Icc T.entrance c))
    (hQ : ContinuousOn Q (Icc T.entrance c))
    (hu : (u : ℝ → ℝ) =ᵐ[deepTailMeasure T] U)
    (hflux : (fun x => T.p x * d x) =ᵐ[deepTailMeasure T] Q)
    (hder : ∀ x ∈ Ioo T.entrance c, HasDerivAt U (Q x / T.p x) x) :
    U T.entrance = 0 := by
  rcases hT with ⟨_, _, _, _, _, _, _, hp, hpos, _, _⟩
  have hsub : Icc T.entrance c ⊆ Ico T.entrance T.endpoint :=
    fun x hx => ⟨hx.1, hx.2.trans_lt hcb⟩
  have hpNear := hp.continuousOn.mono hsub
  have hposNear : ∀ x ∈ Icc T.entrance c, 0 < T.p x := fun x hx => hpos x (hsub hx)
  have hpOpen := hp.mono Ioo_subset_Ico_self
  have hposOpen : ∀ x ∈ Ioo T.entrance T.endpoint, 0 < T.p x :=
    fun x hx => hpos x (Ioo_subset_Ico_self hx)
  have hd : (d : ℝ → ℝ) =ᵐ[deepTailMeasure T] fun x => Q x / T.p x := by
    apply (tail_ae_eq_iff_volume hpOpen hposOpen).mpr
    filter_upwards [(tail_ae_eq_iff_volume hpOpen hposOpen).mp hflux,
      ae_restrict_mem measurableSet_Ioo] with x hx hxin
    apply (eq_div_iff (hposOpen x hxin).ne').mpr
    simpa only [mul_comm] using hx
  exact tailFormLift_classical_entrance_eq_zero hpOpen hposOpen hac hcb hpNear hposNear
    hud hU (hQ.div hpNear (fun x hx => (hposNear x hx).ne')) hu hd hder

end ContinuousFlexibility.Radial
