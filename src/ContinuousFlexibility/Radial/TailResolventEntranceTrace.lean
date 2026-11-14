module

public import ContinuousFlexibility.Radial.TailResolventClassical
public import Mathlib.MeasureTheory.Function.LpSeminorm.Indicator

/-!
# The Friedrichs entrance trace

On a regular initial interval, the identity
`(c - a) U a = ∫ U - ∫ (c - x) U'` expresses the entrance trace by two
continuous functionals on the weighted energy space. The identity vanishes
on every compact-interior core function, hence on the entire closed form.
-/

@[expose] public section

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
    simpa only [zero_sub, neg_one_mul, id_eq] using h
  have hi : IntervalIntegrable (fun x => -U x + (c - x) * D x) volume a c :=
    hUi.neg.add hVi
  have hUneg : IntervalIntegrable (fun x => -U x) volume a c := hUi.neg
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hac hW hWd hi
  rw [intervalIntegral.integral_add hUneg hVi, intervalIntegral.integral_neg] at hFTC
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
  simpa only [mul_one, one_mul, mul_comm] using hpair

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
    change (c - x) * d x = (c - x) * D x
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

/-- Every weighted `L²` vector is ordinarily integrable all the way to the
regular entrance on a fixed initial interval. -/
theorem tail_intervalIntegrable_at_entrance {T : DeepTailData} {c : ℝ}
    (hp : ContDiffOn ℝ ∞ T.p (Ioo T.entrance T.endpoint))
    (hpos : ∀ x ∈ Ioo T.entrance T.endpoint, 0 < T.p x)
    (hac : T.entrance ≤ c) (hcb : c < T.endpoint)
    (hpNear : ContinuousOn T.p (Icc T.entrance c))
    (hposNear : ∀ x ∈ Icc T.entrance c, 0 < T.p x) (u : DeepTailL2 T) :
    IntervalIntegrable (u : ℝ → ℝ) volume T.entrance c := by
  have hA : MemLp (tailEntranceWeight T c (fun _ => 1)) 2 (deepTailMeasure T) :=
    tailEntranceWeight_memLp hp hpos hpNear hposNear continuousOn_const
  have hi := (Lp.memLp u).integrable_mul hA
  have hdensity := (tail_integrable_density_iff hp hpos _).mp hi
  have hsub : Ioc T.entrance c ⊆ Ioo T.entrance T.endpoint :=
    fun x hx => ⟨hx.1, hx.2.trans_lt hcb⟩
  apply (intervalIntegrable_iff_integrableOn_Ioc_of_le hac).mpr
  apply (hdensity.mono_set hsub).congr_fun _ measurableSet_Ioc
  intro x hx
  change T.p x * (u x * tailEntranceWeight T c (fun _ => 1) x) = u x
  rw [tailEntranceWeight, indicator_of_mem hx]
  field_simp [(hposNear x (Ioc_subset_Icc_self hx)).ne'] <;> ring

/-- An integrable classical derivative has a continuous primitive at the
left endpoint. Only the endpoint value is changed; the whole open-interval
function is retained. -/
theorem exists_interval_left_continuous_extension {a b c : ℝ} {F H : ℝ → ℝ}
    (hac : a < c) (hcb : c < b)
    (hF : ContinuousOn F (Ioo a b))
    (hder : ∀ x ∈ Ioo a b, HasDerivAt F (H x) x)
    (hH : IntervalIntegrable H volume a c) :
    ∃ E : ℝ → ℝ, EqOn E F (Ioo a b) ∧ ContinuousOn E (Ico a b) := by
  let P : ℝ → ℝ := fun x => F c + ∫ t in c..x, H t
  have hcc : c ∈ uIcc a c := by simp only [uIcc_of_le hac.le, mem_Icc, hac.le, le_refl, and_self]
  have hPrimitive : ContinuousOn (fun x => ∫ t in c..x, H t) (Icc a c) := by
    simpa only [uIcc_of_le hac.le] using
      (hH.absolutelyContinuousOnInterval_intervalIntegral hcc).continuousOn
  have hP : ContinuousOn P (Icc a c) := continuousOn_const.fun_add hPrimitive
  have hPeq (x : ℝ) (hx : x ∈ Ioc a c) : P x = F x := by
    have hsub : Icc x c ⊆ Ioo a b :=
      fun y hy => ⟨hx.1.trans_le hy.1, hy.2.trans_lt hcb⟩
    have hi : IntervalIntegrable H volume x c := hH.mono_set (by
      rw [uIcc_of_le hx.2, uIcc_of_le hac.le]
      exact fun y hy => ⟨hx.1.le.trans hy.1, hy.2⟩)
    have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hx.2 (hF.mono hsub)
      (fun y hy => hder y (hsub (Ioo_subset_Icc_self hy))) hi
    dsimp only [P]
    rw [intervalIntegral.integral_symm, hFTC]
    ring
  let E : ℝ → ℝ := fun x => if x = a then P a else F x
  have hEq : EqOn E F (Ioo a b) := by
    intro x hx
    simp only [E, if_neg hx.1.ne']
  have hEqNear : EqOn E P (Icc a c) := by
    intro x hx
    by_cases hxa : x = a
    · simp [E, hxa]
    · rw [show E x = F x from if_neg hxa]
      exact (hPeq x ⟨lt_of_le_of_ne hx.1 (Ne.symm hxa), hx.2⟩).symm
  have hENear : ContinuousOn E (Icc a c) := hP.congr hEqNear
  have hEOpen : ContinuousOn E (Ioo a b) := hF.congr hEq
  refine ⟨E, hEq, ?_⟩
  intro x hx
  by_cases hxa : x = a
  · subst x
    apply (hENear a ⟨le_rfl, hac.le⟩).mono_of_mem_nhdsWithin
    filter_upwards [self_mem_nhdsWithin,
      mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds hac)] with y hy hyc
    exact ⟨hy.1, hyc.le⟩
  · have hxin : x ∈ Ioo a b := ⟨lt_of_le_of_ne hx.1 (Ne.symm hxa), hx.2⟩
    exact (hEOpen.continuousAt (isOpen_Ioo.mem_nhds hxin)).continuousWithinAt

/-- No boundary regularity assumption is needed for the resolvent: local
weighted integrability first extends its flux to the regular entrance, then
extends its function, and the closed form forces the entrance value to zero. -/
theorem exists_tailResolvent_classical_rep_with_entrance {T : DeepTailData}
    (hT : DeepTailHypotheses T) (hI : TailFormIdentification T T.endpoint)
    {u f : DeepTailL2 T} {ψ : ℝ → ℝ}
    (hψ : ContinuousOn ψ (Ioo T.entrance T.endpoint))
    (hf : (f : ℝ → ℝ) =ᵐ[deepTailMeasure T] ψ)
    (hgraph : TailFriedrichsGraph T T.endpoint u (f + T.Λ • u)) :
    ∃ d : DeepTailL2 T, ∃ U Q : ℝ → ℝ,
      (u, d) ∈ TailFormLift T T.endpoint ∧
      ContinuousOn U (Ico T.entrance T.endpoint) ∧
      ContinuousOn Q (Ico T.entrance T.endpoint) ∧ U T.entrance = 0 ∧
      (u : ℝ → ℝ) =ᵐ[deepTailMeasure T] U ∧
      (fun x => T.p x * d x) =ᵐ[deepTailMeasure T] Q ∧
      (∀ x ∈ Ioo T.entrance T.endpoint, HasDerivAt U (Q x / T.p x) x) ∧
      (∀ x ∈ Ioo T.entrance T.endpoint,
        HasDerivAt Q (-(T.p x * (ψ x + T.Λ * U x))) x) := by
  obtain ⟨d, U, Q, hud, hU, hQ, huAE, hQAE, hUd, hQd⟩ :=
    exists_tailResolvent_classical_rep hT hI hψ hf hgraph
  have hTcopy := hT
  rcases hTcopy with ⟨hab, _, _, _, _, _, _, hp, hpos, _, _⟩
  let c : ℝ := (T.entrance + T.endpoint) / 2
  have hac : T.entrance < c := by dsimp only [c]; linarith
  have hcb : c < T.endpoint := by dsimp only [c]; linarith
  have hsub : Icc T.entrance c ⊆ Ico T.entrance T.endpoint :=
    fun x hx => ⟨hx.1, hx.2.trans_lt hcb⟩
  have hpNear := hp.continuousOn.mono hsub
  have hposNear : ∀ x ∈ Icc T.entrance c, 0 < T.p x := fun x hx => hpos x (hsub hx)
  have hpOpen := hp.mono Ioo_subset_Ico_self
  have hposOpen : ∀ x ∈ Ioo T.entrance T.endpoint, 0 < T.p x :=
    fun x hx => hpos x (Ioo_subset_Ico_self hx)
  let s : DeepTailL2 T := f + T.Λ • u
  have hsAE : (s : ℝ → ℝ) =ᵐ[deepTailMeasure T] fun x => ψ x + T.Λ * U x := by
    filter_upwards [Lp.coeFn_add f (T.Λ • u), Lp.coeFn_smul T.Λ u, hf, huAE]
      with x hAdd hSmul hfx hux
    change (f + T.Λ • u) x = ψ x + T.Λ * U x
    change (f + T.Λ • u) x = f x + (T.Λ • u) x at hAdd
    change (T.Λ • u) x = T.Λ * u x at hSmul
    rw [hAdd, hSmul, hfx, hux]
  have hsInt := tail_intervalIntegrable_at_entrance hpOpen hposOpen hac.le hcb hpNear hposNear s
  have hpUcc : ContinuousOn T.p (uIcc T.entrance c) := by
    simpa only [uIcc_of_le hac.le] using hpNear
  have hRawInt : IntervalIntegrable (fun x => -(T.p x * s x)) volume T.entrance c :=
    (hsInt.continuousOn_mul hpUcc).neg
  have hHInt : IntervalIntegrable (fun x => -(T.p x * (ψ x + T.Λ * U x)))
      volume T.entrance c := by
    apply hRawInt.congr_ae
    change ∀ᵐ x ∂volume.restrict (uIoc T.entrance c),
      -(T.p x * s x) = -(T.p x * (ψ x + T.Λ * U x))
    rw [ae_restrict_iff' measurableSet_uIoc]
    filter_upwards [(ae_restrict_iff' measurableSet_Ioo).mp
      ((tail_ae_eq_iff_volume hpOpen hposOpen).mp hsAE)] with x hx hxin
    rw [uIoc_of_le hac.le] at hxin
    rw [hx ⟨hxin.1, hxin.2.trans_lt hcb⟩]
  obtain ⟨E, hEQ, hEcont⟩ := exists_interval_left_continuous_extension hac hcb hQ hQd hHInt
  have hDcont : ContinuousOn (fun x => E x / T.p x) (Icc T.entrance c) :=
    (hEcont.mono hsub).div hpNear (fun x hx => (hposNear x hx).ne')
  have hDInt : IntervalIntegrable (fun x => Q x / T.p x) volume T.entrance c := by
    apply (hDcont.intervalIntegrable_of_Icc hac.le).congr
    intro x hx
    rw [uIoc_of_le hac.le] at hx
    change E x / T.p x = Q x / T.p x
    rw [hEQ ⟨hx.1, hx.2.trans_lt hcb⟩]
  obtain ⟨F, hFU, hFcont⟩ := exists_interval_left_continuous_extension hac hcb hU hUd hDInt
  have hUnew : (u : ℝ → ℝ) =ᵐ[deepTailMeasure T] F := huAE.trans
    ((tail_ae_eq_iff_volume hpOpen hposOpen).mpr (by
      filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
      exact (hFU hx).symm))
  have hQnew : (fun x => T.p x * d x) =ᵐ[deepTailMeasure T] E := hQAE.trans
    ((tail_ae_eq_iff_volume hpOpen hposOpen).mpr (by
      filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
      exact (hEQ hx).symm))
  have hFd (x : ℝ) (hx : x ∈ Ioo T.entrance T.endpoint) :
      HasDerivAt F (E x / T.p x) x := by
    rw [hEQ hx]
    apply (hUd x hx).congr_of_eventuallyEq
    filter_upwards [isOpen_Ioo.mem_nhds hx] with y hy
    exact hFU hy
  have hEd (x : ℝ) (hx : x ∈ Ioo T.entrance T.endpoint) :
      HasDerivAt E (-(T.p x * (ψ x + T.Λ * F x))) x := by
    rw [hFU hx]
    apply (hQd x hx).congr_of_eventuallyEq
    filter_upwards [isOpen_Ioo.mem_nhds hx] with y hy
    exact hEQ hy
  have hFa : F T.entrance = 0 :=
    tailResolvent_classical_entrance_eq_zero hT hac hcb hud
      (hFcont.mono hsub) (hEcont.mono hsub) hUnew hQnew
      (fun x hx => hFd x ⟨hx.1, hx.2.trans hcb⟩)
  exact ⟨d, F, E, hud, hFcont, hEcont, hFa, hUnew, hQnew, hFd, hEd⟩

end ContinuousFlexibility.Radial
