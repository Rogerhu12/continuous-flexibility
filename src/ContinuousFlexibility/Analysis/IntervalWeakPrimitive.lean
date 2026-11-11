import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.Analysis.Calculus.BumpFunction.Normed
import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.Deriv.Support

/-!
# Integral representatives of weak derivatives on an interval

Local integrability and the compact-interior test identity determine a
representative of the form `c + ∫ x₀..x, g`. This representative is continuous
and absolutely continuous on every compact subinterval. If the weak derivative
is continuous, the representative has that derivative at every interior point.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter MeasureTheory
open scoped Topology ContDiff

/-- The test class is compactly contained in the open interval. -/
def HasIntervalWeakDerivative (a b : ℝ) (f g : ℝ → ℝ) : Prop :=
  ∀ ψ : ℝ → ℝ, ContDiff ℝ ∞ ψ → HasCompactSupport ψ →
    tsupport ψ ⊆ Ioo a b →
    (∫ x, f x * deriv ψ x) = -(∫ x, g x * ψ x)

/-- Compact subsets of an open interval lie strictly inside a smaller
compact interval. -/
theorem interval_compact_subset_Ioo {a b : ℝ} (hab : a < b) {K : Set ℝ}
    (hK : IsCompact K) (hs : K ⊆ Ioo a b) :
    ∃ l r : ℝ, a < l ∧ l < r ∧ r < b ∧ K ⊆ Ioo l r := by
  rcases K.eq_empty_or_nonempty with he | hn
  · refine ⟨(2 * a + b) / 3, (a + 2 * b) / 3, by linarith,
      by linarith, by linarith, ?_⟩
    rw [he]
    exact empty_subset _
  · obtain ⟨x, hx, hmin⟩ := hK.exists_isLeast hn
    obtain ⟨y, hy, hmax⟩ := hK.exists_isGreatest hn
    obtain ⟨l, hal, hlx⟩ := exists_between (hs hx).1
    obtain ⟨r, hyr, hrb⟩ := exists_between (hs hy).2
    exact ⟨l, r, hal, (hlx.trans_le (hmin hy)).trans hyr, hrb,
      fun z hz => ⟨hlx.trans_le (hmin hz), (hmax hz).trans_lt hyr⟩⟩

/-- A locally integrable function can be paired with any continuous test
whose compact support stays in the interval. -/
theorem interval_integrable_mul_test {a b : ℝ} {f ψ : ℝ → ℝ}
    (hf : LocallyIntegrableOn f (Ioo a b)) (hψ : Continuous ψ)
    (hc : HasCompactSupport ψ) (hs : tsupport ψ ⊆ Ioo a b) :
    Integrable (fun x => f x * ψ x) := by
  have hi : Integrable ((tsupport ψ).indicator f) :=
    (integrable_indicator_iff (isClosed_tsupport ψ).measurableSet).mpr
      (hf.integrableOn_compact_subset hs hc)
  have hp : Integrable (fun x => ((tsupport ψ).indicator f) x • ψ x) :=
    hi.smul_of_top_left (hψ.memLp_top_of_hasCompactSupport hc volume)
  convert hp using 1
  funext x
  by_cases hx : x ∈ tsupport ψ
  · simp only [indicator_of_mem hx, smul_eq_mul]
  · simp only [indicator_of_notMem hx, image_eq_zero_of_notMem_tsupport hx,
      mul_zero, zero_smul]

/-- A zero-integral smooth test has a smooth primitive with compact support
in the same open interval. -/
theorem exists_interval_compact_primitive {a b : ℝ} (hab : a < b) {g : ℝ → ℝ}
    (hg : ContDiff ℝ ∞ g) (hc : HasCompactSupport g)
    (hs : tsupport g ⊆ Ioo a b) (hzero : (∫ x, g x) = 0) :
    ∃ P : ℝ → ℝ, ContDiff ℝ ∞ P ∧ HasCompactSupport P ∧
      tsupport P ⊆ Ioo a b ∧ deriv P = g := by
  obtain ⟨l, r, hal, hlr, hrb, hgs⟩ := interval_compact_subset_Ioo hab hc hs
  let P : ℝ → ℝ := fun x => ∫ t in l..x, g t
  have hP (x : ℝ) : HasDerivAt P (g x) x :=
    (hg.continuous.integral_hasStrictDerivAt l x).hasDerivAt
  have hd : deriv P = g := funext fun x => (hP x).deriv
  have hgzero (x : ℝ) (hx : x ∉ Ioc l r) : g x = 0 :=
    image_eq_zero_of_notMem_tsupport (fun h => hx ⟨(hgs h).1, (hgs h).2.le⟩)
  have hPzero (x : ℝ) (hx : x ∉ Icc l r) : P x = 0 := by
    change (∫ t in l..x, g t) = 0
    by_cases hxl : x < l
    · have hI : (∫ t in Ioc x l, g t) = 0 := by
        calc
          _ = ∫ _ in Ioc x l, (0 : ℝ) := by
            apply setIntegral_congr_fun measurableSet_Ioc
            intro t ht
            exact hgzero t (fun hm => (not_lt_of_ge ht.2) hm.1)
          _ = 0 := by simp
      rw [intervalIntegral.integral_symm, intervalIntegral.integral_of_le hxl.le,
        hI, neg_zero]
    · have hlx : l ≤ x := le_of_not_gt hxl
      have hrx : r < x := lt_of_not_ge (fun h => hx ⟨hlx, h⟩)
      have hout (t : ℝ) (ht : t ∉ Ioc l x) : g t = 0 :=
        hgzero t (fun hm => ht ⟨hm.1, hm.2.trans hrx.le⟩)
      rw [intervalIntegral.integral_of_le hlx]
      exact (setIntegral_eq_integral_of_forall_compl_eq_zero hout).trans hzero
  have hsP : tsupport P ⊆ Icc l r := by
    apply closure_minimal _ isClosed_Icc
    intro x hx
    by_contra h
    exact hx (hPzero x h)
  have hcP : HasCompactSupport P :=
    HasCompactSupport.intro isCompact_Icc hPzero
  refine ⟨P, contDiff_infty_iff_deriv.mpr
    ⟨fun x => (hP x).differentiableAt, hd.symm ▸ hg⟩, hcP, ?_, hd⟩
  exact hsP.trans (fun x hx => ⟨hal.trans_le hx.1, hx.2.trans_lt hrb⟩)

/-- A unit-integral smooth test strictly inside the interval. -/
theorem exists_interval_unit_test {a b : ℝ} (hab : a < b) :
    ∃ η : ℝ → ℝ, ContDiff ℝ ∞ η ∧ HasCompactSupport η ∧
      tsupport η ⊆ Ioo a b ∧ (∫ x, η x) = 1 := by
  let χ : ContDiffBump ((a + b) / 2) :=
    { rIn := (b - a) / 8, rOut := (b - a) / 4,
      rIn_pos := by linarith, rIn_lt_rOut := by linarith }
  refine ⟨χ.normed volume, χ.contDiff_normed, χ.hasCompactSupport_normed, ?_,
    χ.integral_normed⟩
  rw [χ.tsupport_normed_eq]
  intro x hx
  have hdist : |x - (a + b) / 2| ≤ (b - a) / 4 := by
    simpa only [Real.dist_eq, χ] using Metric.mem_closedBall.mp hx
  have h := abs_le.mp hdist
  constructor <;> linarith [h.1, h.2]

/-- Vanishing weak derivative means a single almost-everywhere constant on
the connected open interval. -/
theorem interval_ae_constant_of_integral_deriv_zero {a b : ℝ} (hab : a < b)
    {F : ℝ → ℝ} (hF : LocallyIntegrableOn F (Ioo a b))
    (hzero : ∀ ψ : ℝ → ℝ, ContDiff ℝ ∞ ψ → HasCompactSupport ψ →
      tsupport ψ ⊆ Ioo a b → (∫ x, F x * deriv ψ x) = 0) :
    ∃ c : ℝ, F =ᵐ[volume.restrict (Ioo a b)] fun _ => c := by
  obtain ⟨η, hη, hcη, hsη, hηone⟩ := exists_interval_unit_test hab
  let c : ℝ := ∫ x, F x * η x
  have hcLoc : LocallyIntegrableOn (fun _ : ℝ => c) (Ioo a b) :=
    continuousOn_const.locallyIntegrableOn measurableSet_Ioo
  have hz : ∀ᵐ x ∂volume, x ∈ Ioo a b → F x - c = 0 := by
    apply isOpen_Ioo.ae_eq_zero_of_integral_contDiff_smul_eq_zero (hF.sub hcLoc)
    intro φ hφ hcφ hsφ
    let M : ℝ := ∫ x, φ x
    let g : ℝ → ℝ := fun x => φ x - M * η x
    have hg : ContDiff ℝ ∞ g := hφ.sub (contDiff_const.mul hη)
    have hcg : HasCompactSupport g := hcφ.sub (hcη.mul_left (f := fun _ => M))
    have hsg : tsupport g ⊆ Ioo a b :=
      (tsupport_sub φ (fun x => M * η x)).trans
        (union_subset hsφ (tsupport_mul_subset_right.trans hsη))
    have hφI : Integrable φ := hφ.continuous.integrable_of_hasCompactSupport hcφ
    have hηI : Integrable η := hη.continuous.integrable_of_hasCompactSupport hcη
    have hgzero : (∫ x, g x) = 0 := by
      change (∫ x, φ x - M * η x) = 0
      rw [integral_sub hφI (hηI.const_mul M), integral_const_mul, hηone, mul_one]
      exact sub_self _
    obtain ⟨P, hP, hcP, hsP, hdP⟩ := exists_interval_compact_primitive hab hg hcg hsg hgzero
    have hPg := hzero P hP hcP hsP
    rw [hdP] at hPg
    have hFφ := interval_integrable_mul_test hF hφ.continuous hcφ hsφ
    have hFη := interval_integrable_mul_test hF hη.continuous hcη hsη
    have hsplit : (∫ x, F x * g x) = (∫ x, F x * φ x) - M * c := by
      calc
        _ = ∫ x, F x * φ x - M * (F x * η x) := by
          apply integral_congr_ae
          exact Eventually.of_forall fun x => by dsimp only [g]; ring
        _ = _ := by rw [integral_sub hFφ (hFη.const_mul M), integral_const_mul]
    rw [hsplit] at hPg
    have heq : (∫ x, φ x * F x) = M * c := by
      simpa only [mul_comm] using sub_eq_zero.mp hPg
    have hφF : Integrable (fun x => φ x * F x) := by
      simpa only [mul_comm] using hFφ
    change (∫ x, φ x * (F x - c)) = 0
    simp_rw [mul_sub]
    rw [integral_sub hφF (hφI.mul_const c), integral_mul_const, heq]
    exact sub_self _
  refine ⟨c, ?_⟩
  rw [ae_restrict_iff' measurableSet_Ioo]
  filter_upwards [hz] with x hx hxin
  exact sub_eq_zero.mp (hx hxin)

/-- The actual interval primitive of a locally integrable function. -/
def intervalWeakPrimitive (x₀ : ℝ) (g : ℝ → ℝ) (x : ℝ) : ℝ :=
  ∫ t in x₀..x, g t

theorem intervalIntegrable_of_locallyIntegrableOn_Ioo {a b x y : ℝ} {g : ℝ → ℝ}
    (hg : LocallyIntegrableOn g (Ioo a b)) (hx : x ∈ Ioo a b) (hy : y ∈ Ioo a b) :
    IntervalIntegrable g volume x y :=
  intervalIntegrable_iff.mpr
    ((hg.integrableOn_compact_subset (ordConnected_Ioo.uIcc_subset hx hy) isCompact_uIcc).mono_set
      uIoc_subset_uIcc)

/-- The primitive is absolutely continuous on every compact subinterval,
even when the chosen base point is outside that smaller interval. -/
theorem intervalWeakPrimitive_absolutelyContinuous {a b x₀ l r : ℝ} {g : ℝ → ℝ}
    (hg : LocallyIntegrableOn g (Ioo a b)) (hx₀ : x₀ ∈ Ioo a b)
    (hl : l ∈ Ioo a b) (hr : r ∈ Ioo a b) :
    AbsolutelyContinuousOnInterval (intervalWeakPrimitive x₀ g) l r := by
  let L : ℝ := min x₀ (min l r)
  let R : ℝ := max x₀ (max l r)
  have hL : L ∈ Ioo a b :=
    ⟨lt_min hx₀.1 (lt_min hl.1 hr.1), (min_le_left _ _).trans_lt hx₀.2⟩
  have hR : R ∈ Ioo a b :=
    ⟨hx₀.1.trans_le (le_max_left _ _), max_lt hx₀.2 (max_lt hl.2 hr.2)⟩
  have hLR : L ≤ R := (min_le_left _ _).trans (le_max_left _ _)
  have hx₀LR : x₀ ∈ uIcc L R := by
    rw [uIcc_of_le hLR]
    exact ⟨min_le_left _ _, le_max_left _ _⟩
  have hsub : uIcc l r ⊆ uIcc L R := by
    rw [uIcc_of_le hLR]
    intro x hx
    exact ⟨(min_le_right _ _).trans hx.1, hx.2.trans (le_max_right _ _)⟩
  exact ((intervalIntegrable_of_locallyIntegrableOn_Ioo hg hL hR).
    absolutelyContinuousOnInterval_intervalIntegral hx₀LR).mono hsub

theorem continuousOn_intervalWeakPrimitive {a b x₀ : ℝ} {g : ℝ → ℝ}
    (hg : LocallyIntegrableOn g (Ioo a b)) (hx₀ : x₀ ∈ Ioo a b) :
    ContinuousOn (intervalWeakPrimitive x₀ g) (Ioo a b) := by
  intro x hx
  obtain ⟨l, hal, hlx⟩ := exists_between hx.1
  obtain ⟨r, hxr, hrb⟩ := exists_between hx.2
  have hAC := intervalWeakPrimitive_absolutelyContinuous hg hx₀
    ⟨hal, hlx.trans hx.2⟩ ⟨hx.1.trans hxr, hrb⟩
  have hcont : ContinuousOn (intervalWeakPrimitive x₀ g) (Icc l r) := by
    simpa only [uIcc_of_le (hlx.trans hxr).le] using hAC.continuousOn
  exact (hcont.continuousAt (Icc_mem_nhds hlx hxr)).continuousWithinAt

private theorem interval_test_integral_eq {l r : ℝ} (hlr : l ≤ r)
    (F ψ : ℝ → ℝ) (hs : Function.support ψ ⊆ Ioo l r) :
    (∫ x, F x * ψ x) = ∫ x in l..r, F x * ψ x := by
  rw [intervalIntegral.integral_of_le hlr]
  symm
  apply setIntegral_eq_integral_of_forall_compl_eq_zero
  intro x hx
  have hψ : ψ x = 0 := Function.notMem_support.mp
    (fun h => hx ⟨(hs h).1, (hs h).2.le⟩)
  rw [hψ, mul_zero]

/-- Integration by parts for the locally absolutely continuous primitive.
Only local integrability of the derivative is required. -/
theorem intervalWeakPrimitive_weakDerivative {a b x₀ : ℝ} {g : ℝ → ℝ}
    (hg : LocallyIntegrableOn g (Ioo a b)) (hx₀ : x₀ ∈ Ioo a b) :
    HasIntervalWeakDerivative a b (intervalWeakPrimitive x₀ g) g := by
  intro ψ hψ hcψ hsψ
  have hK : IsCompact (tsupport ψ ∪ {x₀}) := hcψ.union isCompact_singleton
  have hsK : tsupport ψ ∪ {x₀} ⊆ Ioo a b :=
    union_subset hsψ (singleton_subset_iff.mpr hx₀)
  obtain ⟨l, r, hal, hlr, hrb, hsmall⟩ :=
    interval_compact_subset_Ioo (hx₀.1.trans hx₀.2) hK hsK
  have hψsmall : tsupport ψ ⊆ Ioo l r := subset_union_left.trans hsmall
  have hx₀small : x₀ ∈ Ioo l r := hsmall (Or.inr (by simp))
  have hl : l ∈ Ioo a b := ⟨hal, hlr.trans hrb⟩
  have hr : r ∈ Ioo a b := ⟨hal.trans hlr, hrb⟩
  have hgi := intervalIntegrable_of_locallyIntegrableOn_Ioo hg hl hr
  have hx₀cc : x₀ ∈ uIcc l r := by
    rw [uIcc_of_le hlr.le]
    exact ⟨hx₀small.1.le, hx₀small.2.le⟩
  have hPAC : AbsolutelyContinuousOnInterval (intervalWeakPrimitive x₀ g) l r :=
    hgi.absolutelyContinuousOnInterval_intervalIntegral hx₀cc
  have hψAC : AbsolutelyContinuousOnInterval ψ l r :=
    (show ContDiff ℝ 1 ψ from hψ.of_le (by simp)).contDiffOn.absolutelyContinuousOnInterval
  have hψl : ψ l = 0 := image_eq_zero_of_notMem_tsupport
    (fun h => (lt_irrefl l) (hψsmall h).1)
  have hψr : ψ r = 0 := image_eq_zero_of_notMem_tsupport
    (fun h => (lt_irrefl r) (hψsmall h).2)
  have hibp := hPAC.integral_mul_deriv_eq_deriv_mul hψAC
  simp only [hψl, hψr, mul_zero, sub_zero, zero_sub] at hibp
  have hder : (∫ x in l..r, deriv (intervalWeakPrimitive x₀ g) x * ψ x) =
      ∫ x in l..r, g x * ψ x := by
    apply intervalIntegral.integral_congr_ae
    filter_upwards [hgi.ae_hasDerivAt_integral] with x hx hxin
    rw [(hx (uIoc_subset_uIcc hxin) x₀ hx₀cc).deriv]
  rw [hder] at hibp
  rw [interval_test_integral_eq hlr.le _ _ (support_deriv_subset.trans hψsmall),
    interval_test_integral_eq hlr.le _ _ ((subset_tsupport ψ).trans hψsmall)]
  exact hibp

/-- The weak derivative identity determines the integral representative up
to one constant throughout the whole connected interval. -/
theorem exists_intervalWeakPrimitive_rep {a b x₀ : ℝ} {f g : ℝ → ℝ}
    (hf : LocallyIntegrableOn f (Ioo a b)) (hg : LocallyIntegrableOn g (Ioo a b))
    (hx₀ : x₀ ∈ Ioo a b) (hweak : HasIntervalWeakDerivative a b f g) :
    ∃ c : ℝ, f =ᵐ[volume.restrict (Ioo a b)] fun x => c + intervalWeakPrimitive x₀ g x := by
  have hPcont := continuousOn_intervalWeakPrimitive hg hx₀
  have hPloc := hPcont.locallyIntegrableOn measurableSet_Ioo
  have hPweak := intervalWeakPrimitive_weakDerivative hg hx₀
  let k : ℝ → ℝ := fun x => f x - intervalWeakPrimitive x₀ g x
  have hk : LocallyIntegrableOn k (Ioo a b) := hf.sub hPloc
  have hkzero : ∀ ψ : ℝ → ℝ, ContDiff ℝ ∞ ψ → HasCompactSupport ψ →
      tsupport ψ ⊆ Ioo a b → (∫ x, k x * deriv ψ x) = 0 := by
    intro ψ hψ hcψ hsψ
    have hdψ : ContDiff ℝ ∞ (deriv ψ) := (contDiff_infty_iff_deriv.mp hψ).2
    have hsD : tsupport (deriv ψ) ⊆ Ioo a b := tsupport_deriv_subset.trans hsψ
    have hfi := interval_integrable_mul_test hf hdψ.continuous hcψ.deriv hsD
    have hPi := interval_integrable_mul_test hPloc hdψ.continuous hcψ.deriv hsD
    change (∫ x, (f x - intervalWeakPrimitive x₀ g x) * deriv ψ x) = 0
    simp_rw [sub_mul]
    rw [integral_sub hfi hPi, hweak ψ hψ hcψ hsψ, hPweak ψ hψ hcψ hsψ, sub_self]
  obtain ⟨c, hc⟩ := interval_ae_constant_of_integral_deriv_zero
    (hx₀.1.trans hx₀.2) hk hkzero
  refine ⟨c, ?_⟩
  filter_upwards [hc] with x hx
  change f x - intervalWeakPrimitive x₀ g x = c at hx
  linarith only [hx]

/-- A weakly differentiable function has a continuous representative that is
absolutely continuous on every compact subinterval. -/
theorem exists_interval_weakDerivative_representative {a b x₀ : ℝ} {f g : ℝ → ℝ}
    (hf : LocallyIntegrableOn f (Ioo a b)) (hg : LocallyIntegrableOn g (Ioo a b))
    (hx₀ : x₀ ∈ Ioo a b) (hweak : HasIntervalWeakDerivative a b f g) :
    ∃ c : ℝ, ∃ F : ℝ → ℝ,
      ContinuousOn F (Ioo a b) ∧
      (∀ l ∈ Ioo a b, ∀ r ∈ Ioo a b, AbsolutelyContinuousOnInterval F l r) ∧
      (∀ x, F x = c + ∫ t in x₀..x, g t) ∧
      f =ᵐ[volume.restrict (Ioo a b)] F := by
  obtain ⟨c, hc⟩ := exists_intervalWeakPrimitive_rep hf hg hx₀ hweak
  refine ⟨c, fun x => c + intervalWeakPrimitive x₀ g x,
    continuousOn_const.add (continuousOn_intervalWeakPrimitive hg hx₀), ?_, fun _ => rfl, hc⟩
  intro l hl r hr
  have hconst : AbsolutelyContinuousOnInterval (fun _ : ℝ => c) l r :=
    (contDiff_const : ContDiff ℝ 1 (fun _ : ℝ => c)).contDiffOn.absolutelyContinuousOnInterval
  exact hconst.fun_add (intervalWeakPrimitive_absolutelyContinuous hg hx₀ hl hr)

/-- A continuous weak derivative is the pointwise classical derivative of
the integral representative at every interior point. -/
theorem hasDerivAt_intervalWeakPrimitive {a b x₀ x : ℝ} {g : ℝ → ℝ}
    (hg : ContinuousOn g (Ioo a b)) (hx₀ : x₀ ∈ Ioo a b) (hx : x ∈ Ioo a b) :
    HasDerivAt (intervalWeakPrimitive x₀ g) (g x) x :=
  intervalIntegral.integral_hasDerivAt_right
    (ContinuousOn.intervalIntegrable (hg.mono (ordConnected_Ioo.uIcc_subset hx₀ hx)))
    (hg.stronglyMeasurableAtFilter isOpen_Ioo x hx)
    (hg.continuousAt (isOpen_Ioo.mem_nhds hx))

theorem exists_interval_classical_rep {a b x₀ : ℝ} {f g : ℝ → ℝ}
    (hf : LocallyIntegrableOn f (Ioo a b)) (hg : ContinuousOn g (Ioo a b))
    (hx₀ : x₀ ∈ Ioo a b) (hweak : HasIntervalWeakDerivative a b f g) :
    ∃ c : ℝ, ∃ F : ℝ → ℝ,
      (∀ x, F x = c + ∫ t in x₀..x, g t) ∧
      f =ᵐ[volume.restrict (Ioo a b)] F ∧
      (∀ x ∈ Ioo a b, HasDerivAt F (g x) x) := by
  obtain ⟨c, hc⟩ := exists_intervalWeakPrimitive_rep hf
    (hg.locallyIntegrableOn measurableSet_Ioo) hx₀ hweak
  refine ⟨c, fun x => c + intervalWeakPrimitive x₀ g x, fun _ => rfl, hc, ?_⟩
  intro x hx
  simpa only [zero_add] using
    (hasDerivAt_const x c).add (hasDerivAt_intervalWeakPrimitive hg hx₀ hx)

end ContinuousFlexibility.Analysis
