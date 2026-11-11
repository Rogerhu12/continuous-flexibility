import ContinuousFlexibility.Analysis.IntervalWeakPrimitive

/-!
# Recovering pointwise derivatives from locally absolutely continuous states

The source primitive has its expected derivative almost everywhere.  When
an absolutely continuous expression has a continuous candidate derivative,
the fundamental theorem of calculus upgrades that derivative to every
interior point.  This applies to the cancellation in variation of parameters
for merely locally integrable forcing.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter MeasureTheory
open scoped Topology

/-- The weak primitive has its expected derivative almost everywhere on
each compact subinterval, even if its base point lies outside that subinterval. -/
theorem intervalWeakPrimitive_ae_hasDerivAt_on {a b c l r : ℝ} {g : ℝ → ℝ}
    (hg : LocallyIntegrableOn g (Ioo a b)) (hc : c ∈ Ioo a b)
    (hl : l ∈ Ioo a b) (hr : r ∈ Ioo a b) :
    ∀ᵐ x ∂volume, x ∈ uIcc l r → HasDerivAt (intervalWeakPrimitive c g) (g x) x := by
  let L : ℝ := min c (min l r)
  let R : ℝ := max c (max l r)
  have hL : L ∈ Ioo a b :=
    ⟨lt_min hc.1 (lt_min hl.1 hr.1), (min_le_left _ _).trans_lt hc.2⟩
  have hR : R ∈ Ioo a b :=
    ⟨hc.1.trans_le (le_max_left _ _), max_lt hc.2 (max_lt hl.2 hr.2)⟩
  have hLR : L ≤ R := (min_le_left _ _).trans (le_max_left _ _)
  have hcLR : c ∈ uIcc L R := by
    rw [uIcc_of_le hLR]
    exact ⟨min_le_left _ _, le_max_left _ _⟩
  have hsub : uIcc l r ⊆ uIcc L R := by
    rw [uIcc_of_le hLR]
    intro x hx
    exact ⟨(min_le_right _ _).trans hx.1, hx.2.trans (le_max_right _ _)⟩
  have hi := intervalIntegrable_of_locallyIntegrableOn_Ioo hg hL hR
  filter_upwards [hi.ae_hasDerivAt_integral] with x hx hxin
  exact hx (hsub hxin) c hcLR

/-- An almost-everywhere continuous derivative of a locally absolutely
continuous function is its derivative at every interior point. -/
theorem hasDerivAt_of_locallyAC_ae {a b : ℝ} {f g : ℝ → ℝ}
    (hAC : ∀ l ∈ Ioo a b, ∀ r ∈ Ioo a b, AbsolutelyContinuousOnInterval f l r)
    (hg : ContinuousOn g (Ioo a b))
    (hder : ∀ l ∈ Ioo a b, ∀ r ∈ Ioo a b,
      ∀ᵐ x ∂volume, x ∈ uIcc l r → HasDerivAt f (g x) x) :
    ∀ x ∈ Ioo a b, HasDerivAt f (g x) x := by
  intro x hx
  obtain ⟨l, hal, hlx⟩ := exists_between hx.1
  obtain ⟨r, hxr, hrb⟩ := exists_between hx.2
  have hl : l ∈ Ioo a b := ⟨hal, hlx.trans hx.2⟩
  have hr : r ∈ Ioo a b := ⟨hx.1.trans hxr, hrb⟩
  have hlr : l < r := hlx.trans hxr
  have hsub : uIcc l r ⊆ Ioo a b := ordConnected_Ioo.uIcc_subset hl hr
  have hxmem : x ∈ uIcc l r := by
    rw [uIcc_of_le hlr.le]
    exact ⟨hlx.le, hxr.le⟩
  have hPAC := intervalWeakPrimitive_absolutelyContinuous
    (hg.locallyIntegrableOn measurableSet_Ioo) hx hl hr
  have hzero : ∀ᵐ y ∂volume, y ∈ uIcc l r →
      HasDerivAt (fun t => f t - intervalWeakPrimitive x g t) 0 y := by
    filter_upwards [hder l hl r hr] with y hy hymem
    exact ((hy hymem).sub
      (hasDerivAt_intervalWeakPrimitive hg hx (hsub hymem))).congr_deriv (by ring)
  obtain ⟨C, hC⟩ := ((hAC l hl r hr).sub hPAC).const_of_ae_hasDerivAt_zero hzero
  have hCx : f x = C := by
    simpa only [Pi.sub_apply, intervalWeakPrimitive, intervalIntegral.integral_same, sub_zero] using hC x hxmem
  have hclass : HasDerivAt (fun t => f x + intervalWeakPrimitive x g t) (g x) x :=
    (hasDerivAt_intervalWeakPrimitive hg hx hx).const_add (f x)
  apply hclass.congr_of_eventuallyEq
  filter_upwards [Ioo_mem_nhds hlx hxr] with y hy
  have hymem : y ∈ uIcc l r := by
    rw [uIcc_of_le hlr.le]
    exact ⟨hy.1.le, hy.2.le⟩
  have hCy := hC y hymem
  change f y - intervalWeakPrimitive x g y = C at hCy
  linarith

private theorem integral_mul_eq_interval_of_support {l r : ℝ} (hlr : l ≤ r)
    (F ψ : ℝ → ℝ) (hs : Function.support ψ ⊆ Ioo l r) :
    (∫ x, F x * ψ x) = ∫ x in l..r, F x * ψ x := by
  rw [intervalIntegral.integral_of_le hlr]
  symm
  apply setIntegral_eq_integral_of_forall_compl_eq_zero
  intro x hx
  have hψ : ψ x = 0 := Function.notMem_support.mp
    (fun h => hx ⟨(hs h).1, (hs h).2.le⟩)
  rw [hψ, mul_zero]

/-- A locally absolutely continuous state satisfies the weak derivative
identity with its almost-everywhere derivative. -/
theorem hasIntervalWeakDerivative_of_locallyAC_ae {a b : ℝ} {f g : ℝ → ℝ}
    (hab : a < b)
    (hAC : ∀ l ∈ Ioo a b, ∀ r ∈ Ioo a b, AbsolutelyContinuousOnInterval f l r)
    (hder : ∀ l ∈ Ioo a b, ∀ r ∈ Ioo a b,
      ∀ᵐ x ∂volume, x ∈ uIcc l r → HasDerivAt f (g x) x) :
    HasIntervalWeakDerivative a b f g := by
  intro ψ hψ hc hs
  obtain ⟨l, r, hal, hlr, hrb, hsmall⟩ := interval_compact_subset_Ioo hab hc hs
  have hl : l ∈ Ioo a b := ⟨hal, hlr.trans hrb⟩
  have hr : r ∈ Ioo a b := ⟨hal.trans hlr, hrb⟩
  have hψAC : AbsolutelyContinuousOnInterval ψ l r :=
    (show ContDiff ℝ 1 ψ from hψ.of_le (by simp)).contDiffOn.absolutelyContinuousOnInterval
  have hψl : ψ l = 0 := image_eq_zero_of_notMem_tsupport
    (fun h => (lt_irrefl l) (hsmall h).1)
  have hψr : ψ r = 0 := image_eq_zero_of_notMem_tsupport
    (fun h => (lt_irrefl r) (hsmall h).2)
  have hibp := (hAC l hl r hr).integral_mul_deriv_eq_deriv_mul hψAC
  simp only [hψl, hψr, mul_zero, sub_zero, zero_sub] at hibp
  have hderInt : (∫ x in l..r, deriv f x * ψ x) = ∫ x in l..r, g x * ψ x := by
    apply intervalIntegral.integral_congr_ae
    filter_upwards [hder l hl r hr] with x hx hxin
    rw [(hx (uIoc_subset_uIcc hxin)).deriv]
  rw [hderInt] at hibp
  rw [integral_mul_eq_interval_of_support hlr.le _ _
      (support_deriv_subset.trans hsmall),
    integral_mul_eq_interval_of_support hlr.le _ _ ((subset_tsupport ψ).trans hsmall)]
  exact hibp

end ContinuousFlexibility.Analysis
