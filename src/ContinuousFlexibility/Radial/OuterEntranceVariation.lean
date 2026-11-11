import ContinuousFlexibility.Radial.OuterIntegrableFlux
import ContinuousFlexibility.Radial.TailFundamentalGreenRepresentation

/-!
# The actual one-sided entrance trace of the outer Green solution

The source need only be locally integrable, with integrable initial
segments from the entrance.  Recentring the same integral formula at an
interior point proves its value and flux equations.  Continuity of the
initial primitives then gives the genuine one-sided derivative at the
entrance, and hence both normalized Robin traces.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open Set Filter MeasureTheory
open scoped Topology
open ContinuousFlexibility.Analysis

private theorem initialPrimitive_rebase {a b c x : ℝ} {g : ℝ → ℝ}
    (hg : LocallyIntegrableOn g (Ioo a b))
    (hi : ∀ y ∈ Ioo a b, IntervalIntegrable g volume a y)
    (hc : c ∈ Ioo a b) (hx : x ∈ Ioo a b) :
    (∫ t in a..x, g t) = (∫ t in a..c, g t) + ∫ t in c..x, g t :=
  (intervalIntegral.integral_add_adjacent_intervals (hi c hc)
    (intervalIntegrable_of_locallyIntegrableOn_Ioo hg hc hx)).symm

/-- The primitive based at the actual entrance is continuous up to it. -/
theorem continuousOn_initialPrimitive {a b : ℝ} {g : ℝ → ℝ}
    (hi : ∀ x ∈ Ioo a b, IntervalIntegrable g volume a x) :
    ContinuousOn (fun x => ∫ t in a..x, g t) (Ico a b) := by
  intro x hx
  obtain ⟨r, hxr, hrb⟩ := exists_between hx.2
  have har : a < r := hx.1.trans_lt hxr
  have ha : a ∈ uIcc a r := by
    rw [uIcc_of_le har.le]
    exact ⟨le_rfl, har.le⟩
  have hAC := (hi r ⟨har, hrb⟩).absolutelyContinuousOnInterval_intervalIntegral ha
  have hcont : ContinuousOn (fun y => ∫ t in a..y, g t) (Icc a r) := by
    simpa only [uIcc_of_le har.le] using hAC.continuousOn
  apply (hcont x ⟨hx.1, hxr.le⟩).mono_of_mem_nhdsWithin
  filter_upwards [self_mem_nhdsWithin,
    (eventually_lt_nhds hxr).filter_mono nhdsWithin_le_nhds] with y hy hyr
  exact ⟨hy.1, hyr.le⟩

/-- Recentring changes only the two scalar coefficients in the existing
variation-of-parameters formula. -/
theorem outerSolution_rebase_from_left {a b lam cA cB c : ℝ} {U V f : ℝ → ℝ}
    (hU : ContinuousOn U (Ioo a b)) (hV : ContinuousOn V (Ioo a b))
    (hf : LocallyIntegrableOn f (Ioo a b))
    (hUi : ∀ x ∈ Ioo a b, IntervalIntegrable (fun t => U t * f t) volume a x)
    (hVi : ∀ x ∈ Ioo a b, IntervalIntegrable (fun t => V t * f t) volume a x)
    (hc : c ∈ Ioo a b) :
    EqOn (outerSolution lam cA cB a U V f)
      (outerSolution lam (cA + ∫ t in a..c, U t * f t)
        (cB - ∫ t in a..c, V t * f t) c U V f) (Ioo a b) := by
  intro x hx
  have hA := initialPrimitive_rebase
    (hf.continuousOn_mul hU isOpen_Ioo.isLocallyClosed) hUi hc hx
  have hB := initialPrimitive_rebase
    (hf.continuousOn_mul hV isOpen_Ioo.isLocallyClosed) hVi hc hx
  unfold outerSolution
  rw [hA, hB]
  ring

/-- Interior differentiability for a source integrated from the entrance. -/
theorem hasDerivAt_outerSolution_from_left {a b lam cA cB : ℝ} {U V f : ℝ → ℝ}
    (hU : ContDiffOn ℝ 1 U (Ioo a b)) (hV : ContDiffOn ℝ 1 V (Ioo a b))
    (hf : LocallyIntegrableOn f (Ioo a b))
    (hUi : ∀ x ∈ Ioo a b, IntervalIntegrable (fun t => U t * f t) volume a x)
    (hVi : ∀ x ∈ Ioo a b, IntervalIntegrable (fun t => V t * f t) volume a x) :
    ∀ x ∈ Ioo a b, HasDerivAt (outerSolution lam cA cB a U V f)
      (-(1 / lam) * (deriv V x * (cA + ∫ t in a..x, U t * f t) +
        deriv U x * (cB - ∫ t in a..x, V t * f t))) x := by
  intro x hx
  have hd := hasDerivAt_outerSolution_locallyIntegrable (lam := lam)
    (cA := cA + ∫ t in a..x, U t * f t) (cB := cB - ∫ t in a..x, V t * f t)
    hU hV hf hx x hx
  simp only [intervalIntegral.integral_same, add_zero, sub_zero] at hd
  apply hd.congr_of_eventuallyEq
  filter_upwards [isOpen_Ioo.mem_nhds hx] with y hy
  exact outerSolution_rebase_from_left hU.continuousOn hV.continuousOn hf hUi hVi hx hy

/-- The flux expression is the actual derivative flux throughout the open interval. -/
theorem outerSolutionFlux_eq_from_left {a b lam cA cB : ℝ} {w U V f : ℝ → ℝ}
    (hU : ContDiffOn ℝ 1 U (Ioo a b)) (hV : ContDiffOn ℝ 1 V (Ioo a b))
    (hf : LocallyIntegrableOn f (Ioo a b))
    (hUi : ∀ x ∈ Ioo a b, IntervalIntegrable (fun t => U t * f t) volume a x)
    (hVi : ∀ x ∈ Ioo a b, IntervalIntegrable (fun t => V t * f t) volume a x) :
    ∀ x ∈ Ioo a b, outerSolutionFlux lam cA cB a w U V f x =
      w x * deriv (outerSolution lam cA cB a U V f) x := by
  intro x hx
  rw [(hasDerivAt_outerSolution_from_left hU hV hf hUi hVi x hx).deriv]
  unfold outerSolutionFlux
  ring

/-- The exact one-sided state at the entrance is a scalar multiple of the
left homogeneous state; no source regularity at that endpoint is assumed. -/
theorem outerSolution_entrance_state {a b lam cB : ℝ} {w U V f : ℝ → ℝ}
    (hab : a < b)
    (hU : ContDiffOn ℝ 1 U (Ioo a b)) (hV : ContDiffOn ℝ 1 V (Ioo a b))
    (hUc : ContinuousOn U (Ico a b)) (hVc : ContinuousOn V (Ico a b))
    (hDU : ContinuousOn (deriv U) (Ico a b)) (hDV : ContinuousOn (deriv V) (Ico a b))
    (hf : LocallyIntegrableOn f (Ioo a b))
    (hUi : ∀ x ∈ Ioo a b, IntervalIntegrable (fun t => U t * f t) volume a x)
    (hVi : ∀ x ∈ Ioo a b, IntervalIntegrable (fun t => V t * f t) volume a x) :
    (outerSolution lam 0 cB a U V f a,
      w a * derivWithin (outerSolution lam 0 cB a U V f) (Ico a b) a / lam) =
      (-(cB / lam)) • outerFluxState lam w U a := by
  have hA : ContinuousOn (fun x => 0 + ∫ t in a..x, U t * f t) (Ico a b) :=
    continuousOn_const.add (continuousOn_initialPrimitive hUi)
  have hB : ContinuousOn (fun x => cB - ∫ t in a..x, V t * f t) (Ico a b) :=
    continuousOn_const.sub (continuousOn_initialPrimitive hVi)
  have hvalue : ContinuousOn (outerSolution lam 0 cB a U V f) (Ico a b) :=
    continuousOn_const.mul ((hVc.mul hA).add (hUc.mul hB))
  have hderivative : ContinuousOn (fun x => -(1 / lam) *
      (deriv V x * (0 + ∫ t in a..x, U t * f t) +
        deriv U x * (cB - ∫ t in a..x, V t * f t))) (Ico a b) :=
    continuousOn_const.mul ((hDV.mul hA).add (hDU.mul hB))
  have hwithin := tail_hasDerivWithinAt_Ico_of_continuous hab hvalue hderivative
    (hasDerivAt_outerSolution_from_left hU hV hf hUi hVi) a ⟨le_rfl, hab⟩
  have hd := hwithin.derivWithin (uniqueDiffOn_Ico a b a ⟨le_rfl, hab⟩)
  apply Prod.ext
  · exact outerSolution_base
  · change w a * derivWithin (outerSolution lam 0 cB a U V f) (Ico a b) a / lam =
      (-(cB / lam)) * (w a * deriv U a / lam)
    rw [hd]
    simp only [intervalIntegral.integral_same]
    ring

/-- The normalized Robin trace and its complementary trace for the actual
one-sided entrance state. -/
theorem outerSolution_entrance_traces {a b lam cB : ℝ} {w U V f : ℝ → ℝ}
    {v : ℝ × ℝ} (hab : a < b) (hv : v.1 ^ 2 + v.2 ^ 2 = 1)
    (hU : ContDiffOn ℝ 1 U (Ioo a b)) (hV : ContDiffOn ℝ 1 V (Ioo a b))
    (hUc : ContinuousOn U (Ico a b)) (hVc : ContinuousOn V (Ico a b))
    (hDU : ContinuousOn (deriv U) (Ico a b)) (hDV : ContinuousOn (deriv V) (Ico a b))
    (hf : LocallyIntegrableOn f (Ioo a b))
    (hUi : ∀ x ∈ Ioo a b, IntervalIntegrable (fun t => U t * f t) volume a x)
    (hVi : ∀ x ∈ Ioo a b, IntervalIntegrable (fun t => V t * f t) volume a x)
    (hstate : outerFluxState lam w U a = outerStatePerp v) :
    let state := (outerSolution lam 0 cB a U V f a,
      w a * derivWithin (outerSolution lam 0 cB a U V f) (Ico a b) a / lam)
    outerStatePair v state = 0 ∧ outerStatePair (outerStatePerp v) state = -(cB / lam) := by
  dsimp only
  rw [outerSolution_entrance_state hab hU hV hUc hVc hDU hDV hf hUi hVi, hstate]
  constructor
  · change v.1 * (-(cB / lam) * (-v.2)) + v.2 * (-(cB / lam) * v.1) = 0
    ring
  · change (-v.2) * (-(cB / lam) * (-v.2)) + v.1 * (-(cB / lam) * v.1) = -(cB / lam)
    nlinarith [congrArg (fun t : ℝ => -(cB / lam) * t) hv]

private theorem outerSolutionFlux_rebase_from_left
    {a b lam cA cB c : ℝ} {w U V f : ℝ → ℝ}
    (hU : ContinuousOn U (Ioo a b)) (hV : ContinuousOn V (Ioo a b))
    (hf : LocallyIntegrableOn f (Ioo a b))
    (hUi : ∀ x ∈ Ioo a b, IntervalIntegrable (fun t => U t * f t) volume a x)
    (hVi : ∀ x ∈ Ioo a b, IntervalIntegrable (fun t => V t * f t) volume a x)
    (hc : c ∈ Ioo a b) :
    EqOn (outerSolutionFlux lam cA cB a w U V f)
      (outerSolutionFlux lam (cA + ∫ t in a..c, U t * f t)
        (cB - ∫ t in a..c, V t * f t) c w U V f) (Ioo a b) := by
  intro x hx
  have hA := initialPrimitive_rebase
    (hf.continuousOn_mul hU isOpen_Ioo.isLocallyClosed) hUi hc hx
  have hB := initialPrimitive_rebase
    (hf.continuousOn_mul hV isOpen_Ioo.isLocallyClosed) hVi hc hx
  unfold outerSolutionFlux
  rw [hA, hB]
  ring

/-- The actual entrance-based solution satisfies the radial equation weakly. -/
theorem outerSolutionFlux_weakDerivative_from_left
    {a b J lam cA cB : ℝ} {w U V f : ℝ → ℝ}
    (hab : a < b) (hw : ContDiffOn ℝ 1 w (Ioo a b))
    (hU : ContDiffOn ℝ 2 U (Ioo a b)) (hV : ContDiffOn ℝ 2 V (Ioo a b))
    (hUeq : ∀ x ∈ Ioo a b, radialJacobi J w U x = 0)
    (hVeq : ∀ x ∈ Ioo a b, radialJacobi J w V x = 0)
    (hW : ∀ x ∈ Ioo a b, radialWronskian w U V x = -lam)
    (hlam : lam ≠ 0) (hf : LocallyIntegrableOn f (Ioo a b))
    (hUi : ∀ x ∈ Ioo a b, IntervalIntegrable (fun t => U t * f t) volume a x)
    (hVi : ∀ x ∈ Ioo a b, IntervalIntegrable (fun t => V t * f t) volume a x) :
    HasIntervalWeakDerivative a b (outerSolutionFlux lam cA cB a w U V f)
      (fun x => J * deriv w x / x * outerSolution lam cA cB a U V f x + f x) := by
  obtain ⟨c, hc⟩ := nonempty_Ioo.mpr hab
  let A : ℝ := cA + ∫ t in a..c, U t * f t
  let B : ℝ := cB - ∫ t in a..c, V t * f t
  have hvalue : EqOn (outerSolution lam cA cB a U V f)
      (outerSolution lam A B c U V f) (Ioo a b) :=
    outerSolution_rebase_from_left hU.continuousOn hV.continuousOn hf hUi hVi hc
  have hflux : EqOn (outerSolutionFlux lam cA cB a w U V f)
      (outerSolutionFlux lam A B c w U V f) (Ioo a b) :=
    outerSolutionFlux_rebase_from_left hU.continuousOn hV.continuousOn hf hUi hVi hc
  have hweak := outerSolutionFlux_weakDerivative (cA := A) (cB := B)
    hw hU hV hUeq hVeq hW hlam hf hc
  intro ψ hψ hcψ hsψ
  change (∫ x, outerSolutionFlux lam cA cB a w U V f x * deriv ψ x) =
    -(∫ x, (J * deriv w x / x * outerSolution lam cA cB a U V f x + f x) * ψ x)
  have hleft :
      (∫ x, outerSolutionFlux lam cA cB a w U V f x * deriv ψ x) =
        ∫ x, outerSolutionFlux lam A B c w U V f x * deriv ψ x := by
    apply integral_congr_ae
    apply Eventually.of_forall
    intro x
    dsimp only
    by_cases hx : x ∈ Ioo a b
    · rw [hflux hx]
    · have hz : deriv ψ x = 0 :=
        Function.notMem_support.mp (fun h => hx (hsψ (support_deriv_subset h)))
      rw [hz, mul_zero, mul_zero]
  have hright :
      (∫ x, (J * deriv w x / x * outerSolution lam cA cB a U V f x + f x) * ψ x) =
        ∫ x, (J * deriv w x / x * outerSolution lam A B c U V f x + f x) * ψ x := by
    apply integral_congr_ae
    apply Eventually.of_forall
    intro x
    dsimp only
    by_cases hx : x ∈ Ioo a b
    · rw [hvalue hx]
    · have hz : ψ x = 0 :=
        Function.notMem_support.mp (fun h => hx (hsψ ((subset_tsupport ψ) h)))
      rw [hz, mul_zero, mul_zero]
  rw [hleft, hright]
  exact hweak ψ hψ hcψ hsψ

end ContinuousFlexibility.Radial
