import ContinuousFlexibility.Radial.CentralRadiusGrowth
import ContinuousFlexibility.Radial.CentralPositionInverse
import ContinuousFlexibility.Radial.CentralReducedPositionInverse

/-!
# The actual central radial weight on the genuine inverse

The geometric weight is the actual logarithmic derivative `nu = R'/R`.
Its decomposition into bounded measurable multipliers and the genuine
position multiplier transfers the already proved physical position
estimates to the same central inverse. No inverse existence is assumed.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open Real Set Filter MeasureTheory
open scoped Topology RealInnerProductSpace InnerProductSpace

set_option backward.isDefEq.respectTransparency false

private theorem boundedScalarProduct_memLp (a : ℝ → ℝ) (ha : Measurable a)
    (C : ℝ) (hbound : ∀ x, |a x| ≤ C) (f : HermiteL2) :
    MemLp (fun x : ℝ => a x * f x) 2 volume := by
  apply (Lp.memLp f).of_le_mul (c := C)
    (ha.aestronglyMeasurable.mul (Lp.memLp f).aestronglyMeasurable)
  apply Eventually.of_forall
  intro x
  change ‖a x * f x‖ ≤ C * ‖f x‖
  rw [norm_mul, Real.norm_eq_abs]
  exact mul_le_mul_of_nonneg_right (hbound x) (norm_nonneg _)

private def boundedScalarMultiplierValue (a : ℝ → ℝ) (ha : Measurable a)
    (C : ℝ) (hbound : ∀ x, |a x| ≤ C) (f : HermiteL2) : HermiteL2 :=
  (boundedScalarProduct_memLp a ha C hbound f).toLp (fun x => a x * f x)

private theorem boundedScalarMultiplierValue_ae (a : ℝ → ℝ) (ha : Measurable a)
    (C : ℝ) (hbound : ∀ x, |a x| ≤ C) (f : HermiteL2) :
    (boundedScalarMultiplierValue a ha C hbound f : ℝ → ℝ) =ᵐ[volume]
      (fun x => a x * f x) :=
  MemLp.coeFn_toLp _

private theorem boundedScalarMultiplierValue_bound (a : ℝ → ℝ) (ha : Measurable a)
    (C : ℝ) (hbound : ∀ x, |a x| ≤ C) (f : HermiteL2) :
    ‖boundedScalarMultiplierValue a ha C hbound f‖ ≤ C * ‖f‖ := by
  apply Lp.norm_le_mul_norm_of_ae_le_mul
  filter_upwards [boundedScalarMultiplierValue_ae a ha C hbound f] with x hx
  rw [hx, norm_mul, Real.norm_eq_abs]
  exact mul_le_mul_of_nonneg_right (hbound x) (norm_nonneg _)

private def boundedScalarMultiplierLinear (a : ℝ → ℝ) (ha : Measurable a)
    (C : ℝ) (hbound : ∀ x, |a x| ≤ C) : HermiteL2 →ₗ[ℝ] HermiteL2 where
  toFun := boundedScalarMultiplierValue a ha C hbound
  map_add' f g := by
    apply Lp.ext
    filter_upwards [boundedScalarMultiplierValue_ae a ha C hbound (f + g),
      boundedScalarMultiplierValue_ae a ha C hbound f,
      boundedScalarMultiplierValue_ae a ha C hbound g,
      Lp.coeFn_add f g,
      Lp.coeFn_add (boundedScalarMultiplierValue a ha C hbound f)
        (boundedScalarMultiplierValue a ha C hbound g)] with x hs hf hg hin hout
    rw [hs, hout, hin]
    simp only [Pi.add_apply]
    rw [hf, hg]
    ring
  map_smul' r f := by
    change boundedScalarMultiplierValue a ha C hbound (r • f) =
      r • boundedScalarMultiplierValue a ha C hbound f
    apply Lp.ext
    filter_upwards [boundedScalarMultiplierValue_ae a ha C hbound (r • f),
      boundedScalarMultiplierValue_ae a ha C hbound f, Lp.coeFn_smul r f,
      Lp.coeFn_smul r (boundedScalarMultiplierValue a ha C hbound f)] with x hs hf hin hout
    rw [hs, hout, hin]
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [hf]
    ring

/-- Actual multiplication by a bounded measurable real function on
Lebesgue L², with the uniform pointwise bound supplying continuity. -/
def boundedScalarMultiplier (a : ℝ → ℝ) (ha : Measurable a)
    (C : ℝ) (hbound : ∀ x, |a x| ≤ C) : HermiteL2 →L[ℝ] HermiteL2 :=
  (boundedScalarMultiplierLinear a ha C hbound).mkContinuous C
    (boundedScalarMultiplierValue_bound a ha C hbound)

theorem boundedScalarMultiplier_ae (a : ℝ → ℝ) (ha : Measurable a)
    (C : ℝ) (hbound : ∀ x, |a x| ≤ C) (f : HermiteL2) :
    (boundedScalarMultiplier a ha C hbound f : ℝ → ℝ) =ᵐ[volume]
      (fun x => a x * f x) :=
  boundedScalarMultiplierValue_ae a ha C hbound f

theorem boundedScalarMultiplier_bound (a : ℝ → ℝ) (ha : Measurable a)
    (C : ℝ) (hbound : ∀ x, |a x| ≤ C) (f : HermiteL2) :
    ‖boundedScalarMultiplier a ha C hbound f‖ ≤ C * ‖f‖ :=
  boundedScalarMultiplierValue_bound a ha C hbound f

theorem boundedScalarMultiplier_norm_le (a : ℝ → ℝ) (ha : Measurable a)
    (C : ℝ) (hC : 0 ≤ C) (hbound : ∀ x, |a x| ≤ C) :
    ‖boundedScalarMultiplier a ha C hbound‖ ≤ C :=
  LinearMap.mkContinuous_norm_le _ hC _

theorem boundedScalarMultiplier_inner_swap (a : ℝ → ℝ) (ha : Measurable a)
    (C : ℝ) (hbound : ∀ x, |a x| ≤ C) (f g : HermiteL2) :
    ⟪boundedScalarMultiplier a ha C hbound f, g⟫_ℝ =
      ⟪f, boundedScalarMultiplier a ha C hbound g⟫_ℝ := by
  rw [L2.inner_def, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [boundedScalarMultiplier_ae a ha C hbound f,
    boundedScalarMultiplier_ae a ha C hbound g] with x hf hg
  rw [hf, hg]
  simp only [RCLike.inner_apply, conj_trivial]
  ring

def centralRadialBoundedWeight (x : ℝ) : ℝ :=
  centralRadiusLogDerivative x / (1 + |x|)

/-- The real sign is written as `x/|x|`, including its actual value zero
at the origin. This permits a direct measurable quotient construction. -/
def centralRadialSignedWeight (x : ℝ) : ℝ :=
  centralRadialBoundedWeight x * (x / |x|)

theorem measurable_centralRadialBoundedWeight : Measurable centralRadialBoundedWeight := by
  change Measurable (fun x : ℝ => centralRadiusLogDerivative x / (1 + |x|))
  exact contDiff_centralRadiusLogDerivative.continuous.measurable.div
    (measurable_const.add continuous_abs.measurable)

theorem measurable_centralRadialSignedWeight : Measurable centralRadialSignedWeight :=
  measurable_centralRadialBoundedWeight.mul (measurable_id.div continuous_abs.measurable)

theorem centralRadialBoundedWeight_abs_le (x : ℝ) :
    |centralRadialBoundedWeight x| ≤ centralRadiusWeightConstant := by
  unfold centralRadialBoundedWeight
  rw [abs_div, abs_of_pos (by positivity : (0 : ℝ) < 1 + |x|)]
  apply (div_le_iff₀ (by positivity : (0 : ℝ) < 1 + |x|)).mpr
  simpa only [Real.norm_eq_abs] using centralRadiusLogDerivative_norm_le_linear x

theorem centralRadialSignedWeight_abs_le (x : ℝ) :
    |centralRadialSignedWeight x| ≤ centralRadiusWeightConstant := by
  unfold centralRadialSignedWeight
  rw [abs_mul, abs_div, abs_abs]
  by_cases hx : x = 0
  · subst x
    simp only [abs_zero, zero_div, mul_zero]
    exact centralRadiusWeightConstant_pos.le
  · rw [div_self (abs_ne_zero.mpr hx), mul_one]
    exact centralRadialBoundedWeight_abs_le x

private theorem real_mul_sign_quotient (x : ℝ) : x * (x / |x|) = |x| := by
  by_cases hx : x = 0
  · subst x
    norm_num
  · have ha : |x| ≠ 0 := abs_ne_zero.mpr hx
    calc
      _ = x ^ 2 / |x| := by ring
      _ = |x| ^ 2 / |x| := by rw [sq_abs]
      _ = |x| := by field_simp [ha]

theorem centralRadiusLogDerivative_decomposition (x : ℝ) :
    centralRadiusLogDerivative x =
      centralRadialBoundedWeight x + x * centralRadialSignedWeight x := by
  symm
  calc
    _ = centralRadialBoundedWeight x * (1 + x * (x / |x|)) := by
      unfold centralRadialSignedWeight
      ring
    _ = centralRadialBoundedWeight x * (1 + |x|) := by rw [real_mul_sign_quotient]
    _ = centralRadiusLogDerivative x := by
      exact div_mul_cancel₀ _ (by positivity : (1 + |x| : ℝ) ≠ 0)

def centralRadialBMultiplier : HermiteL2 →L[ℝ] HermiteL2 :=
  boundedScalarMultiplier centralRadialBoundedWeight measurable_centralRadialBoundedWeight
    centralRadiusWeightConstant centralRadialBoundedWeight_abs_le

def centralRadialCMultiplier : HermiteL2 →L[ℝ] HermiteL2 :=
  boundedScalarMultiplier centralRadialSignedWeight measurable_centralRadialSignedWeight
    centralRadiusWeightConstant centralRadialSignedWeight_abs_le

theorem centralRadialBMultiplier_ae (f : HermiteL2) :
    (centralRadialBMultiplier f : ℝ → ℝ) =ᵐ[volume]
      (fun x => centralRadialBoundedWeight x * f x) :=
  boundedScalarMultiplier_ae _ _ _ _ f

theorem centralRadialCMultiplier_ae (f : HermiteL2) :
    (centralRadialCMultiplier f : ℝ → ℝ) =ᵐ[volume]
      (fun x => centralRadialSignedWeight x * f x) :=
  boundedScalarMultiplier_ae _ _ _ _ f

theorem centralRadialBMultiplier_norm_le :
    ‖centralRadialBMultiplier‖ ≤ centralRadiusWeightConstant :=
  boundedScalarMultiplier_norm_le _ _ _ centralRadiusWeightConstant_pos.le _

theorem centralRadialCMultiplier_norm_le :
    ‖centralRadialCMultiplier‖ ≤ centralRadiusWeightConstant :=
  boundedScalarMultiplier_norm_le _ _ _ centralRadiusWeightConstant_pos.le _

theorem centralRadialBMultiplier_inner_swap (f g : HermiteL2) :
    ⟪centralRadialBMultiplier f, g⟫_ℝ = ⟪f, centralRadialBMultiplier g⟫_ℝ :=
  boundedScalarMultiplier_inner_swap _ _ _ _ f g

theorem centralRadialCMultiplier_inner_swap (f g : HermiteL2) :
    ⟪centralRadialCMultiplier f, g⟫_ℝ = ⟪f, centralRadialCMultiplier g⟫_ℝ :=
  boundedScalarMultiplier_inner_swap _ _ _ _ f g

/-- Actual multiplication by the geometric material weight, including
the specified L² image rather than an assumed multiplication domain. -/
def HasCentralRadialWeightL2 (f wf : HermiteL2) : Prop :=
  (wf : ℝ → ℝ) =ᵐ[volume] (fun x => centralRadiusLogDerivative x * f x)

theorem HasCentralRadialWeightL2.unique {f wf vf : HermiteL2}
    (hw : HasCentralRadialWeightL2 f wf) (hv : HasCentralRadialWeightL2 f vf) : wf = vf :=
  Lp.ext (hw.trans hv.symm)

theorem centralRadialWeight_domain_iff (f : HermiteL2) :
    (∃ wf : HermiteL2, HasCentralRadialWeightL2 f wf) ↔
      MemLp (fun x => centralRadiusLogDerivative x * f x) 2 volume := by
  constructor
  · rintro ⟨wf, hw⟩
    exact (memLp_congr_ae hw).mp (Lp.memLp wf)
  · intro hw
    exact ⟨hw.toLp _, MemLp.coeFn_toLp hw⟩

theorem centralRadialWeight_of_position (f xf : HermiteL2)
    (hx : HasPositionL2 f xf) :
    HasCentralRadialWeightL2 f (centralRadialBMultiplier f + centralRadialCMultiplier xf) := by
  change (xf : ℝ → ℝ) =ᵐ[volume] (fun x => x * f x) at hx
  change ((centralRadialBMultiplier f + centralRadialCMultiplier xf : HermiteL2) : ℝ → ℝ)
    =ᵐ[volume] (fun x => centralRadiusLogDerivative x * f x)
  filter_upwards [hx, centralRadialBMultiplier_ae f, centralRadialCMultiplier_ae xf,
    Lp.coeFn_add (centralRadialBMultiplier f) (centralRadialCMultiplier xf)]
      with x hX hB hC hsum
  rw [hsum]
  simp only [Pi.add_apply]
  rw [hB, hC, hX, centralRadiusLogDerivative_decomposition]
  ring

/-- The required position moment of `cf` follows from the actual weighted
source: `X(cf) = nu*f - bf`. No equality of multiplication domains is used. -/
theorem centralRadialC_position_of_weight (f wf : HermiteL2)
    (hw : HasCentralRadialWeightL2 f wf) :
    HasPositionL2 (centralRadialCMultiplier f) (wf - centralRadialBMultiplier f) := by
  change (wf : ℝ → ℝ) =ᵐ[volume] (fun x => centralRadiusLogDerivative x * f x) at hw
  change ((wf - centralRadialBMultiplier f : HermiteL2) : ℝ → ℝ) =ᵐ[volume]
    (fun x => x * centralRadialCMultiplier f x)
  filter_upwards [hw, centralRadialBMultiplier_ae f, centralRadialCMultiplier_ae f,
    Lp.coeFn_sub wf (centralRadialBMultiplier f)] with x hW hB hC hsub
  rw [hsub]
  simp only [Pi.sub_apply]
  rw [hW, hB, hC, centralRadiusLogDerivative_decomposition]
  ring

def centralRadialOneSidedConstant : ℝ :=
  2 * centralRadiusWeightConstant * (2 / centralGapDelta)

def centralRadialDoubleConstant : ℝ :=
  4 * centralRadiusWeightConstant ^ 2 * (2 / centralGapDelta)

private theorem radialGapBound_nonneg : 0 ≤ (2 / centralGapDelta : ℝ) :=
  div_nonneg (by norm_num) centralGapDelta_pos.le

/-- The actual bounded left-weighted inverse `nu G`. -/
def centralRadialLeftInverse (n : ℕ) (hn : 2 ≤ n) : HermiteL2 →L[ℝ] HermiteL2 :=
  centralRadialBMultiplier.comp (centralHilbertInverse n hn) +
    centralRadialCMultiplier.comp (centralPositionInverse n hn)

/-- The bounded right-weighted extension `G nu`. -/
def centralRadialRightInverse (n : ℕ) (hn : 2 ≤ n) : HermiteL2 →L[ℝ] HermiteL2 :=
  (centralHilbertInverse n hn).comp centralRadialBMultiplier +
    (centralRightPositionInverse n hn).comp centralRadialCMultiplier

def centralRadialRightPositionInverse (n : ℕ) (hn : 2 ≤ n) : HermiteL2 →L[ℝ] HermiteL2 :=
  (centralPositionInverse n hn).comp centralRadialBMultiplier +
    (centralDoublePositionInverse n hn).comp centralRadialCMultiplier

/-- The four bounded pieces are `Mb G Mb`, `Mb R Mc`, `Mc S Mb`,
and `Mc T Mc`, using the actual position inverse pieces `S,R,T`. -/
def centralRadialDoubleInverse (n : ℕ) (hn : 2 ≤ n) : HermiteL2 →L[ℝ] HermiteL2 :=
  centralRadialBMultiplier.comp (centralRadialRightInverse n hn) +
    centralRadialCMultiplier.comp (centralRadialRightPositionInverse n hn)

theorem centralRadialDoubleInverse_apply (n : ℕ) (hn : 2 ≤ n) (f : HermiteL2) :
    centralRadialDoubleInverse n hn f =
      centralRadialBMultiplier (centralHilbertInverse n hn (centralRadialBMultiplier f)) +
      centralRadialBMultiplier (centralRightPositionInverse n hn (centralRadialCMultiplier f)) +
      centralRadialCMultiplier (centralPositionInverse n hn (centralRadialBMultiplier f)) +
      centralRadialCMultiplier (centralDoublePositionInverse n hn (centralRadialCMultiplier f)) := by
  change centralRadialBMultiplier (_ + _) + centralRadialCMultiplier (_ + _) = _
  rw [map_add, map_add]
  abel

theorem centralRadialLeftInverse_norm_le (n : ℕ) (hn : 2 ≤ n) :
    ‖centralRadialLeftInverse n hn‖ ≤ centralRadialOneSidedConstant := by
  unfold centralRadialLeftInverse
  calc
    _ ≤ ‖centralRadialBMultiplier.comp (centralHilbertInverse n hn)‖ +
        ‖centralRadialCMultiplier.comp (centralPositionInverse n hn)‖ := norm_add_le _ _
    _ ≤ ‖centralRadialBMultiplier‖ * ‖centralHilbertInverse n hn‖ +
        ‖centralRadialCMultiplier‖ * ‖centralPositionInverse n hn‖ :=
      add_le_add (ContinuousLinearMap.opNorm_comp_le _ _) (ContinuousLinearMap.opNorm_comp_le _ _)
    _ ≤ centralRadiusWeightConstant * (2 / centralGapDelta) +
        centralRadiusWeightConstant * (2 / centralGapDelta) :=
      add_le_add
        (mul_le_mul centralRadialBMultiplier_norm_le (centralHilbertInverse_norm_le n hn)
          (norm_nonneg _) centralRadiusWeightConstant_pos.le)
        (mul_le_mul centralRadialCMultiplier_norm_le (centralPositionInverse_norm_le n hn)
          (norm_nonneg _) centralRadiusWeightConstant_pos.le)
    _ = _ := by unfold centralRadialOneSidedConstant; ring

theorem centralRadialRightInverse_norm_le (n : ℕ) (hn : 2 ≤ n) :
    ‖centralRadialRightInverse n hn‖ ≤ centralRadialOneSidedConstant := by
  unfold centralRadialRightInverse
  calc
    _ ≤ ‖(centralHilbertInverse n hn).comp centralRadialBMultiplier‖ +
        ‖(centralRightPositionInverse n hn).comp centralRadialCMultiplier‖ := norm_add_le _ _
    _ ≤ ‖centralHilbertInverse n hn‖ * ‖centralRadialBMultiplier‖ +
        ‖centralRightPositionInverse n hn‖ * ‖centralRadialCMultiplier‖ :=
      add_le_add (ContinuousLinearMap.opNorm_comp_le _ _) (ContinuousLinearMap.opNorm_comp_le _ _)
    _ ≤ (2 / centralGapDelta) * centralRadiusWeightConstant +
        (2 / centralGapDelta) * centralRadiusWeightConstant :=
      add_le_add
        (mul_le_mul (centralHilbertInverse_norm_le n hn) centralRadialBMultiplier_norm_le
          (norm_nonneg _) radialGapBound_nonneg)
        (mul_le_mul (centralRightPositionInverse_norm_le n hn) centralRadialCMultiplier_norm_le
          (norm_nonneg _) radialGapBound_nonneg)
    _ = _ := by unfold centralRadialOneSidedConstant; ring

theorem centralRadialRightPositionInverse_norm_le (n : ℕ) (hn : 2 ≤ n) :
    ‖centralRadialRightPositionInverse n hn‖ ≤ centralRadialOneSidedConstant := by
  unfold centralRadialRightPositionInverse
  calc
    _ ≤ ‖(centralPositionInverse n hn).comp centralRadialBMultiplier‖ +
        ‖(centralDoublePositionInverse n hn).comp centralRadialCMultiplier‖ := norm_add_le _ _
    _ ≤ ‖centralPositionInverse n hn‖ * ‖centralRadialBMultiplier‖ +
        ‖centralDoublePositionInverse n hn‖ * ‖centralRadialCMultiplier‖ :=
      add_le_add (ContinuousLinearMap.opNorm_comp_le _ _) (ContinuousLinearMap.opNorm_comp_le _ _)
    _ ≤ (2 / centralGapDelta) * centralRadiusWeightConstant +
        (2 / centralGapDelta) * centralRadiusWeightConstant :=
      add_le_add
        (mul_le_mul (centralPositionInverse_norm_le n hn) centralRadialBMultiplier_norm_le
          (norm_nonneg _) radialGapBound_nonneg)
        (mul_le_mul (centralDoublePositionInverse_norm_le n hn) centralRadialCMultiplier_norm_le
          (norm_nonneg _) radialGapBound_nonneg)
    _ = _ := by unfold centralRadialOneSidedConstant; ring

theorem centralRadialDoubleInverse_norm_le (n : ℕ) (hn : 2 ≤ n) :
    ‖centralRadialDoubleInverse n hn‖ ≤ centralRadialDoubleConstant := by
  unfold centralRadialDoubleInverse
  calc
    _ ≤ ‖centralRadialBMultiplier.comp (centralRadialRightInverse n hn)‖ +
        ‖centralRadialCMultiplier.comp (centralRadialRightPositionInverse n hn)‖ := norm_add_le _ _
    _ ≤ ‖centralRadialBMultiplier‖ * ‖centralRadialRightInverse n hn‖ +
        ‖centralRadialCMultiplier‖ * ‖centralRadialRightPositionInverse n hn‖ :=
      add_le_add (ContinuousLinearMap.opNorm_comp_le _ _) (ContinuousLinearMap.opNorm_comp_le _ _)
    _ ≤ centralRadiusWeightConstant * centralRadialOneSidedConstant +
        centralRadiusWeightConstant * centralRadialOneSidedConstant :=
      add_le_add
        (mul_le_mul centralRadialBMultiplier_norm_le (centralRadialRightInverse_norm_le n hn)
          (norm_nonneg _) centralRadiusWeightConstant_pos.le)
        (mul_le_mul centralRadialCMultiplier_norm_le (centralRadialRightPositionInverse_norm_le n hn)
          (norm_nonneg _) centralRadiusWeightConstant_pos.le)
    _ = _ := by unfold centralRadialOneSidedConstant centralRadialDoubleConstant; ring

theorem centralRadialLeftInverse_ae (n : ℕ) (hn : 2 ≤ n) (f : HermiteL2) :
    HasCentralRadialWeightL2 (centralHilbertInverse n hn f) (centralRadialLeftInverse n hn f) :=
  centralRadialWeight_of_position _ _ (centralPositionInverse_ae n hn f)

theorem centralRadialRightInverse_position (n : ℕ) (hn : 2 ≤ n) (f : HermiteL2) :
    HasPositionL2 (centralRadialRightInverse n hn f) (centralRadialRightPositionInverse n hn f) := by
  change ((centralPositionInverse n hn (centralRadialBMultiplier f) +
    centralDoublePositionInverse n hn (centralRadialCMultiplier f) : HermiteL2) : ℝ → ℝ)
      =ᵐ[volume] (fun x => x * (centralHilbertInverse n hn (centralRadialBMultiplier f) +
        centralRightPositionInverse n hn (centralRadialCMultiplier f)) x)
  have hT : (centralDoublePositionInverse n hn (centralRadialCMultiplier f) : ℝ → ℝ)
      =ᵐ[volume] (fun x => x * centralRightPositionInverse n hn (centralRadialCMultiplier f) x) :=
    centralDoublePositionInverse_ae n hn _
  filter_upwards [centralPositionInverse_ae n hn (centralRadialBMultiplier f), hT,
    Lp.coeFn_add (centralPositionInverse n hn (centralRadialBMultiplier f))
      (centralDoublePositionInverse n hn (centralRadialCMultiplier f)),
    Lp.coeFn_add (centralHilbertInverse n hn (centralRadialBMultiplier f))
      (centralRightPositionInverse n hn (centralRadialCMultiplier f))] with x hS hD hout hin
  rw [hout, hin]
  simp only [Pi.add_apply]
  rw [hS, hD]
  ring

theorem centralRadialDoubleInverse_ae (n : ℕ) (hn : 2 ≤ n) (f : HermiteL2) :
    HasCentralRadialWeightL2 (centralRadialRightInverse n hn f) (centralRadialDoubleInverse n hn f) :=
  centralRadialWeight_of_position _ _ (centralRadialRightInverse_position n hn f)

theorem centralRadialRightInverse_eq (n : ℕ) (hn : 2 ≤ n) (f wf : HermiteL2)
    (hw : HasCentralRadialWeightL2 f wf) :
    centralRadialRightInverse n hn f = centralHilbertInverse n hn wf := by
  change centralHilbertInverse n hn (centralRadialBMultiplier f) +
    centralRightPositionInverse n hn (centralRadialCMultiplier f) = _
  rw [centralRightPositionInverse_eq n hn (centralRadialCMultiplier f)
    (wf - centralRadialBMultiplier f) (centralRadialC_position_of_weight f wf hw), map_sub]
  abel

/-- On every actual nu-weighted source, the bounded four-piece extension
is precisely `nu * G(nu*f)` as an actual L² identity. -/
theorem centralRadialDoubleInverse_weighted (n : ℕ) (hn : 2 ≤ n) (f wf : HermiteL2)
    (hw : HasCentralRadialWeightL2 f wf) :
    HasCentralRadialWeightL2 (centralHilbertInverse n hn wf) (centralRadialDoubleInverse n hn f) := by
  have h := centralRadialDoubleInverse_ae n hn f
  rwa [centralRadialRightInverse_eq n hn f wf hw] at h

theorem centralRadialDoubleInverse_memLp_source (n : ℕ) (hn : 2 ≤ n) (f : HermiteL2)
    (hw : MemLp (fun x => centralRadiusLogDerivative x * f x) 2 volume) :
    HasCentralRadialWeightL2
      (centralHilbertInverse n hn (hw.toLp (fun x => centralRadiusLogDerivative x * f x)))
      (centralRadialDoubleInverse n hn f) :=
  centralRadialDoubleInverse_weighted n hn f _ (MemLp.coeFn_toLp hw)

/-- The actual bounded right extension is the adjoint relation of the
actual left-weighted inverse, on the whole Hilbert space. -/
theorem centralRadialRightInverse_inner_swap (n : ℕ) (hn : 2 ≤ n) (f g : HermiteL2) :
    ⟪centralRadialRightInverse n hn f, g⟫_ℝ =
      ⟪f, centralRadialLeftInverse n hn g⟫_ℝ := by
  change ⟪centralHilbertInverse n hn (centralRadialBMultiplier f) +
      centralRightPositionInverse n hn (centralRadialCMultiplier f), g⟫_ℝ =
    ⟪f, centralRadialBMultiplier (centralHilbertInverse n hn g) +
      centralRadialCMultiplier (centralPositionInverse n hn g)⟫_ℝ
  rw [inner_add_left, inner_add_right]
  have hB := (centralHilbertInverse_inner_swap n hn (centralRadialBMultiplier f) g).trans
    (centralRadialBMultiplier_inner_swap f (centralHilbertInverse n hn g))
  have hC : ⟪centralRightPositionInverse n hn (centralRadialCMultiplier f), g⟫_ℝ =
      ⟪f, centralRadialCMultiplier (centralPositionInverse n hn g)⟫_ℝ := by
    change ⟪ContinuousLinearMap.adjoint (centralPositionInverse n hn)
      (centralRadialCMultiplier f), g⟫_ℝ = _
    rw [ContinuousLinearMap.adjoint_inner_left]
    exact centralRadialCMultiplier_inner_swap f _
  exact congrArg₂ (fun x y : ℝ => x + y) hB hC

private theorem norm_comp_pair_le
    (A B C D : HermiteL2 →L[ℝ] HermiteL2) (a b c d : ℝ)
    (hA : ‖A‖ ≤ a) (hB : ‖B‖ ≤ b) (hC : ‖C‖ ≤ c) (hD : ‖D‖ ≤ d)
    (ha : 0 ≤ a) (hc : 0 ≤ c) :
    ‖A.comp B + C.comp D‖ ≤ a * b + c * d := by
  calc
    _ ≤ ‖A.comp B‖ + ‖C.comp D‖ := norm_add_le _ _
    _ ≤ ‖A‖ * ‖B‖ + ‖C‖ * ‖D‖ :=
      add_le_add (ContinuousLinearMap.opNorm_comp_le _ _) (ContinuousLinearMap.opNorm_comp_le _ _)
    _ ≤ _ := add_le_add
      (mul_le_mul hA hB (norm_nonneg _) ha) (mul_le_mul hC hD (norm_nonneg _) hc)

private theorem reducedHilbertInverse_norm_le_one : ‖centralReducedHilbertInverse‖ ≤ 1 :=
  centralReducedHilbertInverse_norm_le.trans (by norm_num)

/-- The same real material weight on the genuine mode-two reduced
inverse. Its source projection remains the actual Gaussian projection. -/
def centralRadialReducedLeftInverse : HermiteL2 →L[ℝ] HermiteL2 :=
  centralRadialBMultiplier.comp centralReducedHilbertInverse +
    centralRadialCMultiplier.comp centralReducedPositionInverse

def centralRadialReducedRightInverse : HermiteL2 →L[ℝ] HermiteL2 :=
  centralReducedHilbertInverse.comp centralRadialBMultiplier +
    centralReducedRightPositionInverse.comp centralRadialCMultiplier

def centralRadialReducedRightPositionInverse : HermiteL2 →L[ℝ] HermiteL2 :=
  centralReducedPositionInverse.comp centralRadialBMultiplier +
    centralReducedDoublePositionInverse.comp centralRadialCMultiplier

def centralRadialReducedDoubleInverse : HermiteL2 →L[ℝ] HermiteL2 :=
  centralRadialBMultiplier.comp centralRadialReducedRightInverse +
    centralRadialCMultiplier.comp centralRadialReducedRightPositionInverse

theorem centralRadialReducedLeftInverse_norm_le :
    ‖centralRadialReducedLeftInverse‖ ≤ 2 * centralRadiusWeightConstant := by
  have h := norm_comp_pair_le centralRadialBMultiplier centralReducedHilbertInverse
    centralRadialCMultiplier centralReducedPositionInverse
    centralRadiusWeightConstant 1 centralRadiusWeightConstant 1
    centralRadialBMultiplier_norm_le reducedHilbertInverse_norm_le_one
    centralRadialCMultiplier_norm_le centralReducedPositionInverse_norm_le
    centralRadiusWeightConstant_pos.le centralRadiusWeightConstant_pos.le
  exact h.trans_eq (by ring)

theorem centralRadialReducedRightInverse_norm_le :
    ‖centralRadialReducedRightInverse‖ ≤ 2 * centralRadiusWeightConstant := by
  have h := norm_comp_pair_le centralReducedHilbertInverse centralRadialBMultiplier
    centralReducedRightPositionInverse centralRadialCMultiplier
    1 centralRadiusWeightConstant 1 centralRadiusWeightConstant
    reducedHilbertInverse_norm_le_one centralRadialBMultiplier_norm_le
    centralReducedRightPositionInverse_norm_le centralRadialCMultiplier_norm_le zero_le_one zero_le_one
  exact h.trans_eq (by ring)

theorem centralRadialReducedRightPositionInverse_norm_le :
    ‖centralRadialReducedRightPositionInverse‖ ≤ 2 * centralRadiusWeightConstant := by
  have h := norm_comp_pair_le centralReducedPositionInverse centralRadialBMultiplier
    centralReducedDoublePositionInverse centralRadialCMultiplier
    1 centralRadiusWeightConstant 1 centralRadiusWeightConstant
    centralReducedPositionInverse_norm_le centralRadialBMultiplier_norm_le
    centralReducedDoublePositionInverse_norm_le centralRadialCMultiplier_norm_le zero_le_one zero_le_one
  exact h.trans_eq (by ring)

theorem centralRadialReducedDoubleInverse_norm_le :
    ‖centralRadialReducedDoubleInverse‖ ≤ 4 * centralRadiusWeightConstant ^ 2 := by
  have h := norm_comp_pair_le centralRadialBMultiplier centralRadialReducedRightInverse
    centralRadialCMultiplier centralRadialReducedRightPositionInverse
    centralRadiusWeightConstant (2 * centralRadiusWeightConstant)
      centralRadiusWeightConstant (2 * centralRadiusWeightConstant)
    centralRadialBMultiplier_norm_le centralRadialReducedRightInverse_norm_le
    centralRadialCMultiplier_norm_le centralRadialReducedRightPositionInverse_norm_le
    centralRadiusWeightConstant_pos.le centralRadiusWeightConstant_pos.le
  exact h.trans_eq (by ring)

theorem centralRadialReducedDoubleInverse_norm_le_uniform :
    ‖centralRadialReducedDoubleInverse‖ ≤ centralRadialDoubleConstant := by
  have hC : (1 : ℝ) ≤ 2 / centralGapDelta := by
    apply (le_div_iff₀ centralGapDelta_pos).mpr
    linarith [centralGapDelta_lt_one]
  exact centralRadialReducedDoubleInverse_norm_le.trans
    (by simpa only [centralRadialDoubleConstant, mul_one] using
      mul_le_mul_of_nonneg_left hC (by positivity : (0 : ℝ) ≤ 4 * centralRadiusWeightConstant ^ 2))

theorem centralRadialReducedDoubleInverse_apply (f : HermiteL2) :
    centralRadialReducedDoubleInverse f =
      centralRadialBMultiplier (centralReducedHilbertInverse (centralRadialBMultiplier f)) +
      centralRadialBMultiplier (centralReducedRightPositionInverse (centralRadialCMultiplier f)) +
      centralRadialCMultiplier (centralReducedPositionInverse (centralRadialBMultiplier f)) +
      centralRadialCMultiplier (centralReducedDoublePositionInverse (centralRadialCMultiplier f)) := by
  change centralRadialBMultiplier (_ + _) + centralRadialCMultiplier (_ + _) = _
  rw [map_add, map_add]
  abel

theorem centralRadialReducedLeftInverse_ae (f : HermiteL2) :
    HasCentralRadialWeightL2 (centralReducedHilbertInverse f) (centralRadialReducedLeftInverse f) :=
  centralRadialWeight_of_position _ _ (centralReducedPositionInverse_ae f)

theorem centralRadialReducedRightInverse_position (f : HermiteL2) :
    HasPositionL2 (centralRadialReducedRightInverse f) (centralRadialReducedRightPositionInverse f) := by
  change ((centralReducedPositionInverse (centralRadialBMultiplier f) +
    centralReducedDoublePositionInverse (centralRadialCMultiplier f) : HermiteL2) : ℝ → ℝ)
      =ᵐ[volume] (fun x => x * (centralReducedHilbertInverse (centralRadialBMultiplier f) +
        centralReducedRightPositionInverse (centralRadialCMultiplier f)) x)
  have hS : (centralReducedPositionInverse (centralRadialBMultiplier f) : ℝ → ℝ)
      =ᵐ[volume] (fun x => x * centralReducedHilbertInverse (centralRadialBMultiplier f) x) :=
    centralReducedPositionInverse_ae _
  have hT : (centralReducedDoublePositionInverse (centralRadialCMultiplier f) : ℝ → ℝ)
      =ᵐ[volume] (fun x => x * centralReducedRightPositionInverse (centralRadialCMultiplier f) x) :=
    centralReducedDoublePositionInverse_ae _
  filter_upwards [hS, hT,
    Lp.coeFn_add (centralReducedPositionInverse (centralRadialBMultiplier f))
      (centralReducedDoublePositionInverse (centralRadialCMultiplier f)),
    Lp.coeFn_add (centralReducedHilbertInverse (centralRadialBMultiplier f))
      (centralReducedRightPositionInverse (centralRadialCMultiplier f))] with x hs ht hout hin
  rw [hout, hin]
  simp only [Pi.add_apply]
  rw [hs, ht]
  ring

theorem centralRadialReducedDoubleInverse_ae (f : HermiteL2) :
    HasCentralRadialWeightL2 (centralRadialReducedRightInverse f) (centralRadialReducedDoubleInverse f) :=
  centralRadialWeight_of_position _ _ (centralRadialReducedRightInverse_position f)

theorem centralRadialReducedRightInverse_eq (f wf : HermiteL2)
    (hw : HasCentralRadialWeightL2 f wf) :
    centralRadialReducedRightInverse f = centralReducedHilbertInverse wf := by
  change centralReducedHilbertInverse (centralRadialBMultiplier f) +
    centralReducedRightPositionInverse (centralRadialCMultiplier f) = _
  rw [centralReducedRightPositionInverse_eq (centralRadialCMultiplier f)
    (wf - centralRadialBMultiplier f) (centralRadialC_position_of_weight f wf hw), map_sub]
  abel

theorem centralRadialReducedDoubleInverse_weighted (f wf : HermiteL2)
    (hw : HasCentralRadialWeightL2 f wf) :
    HasCentralRadialWeightL2 (centralReducedHilbertInverse wf) (centralRadialReducedDoubleInverse f) := by
  have h := centralRadialReducedDoubleInverse_ae f
  rwa [centralRadialReducedRightInverse_eq f wf hw] at h

theorem centralRadialReducedDoubleInverse_memLp_source (f : HermiteL2)
    (hw : MemLp (fun x => centralRadiusLogDerivative x * f x) 2 volume) :
    HasCentralRadialWeightL2
      (centralReducedHilbertInverse (hw.toLp (fun x => centralRadiusLogDerivative x * f x)))
      (centralRadialReducedDoubleInverse f) :=
  centralRadialReducedDoubleInverse_weighted f _ (MemLp.coeFn_toLp hw)

theorem centralRadialReducedRightInverse_inner_swap (f g : HermiteL2) :
    ⟪centralRadialReducedRightInverse f, g⟫_ℝ = ⟪f, centralRadialReducedLeftInverse g⟫_ℝ := by
  change ⟪centralReducedHilbertInverse (centralRadialBMultiplier f) +
      centralReducedRightPositionInverse (centralRadialCMultiplier f), g⟫_ℝ =
    ⟪f, centralRadialBMultiplier (centralReducedHilbertInverse g) +
      centralRadialCMultiplier (centralReducedPositionInverse g)⟫_ℝ
  rw [inner_add_left, inner_add_right]
  have hB := (centralReducedHilbertInverse_inner_swap (centralRadialBMultiplier f) g).trans
    (centralRadialBMultiplier_inner_swap f (centralReducedHilbertInverse g))
  have hC : ⟪centralReducedRightPositionInverse (centralRadialCMultiplier f), g⟫_ℝ =
      ⟪f, centralRadialCMultiplier (centralReducedPositionInverse g)⟫_ℝ := by
    change ⟪ContinuousLinearMap.adjoint centralReducedPositionInverse
      (centralRadialCMultiplier f), g⟫_ℝ = _
    rw [ContinuousLinearMap.adjoint_inner_left]
    exact centralRadialCMultiplier_inner_swap f _
  exact congrArg₂ (fun x y : ℝ => x + y) hB hC

end ContinuousFlexibility.Radial
