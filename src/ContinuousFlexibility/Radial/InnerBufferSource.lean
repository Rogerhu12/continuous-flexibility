import ContinuousFlexibility.Radial.InnerBufferBarrier
import ContinuousFlexibility.Radial.InnerBufferL2
import Mathlib.Analysis.Calculus.Deriv.Support

/-!
# The actual exponentially small cutoff source

Both derivatives of the fixed transition have universal bounds. The
commutator of the actual buffer cutoff is supported on its inner layer,
whose model-coordinate length is exactly 1 / mass. Combining this fact
with the exponential and derivative estimates of the same buffer column
gives its mass^(3/2) * exp (-action) L² bound.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open Set Filter MeasureTheory Real
open ContinuousFlexibility.Statements
open scoped Topology ContDiff

theorem innerTransition_second_deriv_zero {x : ℝ} (hx : x ∉ Icc (0 : ℝ) 1) :
    deriv (deriv smoothTransition) x = 0 := by
  have hz : deriv smoothTransition =ᶠ[𝓝 x] (fun _ => 0) := by
    filter_upwards [isClosed_Icc.isOpen_compl.mem_nhds hx] with y hy
    exact innerTransition_deriv_eq_zero hy
  exact hz.deriv_eq.trans (deriv_const x 0)

theorem innerTransition_second_deriv_bounded :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x, |deriv (deriv smoothTransition) x| ≤ C := by
  have hcd := (contDiff_infty_iff_deriv.mp smoothTransition.contDiff).2
  have hc := hcd.continuous_deriv (by simp)
  have hs : HasCompactSupport (deriv (deriv smoothTransition)) :=
    HasCompactSupport.intro isCompact_Icc (fun x hx => innerTransition_second_deriv_zero hx)
  obtain ⟨C, hC⟩ := hc.bounded_above_of_compact_support hs
  exact ⟨max 0 C, le_max_left _ _, fun x => (hC x).trans (le_max_right _ _)⟩

private theorem innerBufferCutoff_argument_deriv (B : BufferData) (i : Fin 2) (x : ℝ) :
    HasDerivAt (fun y : ℝ =>
      B.action i + 4 + B.mass i * bufferSign i * (y - bufferCut B i))
      (B.mass i * bufferSign i) x := by
  convert (((hasDerivAt_id x).sub_const (bufferCut B i)).const_mul
    (B.mass i * bufferSign i)).const_add (B.action i + 4) using 1 <;>
      simp only [id_eq, mul_one] <;> ring

theorem innerBufferCutoff_deriv (B : BufferData) (i : Fin 2) (x : ℝ) :
    deriv (innerBufferCutoff B i) x =
      deriv smoothTransition
        (B.action i + 4 + B.mass i * bufferSign i * (x - bufferCut B i)) *
          (B.mass i * bufferSign i) := by
  exact (((smoothTransition.contDiff.differentiable (by simp) _).hasDerivAt).comp x
    (innerBufferCutoff_argument_deriv B i x)).deriv

theorem innerBufferCutoff_second_deriv (B : BufferData) (i : Fin 2) (x : ℝ) :
    deriv (deriv (innerBufferCutoff B i)) x =
      deriv (deriv smoothTransition)
        (B.action i + 4 + B.mass i * bufferSign i * (x - bufferCut B i)) *
          (B.mass i * bufferSign i) ^ 2 := by
  have hfirst : deriv (innerBufferCutoff B i) = fun y =>
      deriv smoothTransition
        (B.action i + 4 + B.mass i * bufferSign i * (y - bufferCut B i)) *
          (B.mass i * bufferSign i) := funext (innerBufferCutoff_deriv B i)
  have hcd := (contDiff_infty_iff_deriv.mp smoothTransition.contDiff).2
  rw [hfirst]
  have hd := ((((hcd.differentiable (by simp) _).hasDerivAt).comp x
    (innerBufferCutoff_argument_deriv B i x)).mul_const (B.mass i * bufferSign i)).deriv
  exact hd.trans (by ring)

theorem innerBufferCutoff_derivative_bounds {B : BufferData} (hB : BufferHypotheses B)
    (i : Fin 2) {C₁ C₂ : ℝ}
    (h₁ : ∀ x, |deriv smoothTransition x| ≤ C₁)
    (h₂ : ∀ x, |deriv (deriv smoothTransition) x| ≤ C₂) (x : ℝ) :
    |deriv (innerBufferCutoff B i) x| ≤ C₁ * B.mass i ∧
      |deriv (deriv (innerBufferCutoff B i)) x| ≤ C₂ * B.mass i ^ 2 := by
  have hm := buffer_mass_pos hB i
  constructor
  · rw [innerBufferCutoff_deriv, abs_mul, abs_mul, abs_bufferSign, mul_one, abs_of_pos hm]
    exact mul_le_mul_of_nonneg_right (h₁ _) hm.le
  · rw [innerBufferCutoff_second_deriv, abs_mul, abs_pow, abs_mul, abs_bufferSign,
      mul_one, abs_of_pos hm]
    exact mul_le_mul_of_nonneg_right (h₂ _) (sq_nonneg _)

def innerBufferSource (B : BufferData) (i : Fin 2) (p : ℝ → ℝ) (x : ℝ) : ℝ :=
  -deriv (deriv (innerBufferCutoff B i)) x * p x -
    2 * deriv (innerBufferCutoff B i) x * deriv p x

theorem innerBufferSource_zero_outside_layer (B : BufferData) (i : Fin 2)
    (p : ℝ → ℝ) {x : ℝ}
    (hx : B.mass i * bufferSign i * (bufferCut B i - x) ∉
      Icc (B.action i + 3) (B.action i + 4)) : innerBufferSource B i p x = 0 := by
  have harg : B.action i + 4 + B.mass i * bufferSign i * (x - bufferCut B i) ∉
      Icc (0 : ℝ) 1 := by
    intro h
    apply hx
    constructor <;> nlinarith only [h.1, h.2]
  rw [innerBufferSource, innerBufferCutoff_deriv, innerBufferCutoff_second_deriv,
    innerTransition_deriv_eq_zero harg, innerTransition_second_deriv_zero harg]
  ring

theorem innerBufferSource_point_bound {B : BufferData} (hB : BufferHypotheses B)
    (i : Fin 2) {p : ℝ → ℝ} {C₁ C₂ : ℝ} (hC₁ : 0 ≤ C₁) (hC₂ : 0 ≤ C₂)
    (h₁ : ∀ x, |deriv smoothTransition x| ≤ C₁)
    (h₂ : ∀ x, |deriv (deriv smoothTransition) x| ≤ C₂)
    (hp : ContDiffOn ℝ 2 p (uIcc (bufferCut B i) (bufferInnerWall B i)))
    (heq : ∀ x ∈ radialOpenSpan (bufferCut B i) (bufferInnerWall B i),
      -deriv (deriv p) x + B.potential x * p x = 0)
    (hcut : p (bufferCut B i) = 1) (hwall : p (bufferInnerWall B i) = 0) (x : ℝ) :
    |innerBufferSource B i p x| ≤
      (C₂ + 2 * C₁ * (2 + B.layerBound)) * B.mass i ^ 2 * exp (-B.action i) := by
  let t : ℝ := B.mass i * bufferSign i * (bufferCut B i - x)
  have hC : 0 < B.layerBound := hB.2.2.2.1
  by_cases ht : t ∈ Icc (B.action i + 3) (B.action i + 4)
  · have hpHeight := innerBuffer_column_inner_height hB i hp heq hcut hwall
      (t := t) ⟨by linarith only [ht.1], by linarith only [ht.2]⟩
    have hpDeriv := innerBuffer_column_inner_derivative hB i hp heq hcut hwall ht
    rw [innerBufferPoint_coordinate hB i x] at hpHeight hpDeriv
    have hχ := innerBufferCutoff_derivative_bounds hB i h₁ h₂ x
    exact innerBuffer_commutator_bound (buffer_mass_pos hB i).le (exp_pos _).le
      hC.le hC₁ hC₂ hpHeight hpDeriv hχ.1 hχ.2
  · rw [innerBufferSource_zero_outside_layer B i p ht, abs_zero]
    positivity

theorem innerBufferPoint_interval_mono (B : BufferData) (i : Fin 2)
    (hm : 0 < B.mass i) {s t y : ℝ} (hy : y ∈ Icc s t) :
    positiveBufferPoint B i y ∈
      uIcc (positiveBufferPoint B i s) (positiveBufferPoint B i t) := by
  by_cases hi : i = 0
  · have hmono : Monotone (positiveBufferPoint B i) := by
      intro a b hab
      simp only [positiveBufferPoint, bufferSign, if_pos hi, neg_mul, one_mul,
        neg_div, sub_neg_eq_add]
      linarith only [div_le_div_of_nonneg_right hab hm.le]
    exact hmono.image_uIcc_subset ⟨y, Icc_subset_uIcc hy, rfl⟩
  · have hanti : Antitone (positiveBufferPoint B i) := by
      intro a b hab
      simp only [positiveBufferPoint, bufferSign, if_neg hi, one_mul]
      linarith only [div_le_div_of_nonneg_right hab hm.le]
    exact hanti.image_uIcc_subset ⟨y, Icc_subset_uIcc hy, rfl⟩

theorem innerBufferSource_support {B : BufferData} (hB : BufferHypotheses B)
    (i : Fin 2) (p : ℝ → ℝ) {x : ℝ}
    (hx : x ∉ uIcc (positiveBufferPoint B i (B.action i + 3))
      (positiveBufferPoint B i (B.action i + 4))) : innerBufferSource B i p x = 0 := by
  apply innerBufferSource_zero_outside_layer
  intro ht
  apply hx
  have h := innerBufferPoint_interval_mono B i (buffer_mass_pos hB i) ht
  rw [innerBufferPoint_coordinate hB i x] at h
  exact h

/-- The zero extension of the actual commutator has the uniform mass-scale
L² estimate, with no factor from the length of the whole model interval. -/
theorem innerBufferSource_L2_bound {B : BufferData} (hB : BufferHypotheses B)
    (i : Fin 2) {p : ℝ → ℝ} {C₁ C₂ : ℝ} (hC₁ : 0 ≤ C₁) (hC₂ : 0 ≤ C₂)
    (h₁ : ∀ x, |deriv smoothTransition x| ≤ C₁)
    (h₂ : ∀ x, |deriv (deriv smoothTransition) x| ≤ C₂)
    (hp : ContDiffOn ℝ 2 p (uIcc (bufferCut B i) (bufferInnerWall B i)))
    (heq : ∀ x ∈ radialOpenSpan (bufferCut B i) (bufferInnerWall B i),
      -deriv (deriv p) x + B.potential x * p x = 0)
    (hcut : p (bufferCut B i) = 1) (hwall : p (bufferInnerWall B i) = 0)
    (f : RadialL2)
    (hf : (f : ℝ → ℝ) =ᵐ[volume] (Ioo B.l B.h).indicator (innerBufferSource B i p)) :
    ‖f‖ ≤ (C₂ + 2 * C₁ * (2 + B.layerBound)) *
      B.mass i ^ (3 / 2 : ℝ) * exp (-B.action i) := by
  let a := positiveBufferPoint B i (B.action i + 3)
  let b := positiveBufferPoint B i (B.action i + 4)
  let K := C₂ + 2 * C₁ * (2 + B.layerBound)
  have hK : 0 ≤ K := by dsimp only [K]; have := hB.2.2.2.1; positivity
  have hm := buffer_mass_pos hB i
  have hbound : ∀ᵐ x ∂volume, x ∈ Icc (min a b) (max a b) →
      |f x| ≤ K * B.mass i ^ 2 * exp (-B.action i) := by
    filter_upwards [hf] with x hfx _
    rw [hfx]
    by_cases hx : x ∈ Ioo B.l B.h
    · rw [Set.indicator_of_mem hx]
      exact innerBufferSource_point_bound hB i hC₁ hC₂ h₁ h₂ hp heq hcut hwall x
    · rw [Set.indicator_of_notMem hx, abs_zero]
      positivity
  have hsupport : ∀ᵐ x ∂volume, x ∉ Icc (min a b) (max a b) → f x = 0 := by
    filter_upwards [hf] with x hfx hx
    rw [hfx]
    by_cases hxi : x ∈ Ioo B.l B.h
    · rw [Set.indicator_of_mem hxi]
      exact innerBufferSource_support hB i p hx
    · rw [Set.indicator_of_notMem hxi]
  have hlength : max a b - min a b = 1 / B.mass i := by
    have hdist := positiveBufferPoint_distance hB i (B.action i + 3) (B.action i + 4)
    have habs : max a b - min a b = |a - b| := by
      rcases le_total a b with hab | hba
      · rw [max_eq_right hab, min_eq_left hab, abs_of_nonpos (sub_nonpos.mpr hab)]
        ring
      · rw [max_eq_left hba, min_eq_right hba, abs_of_nonneg (sub_nonneg.mpr hba)]
    rw [habs]
    simpa only [show B.action i + 3 - (B.action i + 4) = (-1 : ℝ) by ring,
      abs_neg, abs_one] using hdist
  have h := innerIntervalL2_norm_le_of_support_bound (min_le_max) f
    (by positivity) hbound hsupport
  rw [hlength] at h
  calc
    ‖f‖ ≤ (K * B.mass i ^ 2 * exp (-B.action i)) * sqrt (1 / B.mass i) := h
    _ = K * (B.mass i ^ 2 * sqrt (1 / B.mass i)) * exp (-B.action i) := by ring
    _ = _ := by rw [inner_mass_sqrt_layer hm]

end ContinuousFlexibility.Radial
