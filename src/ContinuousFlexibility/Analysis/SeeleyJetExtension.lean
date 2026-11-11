import ContinuousFlexibility.Analysis.SeeleyData
import Mathlib.Analysis.Calculus.FDeriv.Extend
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.Analysis.Calculus.SmoothSeries
import Mathlib.Topology.Order.OrderClosed

/-!
# A single smooth extension of every half-line jet

The reflection coefficients do not depend on the derivative order. Their
moment identities make the reflected series and all its derivatives match
the original right-hand jets at zero. The summable absolute moments justify
termwise differentiation. This is the analytic part of Seeley's extension;
the coefficients are constructed separately, and the Sobolev estimates use
the same reflection formula.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter
open scoped Topology ContDiff

variable {ι F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

/-- A smooth jet up to the boundary, with each jet bounded on the half-line.
No extension across the boundary is included in these data. -/
structure IsBoundedHalfLineJet (J : ℕ → ℝ → F) : Prop where
  continuous : ∀ n, ContinuousOn (J n) (Ici 0)
  derivative : ∀ n x, 0 < x → HasDerivAt (J n) (J (n + 1) x) x
  bounded : ∀ n, ∃ M : ℝ, ∀ x, 0 ≤ x → ‖J n x‖ ≤ M

/-- The negative-side reflection series for the derivative of order `n`. -/
def seeleyReflection (S : SeeleyData ι) (n : ℕ) (f : ℝ → F) (x : ℝ) : F :=
  ∑' i, (S.a i * (-S.b i) ^ n) • f (-S.b i * x)

/-- The actual extension formula. The coefficients and reflection scales
are fixed once and for all, independently of any Sobolev order. -/
def seeleyExtend (S : SeeleyData ι) (f : ℝ → F) (x : ℝ) : F :=
  if 0 ≤ x then f x else seeleyReflection S 0 f x

/-- Candidate derivatives of the same extension, including the original
boundary values. -/
def seeleyExtensionJet (S : SeeleyData ι) (J : ℕ → ℝ → F) (n : ℕ) (x : ℝ) : F :=
  if 0 ≤ x then J n x else seeleyReflection S n (J n) x

@[simp] theorem seeleyExtend_of_nonneg (S : SeeleyData ι) (f : ℝ → F)
    {x : ℝ} (hx : 0 ≤ x) : seeleyExtend S f x = f x := by
  simp only [seeleyExtend, if_pos hx]

@[simp] theorem seeleyExtensionJet_zero (S : SeeleyData ι) (J : ℕ → ℝ → F) :
    seeleyExtensionJet S J 0 = seeleyExtend S (J 0) := rfl

@[simp] theorem seeleyExtensionJet_of_nonneg (S : SeeleyData ι) (J : ℕ → ℝ → F)
    (n : ℕ) {x : ℝ} (hx : 0 ≤ x) : seeleyExtensionJet S J n x = J n x := by
  simp only [seeleyExtensionJet, if_pos hx]

@[simp] theorem seeleyExtensionJet_of_neg (S : SeeleyData ι) (J : ℕ → ℝ → F)
    (n : ℕ) {x : ℝ} (hx : x < 0) :
    seeleyExtensionJet S J n x = seeleyReflection S n (J n) x := by
  simp only [seeleyExtensionJet, if_neg (not_le.mpr hx)]

private theorem seeley_scale_nonneg (S : SeeleyData ι) (i : ι) : 0 ≤ S.b i :=
  zero_le_one.trans (S.one_le_b i)

private theorem seeley_scale_pos (S : SeeleyData ι) (i : ι) : 0 < S.b i :=
  zero_lt_one.trans_le (S.one_le_b i)

theorem norm_seeley_coefficient (S : SeeleyData ι) (n : ℕ) (i : ι) :
    ‖S.a i * (-S.b i) ^ n‖ = |S.a i| * S.b i ^ n := by
  rw [norm_mul, norm_pow, norm_neg, Real.norm_eq_abs, Real.norm_eq_abs,
    abs_of_nonneg (seeley_scale_nonneg S i)]

theorem summable_seeleyReflection (S : SeeleyData ι) (n : ℕ) {f : ℝ → F}
    (hf : ∃ M : ℝ, ∀ y, 0 ≤ y → ‖f y‖ ≤ M) {x : ℝ} (hx : x ≤ 0) :
    Summable (fun i => (S.a i * (-S.b i) ^ n) • f (-S.b i * x)) := by
  obtain ⟨M, hM⟩ := hf
  apply ((S.summable_moment n).mul_right M).of_norm_bounded
  intro i
  rw [norm_smul, norm_seeley_coefficient]
  exact mul_le_mul_of_nonneg_left
    (hM _ (mul_nonneg_of_nonpos_of_nonpos (neg_nonpos.mpr (seeley_scale_nonneg S i)) hx))
    (mul_nonneg (abs_nonneg _) (pow_nonneg (seeley_scale_nonneg S i) n))

theorem seeleyReflection_at_zero (S : SeeleyData ι) (n : ℕ) (f : ℝ → F) :
    seeleyReflection S n f 0 = f 0 := by
  simp only [seeleyReflection, mul_zero]
  exact ((S.hasSum_moment n).smul_const (f 0)).tsum_eq.trans (one_smul ℝ _)

theorem continuousOn_seeleyReflection (S : SeeleyData ι) (n : ℕ) {f : ℝ → F}
    (hc : ContinuousOn f (Ici 0))
    (hb : ∃ M : ℝ, ∀ y, 0 ≤ y → ‖f y‖ ≤ M) :
    ContinuousOn (seeleyReflection S n f) (Iic 0) := by
  obtain ⟨M, hM⟩ := hb
  unfold seeleyReflection
  refine continuousOn_tsum ?_ ((S.summable_moment n).mul_right M) ?_
  · intro i
    have hcomp := hc.comp (continuous_const.mul continuous_id).continuousOn
      (fun x (hx : x ∈ Iic (0 : ℝ)) => mul_nonneg_of_nonpos_of_nonpos
        (neg_nonpos.mpr (seeley_scale_nonneg S i)) hx)
    simpa only [Pi.smul_def, Function.comp_def, Pi.mul_apply, id_eq] using
      hcomp.const_smul (S.a i * (-S.b i) ^ n)
  · intro i x hx
    rw [norm_smul, norm_seeley_coefficient]
    exact mul_le_mul_of_nonneg_left
      (hM _ (mul_nonneg_of_nonpos_of_nonpos (neg_nonpos.mpr (seeley_scale_nonneg S i)) hx))
      (mul_nonneg (abs_nonneg _) (pow_nonneg (seeley_scale_nonneg S i) n))

theorem continuous_seeleyExtensionJet (S : SeeleyData ι) {J : ℕ → ℝ → F}
    (hJ : IsBoundedHalfLineJet J) (n : ℕ) : Continuous (seeleyExtensionJet S J n) := by
  apply continuous_if_le continuous_const continuous_id (hJ.continuous n)
    (continuousOn_seeleyReflection S n (hJ.continuous n) (hJ.bounded n))
  intro x hx
  change (0 : ℝ) = x at hx
  subst x
  exact (seeleyReflection_at_zero S n (J n)).symm

private theorem hasDerivAt_seeleyReflection (S : SeeleyData ι) {J : ℕ → ℝ → F}
    (hJ : IsBoundedHalfLineJet J) (n : ℕ) {x : ℝ} (hx : x < 0) :
    HasDerivAt (seeleyReflection S n (J n)) (seeleyReflection S (n + 1) (J (n + 1)) x) x := by
  obtain ⟨M, hM⟩ := hJ.bounded (n + 1)
  unfold seeleyReflection
  refine hasDerivAt_tsum_of_isPreconnected
    (t := Iio (0 : ℝ))
    (g := fun i y => (S.a i * (-S.b i) ^ n) • J n (-S.b i * y))
    (g' := fun i y => (S.a i * (-S.b i) ^ (n + 1)) • J (n + 1) (-S.b i * y))
    (y₀ := x)
    ((S.summable_moment (n + 1)).mul_right M) isOpen_Iio (convex_Iio 0).isPreconnected
    ?_ ?_ hx (summable_seeleyReflection S n (hJ.bounded n) hx.le) hx
  · intro i y hy
    have hp : 0 < -S.b i * y := mul_pos_of_neg_of_neg
      (neg_neg_of_pos (seeley_scale_pos S i)) hy
    have hd := ((hJ.derivative n _ hp).scomp y ((hasDerivAt_id y).const_mul (-S.b i))).const_smul
      (S.a i * (-S.b i) ^ n)
    simpa only [Pi.smul_def, Function.comp_def, smul_smul, pow_succ, mul_assoc, mul_one] using hd
  · intro i y hy
    rw [norm_smul, norm_seeley_coefficient]
    exact mul_le_mul_of_nonneg_left
      (hM _ (mul_nonneg_of_nonpos_of_nonpos
        (neg_nonpos.mpr (seeley_scale_nonneg S i)) hy.le))
      (mul_nonneg (abs_nonneg _) (pow_nonneg (seeley_scale_nonneg S i) (n + 1)))

/-- The moment identities remove every boundary jump, so these are actual
derivatives on the entire real line, including zero. -/
theorem hasDerivAt_seeleyExtensionJet (S : SeeleyData ι) {J : ℕ → ℝ → F}
    (hJ : IsBoundedHalfLineJet J) (n : ℕ) (x : ℝ) :
    HasDerivAt (seeleyExtensionJet S J n) (seeleyExtensionJet S J (n + 1) x) x := by
  apply hasDerivAt_of_hasDerivAt_of_ne' (x := 0) _
    (continuous_seeleyExtensionJet S hJ n).continuousAt
    (continuous_seeleyExtensionJet S hJ (n + 1)).continuousAt x
  intro y hy
  rcases lt_or_gt_of_ne hy with hneg | hpos
  · rw [seeleyExtensionJet_of_neg S J (n + 1) hneg]
    apply (hasDerivAt_seeleyReflection S hJ n hneg).congr_of_eventuallyEq
    filter_upwards [isOpen_Iio.mem_nhds hneg] with z hz
    exact seeleyExtensionJet_of_neg S J n hz
  · rw [seeleyExtensionJet_of_nonneg S J (n + 1) hpos.le]
    apply (hJ.derivative n y hpos).congr_of_eventuallyEq
    filter_upwards [isOpen_Ioi.mem_nhds hpos] with z hz
    exact seeleyExtensionJet_of_nonneg S J n hz.le

theorem iteratedDeriv_seeleyExtend (S : SeeleyData ι) {J : ℕ → ℝ → F}
    (hJ : IsBoundedHalfLineJet J) (n : ℕ) :
    iteratedDeriv n (seeleyExtend S (J 0)) = seeleyExtensionJet S J n := by
  induction n with
  | zero => rw [iteratedDeriv_zero, seeleyExtensionJet_zero]
  | succ n ih =>
    rw [iteratedDeriv_succ, ih]
    exact funext fun x => (hasDerivAt_seeleyExtensionJet S hJ n x).deriv

/-- Seeley's single extension is smooth and retains every one-sided jet. -/
theorem contDiff_seeleyExtend (S : SeeleyData ι) {J : ℕ → ℝ → F}
    (hJ : IsBoundedHalfLineJet J) : ContDiff ℝ ∞ (seeleyExtend S (J 0)) := by
  apply contDiff_of_differentiable_iteratedDeriv
  intro n _
  rw [iteratedDeriv_seeleyExtend S hJ n]
  exact fun x => (hasDerivAt_seeleyExtensionJet S hJ n x).differentiableAt

theorem iteratedDeriv_seeleyExtend_of_nonneg (S : SeeleyData ι) {J : ℕ → ℝ → F}
    (hJ : IsBoundedHalfLineJet J) (n : ℕ) {x : ℝ} (hx : 0 ≤ x) :
    iteratedDeriv n (seeleyExtend S (J 0)) x = J n x := by
  rw [iteratedDeriv_seeleyExtend S hJ n, seeleyExtensionJet_of_nonneg S J n hx]

end ContinuousFlexibility.Analysis
