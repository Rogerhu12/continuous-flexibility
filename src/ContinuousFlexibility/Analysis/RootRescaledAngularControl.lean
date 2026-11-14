module

public import ContinuousFlexibility.Analysis.RootRegularizedFlow
public import ContinuousFlexibility.Analysis.N04FlowJetsTarget

/-!
# A common angular control for the actual rescaled root field

Both independent root parameters are scaled by the same fixed collar
size. Uniform first angular derivatives of the actual coefficient fields
then give a small angular Grönwall exponent. The collar is selected before
the state, and no higher parameter derivative enters this exponent.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set ContinuousFlexibility.Statements
open scoped ContDiff

set_option backward.isDefEq.respectTransparency false

def rootRescaledField (d c : PolarPoint → ℝ) (δ : ℝ) :
    ℝ × N04FlowPoint → ℝ :=
  fun q => rootRegularizedField d c
    (q.1, ((δ * q.2.1.1, δ * q.2.1.2), q.2.2))

theorem contDiff_rootRescaledField {d c : PolarPoint → ℝ}
    (hd : ContDiff ℝ ∞ d) (hc : ContDiff ℝ ∞ c) (δ : ℝ) :
    ContDiff ℝ ∞ (rootRescaledField d c δ) := by
  have hmap : ContDiff ℝ ∞ (fun q : ℝ × N04FlowPoint =>
      (q.1, ((δ * q.2.1.1, δ * q.2.1.2), q.2.2))) :=
    contDiff_fst.prodMk
      (((contDiff_const.mul contDiff_snd.fst.fst).prodMk
        (contDiff_const.mul contDiff_snd.fst.snd)).prodMk contDiff_snd.snd)
  exact (contDiff_rootRegularizedField hd hc).comp hmap

theorem rootRescaledField_periodic {d c : PolarPoint → ℝ} {T : ℝ}
    (hd : ∀ r, Function.Periodic (fun θ => d (r, θ)) T)
    (hc : ∀ r, Function.Periodic (fun θ => c (r, θ)) T)
    (δ t : ℝ) (v : ℝ × ℝ) :
    Function.Periodic (fun θ => rootRescaledField d c δ (t, (v, θ))) T :=
  rootRegularizedField_periodic hd hc t (δ * v.1, δ * v.2)

/-- The ordinary angular derivative of the actual rescaled field is
bounded by four times the collar size and the input angular bound. -/
theorem rootRescaledField_angular_deriv_le_at
    {d c : PolarPoint → ℝ} (hd : ContDiff ℝ ∞ d) (hc : ContDiff ℝ ∞ c)
    {δ M : ℝ} (hδ : 0 ≤ δ) (hM : 0 ≤ M)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1)
    {v : ℝ × ℝ} (hv : v ∈ n04FlowParameterBox) (θ : ℝ)
    (hdb : |deriv (fun η => d (δ * v.1 * t ^ 2, η)) θ| ≤ M)
    (hcb : |deriv (fun η => c (δ * v.1 * t ^ 2, η)) θ| ≤ M) :
    |deriv (fun η => rootRescaledField d c δ (t, (v, η))) θ| ≤ 4 * δ * M := by
  have htx : t ^ 2 ≤ 1 := by
    simpa only [pow_two, one_mul] using mul_le_mul ht.2 ht.2 ht.1 zero_le_one
  have hvx : |v.1| ≤ 1 := abs_le.mpr hv.1
  have hvζ : |v.2| ≤ 1 := abs_le.mpr hv.2
  have hx : |δ * v.1| ≤ δ := by
    rw [abs_mul, abs_of_nonneg hδ]
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hvx hδ
  have hζ : |δ * v.2| ≤ δ := by
    rw [abs_mul, abs_of_nonneg hδ]
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hvζ hδ
  have hA : |2 * (δ * v.1) * t| ≤ 2 * δ := by
    rw [abs_mul, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2),
      abs_of_nonneg ht.1]
    simpa only [mul_one] using mul_le_mul
      (mul_le_mul_of_nonneg_left hx (by norm_num : (0 : ℝ) ≤ 2)) ht.2
      ht.1 (mul_nonneg (by norm_num) hδ)
  have hB : |2 * (δ * v.2) * t ^ 2| ≤ 2 * δ := by
    rw [abs_mul, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2),
      abs_of_nonneg (sq_nonneg t)]
    simpa only [mul_one] using mul_le_mul
      (mul_le_mul_of_nonneg_left hζ (by norm_num : (0 : ℝ) ≤ 2)) htx
      (sq_nonneg t) (mul_nonneg (by norm_num) hδ)
  have hds : DifferentiableAt ℝ
      (fun η : ℝ => d (δ * v.1 * t ^ 2, η)) θ :=
    (hd.comp (contDiff_const.prodMk contDiff_id)).differentiable (by simp) θ
  have hcs : DifferentiableAt ℝ
      (fun η : ℝ => c (δ * v.1 * t ^ 2, η)) θ :=
    (hc.comp (contDiff_const.prodMk contDiff_id)).differentiable (by simp) θ
  have he : deriv (fun η => rootRescaledField d c δ (t, (v, η))) θ =
      (2 * (δ * v.1) * t) * deriv (fun η => d (δ * v.1 * t ^ 2, η)) θ +
        (2 * (δ * v.2) * t ^ 2) * deriv (fun η => c (δ * v.1 * t ^ 2, η)) θ := by
    exact ((hds.hasDerivAt.const_mul (2 * (δ * v.1) * t)).fun_add
      (hcs.hasDerivAt.const_mul (2 * (δ * v.2) * t ^ 2))).deriv
  rw [he]
  calc
    _ ≤ |2 * (δ * v.1) * t| * |deriv (fun η => d (δ * v.1 * t ^ 2, η)) θ| +
        |2 * (δ * v.2) * t ^ 2| * |deriv (fun η => c (δ * v.1 * t ^ 2, η)) θ| := by
      calc
        _ ≤ |(2 * (δ * v.1) * t) * deriv (fun η => d (δ * v.1 * t ^ 2, η)) θ| +
            |(2 * (δ * v.2) * t ^ 2) * deriv (fun η => c (δ * v.1 * t ^ 2, η)) θ| :=
          abs_add_le _ _
        _ = _ := congrArg₂ (fun x y : ℝ => x + y)
          (abs_mul (2 * (δ * v.1) * t) (deriv (fun η => d (δ * v.1 * t ^ 2, η)) θ))
          (abs_mul (2 * (δ * v.2) * t ^ 2) (deriv (fun η => c (δ * v.1 * t ^ 2, η)) θ))
    _ ≤ 2 * δ * M + 2 * δ * M :=
      add_le_add
        (mul_le_mul hA hdb (abs_nonneg _) (mul_nonneg (by norm_num) hδ))
        (mul_le_mul hB hcb (abs_nonneg _) (mul_nonneg (by norm_num) hδ))
    _ = 4 * δ * M := by ring

/-- The original symmetric-interval interface follows by evaluating
its coefficient bounds at the same physical point. -/
theorem rootRescaledField_angular_deriv_le
    {d c : PolarPoint → ℝ} (hd : ContDiff ℝ ∞ d) (hc : ContDiff ℝ ∞ c)
    {δ M : ℝ} (hδ : 0 ≤ δ) (hM : 0 ≤ M)
    (hdb : ∀ r, |r| ≤ δ → ∀ θ,
      |deriv (fun η => d (r, η)) θ| ≤ M)
    (hcb : ∀ r, |r| ≤ δ → ∀ θ,
      |deriv (fun η => c (r, η)) θ| ≤ M)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1)
    {v : ℝ × ℝ} (hv : v ∈ n04FlowParameterBox) (θ : ℝ) :
    |deriv (fun η => rootRescaledField d c δ (t, (v, η))) θ| ≤ 4 * δ * M := by
  have ht2 : t ^ 2 ≤ 1 := by
    simpa only [pow_two, one_mul] using mul_le_mul ht.2 ht.2 ht.1 zero_le_one
  have hr : |δ * v.1 * t ^ 2| ≤ δ := by
    rw [abs_mul, abs_mul, abs_of_nonneg hδ, abs_of_nonneg (sq_nonneg t)]
    calc
      _ ≤ δ * 1 * 1 := mul_le_mul
        (mul_le_mul_of_nonneg_left (abs_le.mpr hv.1) hδ) ht2
        (sq_nonneg t) (by simpa only [mul_one] using hδ)
      _ = δ := by ring
  exact rootRescaledField_angular_deriv_le_at hd hc hδ hM ht hv θ
    (hdb _ hr θ) (hcb _ hr θ)

/-- One collar gives the desired angular integral bound for every state
in the input family. The bounds used to choose it are only first angular
derivatives of the original two coefficient fields. -/
theorem exists_rootRescaledField_angularControl
    {Z : Type} {U : Set Z} (d c : Z → PolarPoint → ℝ)
    {ρ M Λ : ℝ} (hρ : 0 < ρ) (hM : 0 ≤ M) (hΛ : 0 < Λ)
    (hd : ∀ z ∈ U, ContDiff ℝ ∞ (d z))
    (hc : ∀ z ∈ U, ContDiff ℝ ∞ (c z))
    (hdb : ∀ z ∈ U, ∀ r, |r| ≤ ρ → ∀ θ,
      |deriv (fun η => d z (r, η)) θ| ≤ M)
    (hcb : ∀ z ∈ U, ∀ r, |r| ≤ ρ → ∀ θ,
      |deriv (fun η => c z (r, η)) θ| ≤ M) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ ρ ∧ δ ≤ 1 ∧
      ∀ z ∈ U, N04FlowAngularControl (rootRescaledField (d z) (c z) δ) Λ := by
  let δ := min ρ (min 1 (Λ / (4 * (M + 1))))
  have hden : 0 < 4 * (M + 1) := by positivity
  have hδ : 0 < δ := lt_min hρ (lt_min zero_lt_one (div_pos hΛ hden))
  have hδρ : δ ≤ ρ := min_le_left _ _
  have hδone : δ ≤ 1 := (min_le_right _ _).trans (min_le_left _ _)
  have hδbound : δ ≤ Λ / (4 * (M + 1)) :=
    (min_le_right _ _).trans (min_le_right _ _)
  have hsmall : 4 * δ * M ≤ Λ := by
    have h := (le_div_iff₀ hden).mp hδbound
    nlinarith only [h, hδ.le]
  refine ⟨δ, hδ, hδρ, hδone, ?_⟩
  intro z hz
  refine ⟨fun _ => Λ, continuousOn_const, fun _ _ => hΛ.le, ?_, ?_⟩
  · intro t ht v hv θ
    exact (rootRescaledField_angular_deriv_le (hd z hz) (hc z hz) hδ.le hM
      (fun r hr => hdb z hz r (hr.trans hδρ))
      (fun r hr => hcb z hz r (hr.trans hδρ)) ht hv θ).trans hsmall
  · simp only [intervalIntegral.integral_const, sub_zero, one_smul, le_refl]

end ContinuousFlexibility.Analysis
