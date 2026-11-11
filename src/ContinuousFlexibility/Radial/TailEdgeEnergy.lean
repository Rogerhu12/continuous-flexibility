import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Dirichlet energy on a resistance edge

On an edge with both endpoint values zero, the evaluation bound has the
diagonal of the zero-potential Dirichlet Green function as its constant.
Integrating gives the small relative bound used for the exact edge inverse.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open Set MeasureTheory
open scoped ContDiff

/-- The zero-potential Dirichlet Green function in resistance coordinates. -/
def tailEdgeGreen (a b s t : ℝ) : ℝ :=
  (min s t - a) * (b - max s t) / (b - a)

theorem tailEdgeGreen_self (a b s : ℝ) :
    tailEdgeGreen a b s s = (s - a) * (b - s) / (b - a) := by
  simp only [tailEdgeGreen, min_self, max_self]

private theorem integral_sq_ge_mean_sq {g : ℝ → ℝ} (hg : Continuous g)
    {a b : ℝ} (hab : a ≤ b) :
    (∫ t in a..b, g t) ^ 2 ≤ (b - a) * ∫ t in a..b, g t ^ 2 := by
  obtain rfl | hlt := hab.eq_or_lt
  · simp
  let I : ℝ := ∫ t in a..b, g t
  let c : ℝ := I / (b - a)
  have hc : c * (b - a) = I := div_mul_cancel₀ _ (sub_pos.mpr hlt).ne'
  have hdecomp : (fun t => (g t - c) ^ 2) =
      (fun t => (g t ^ 2 - (2 * c) * g t) + c ^ 2) := by
    funext t
    ring
  have h1 : IntervalIntegrable (fun t => g t ^ 2) volume a b :=
    (hg.pow 2).intervalIntegrable a b
  have h2 : IntervalIntegrable (fun t => (2 * c) * g t) volume a b :=
    (continuous_const.mul hg).intervalIntegrable a b
  have h3 : IntervalIntegrable (fun _ : ℝ => c ^ 2) volume a b :=
    continuous_const.intervalIntegrable a b
  have hnn := intervalIntegral.integral_nonneg_of_forall (μ := volume) hab
    (fun t => sq_nonneg (g t - c))
  rw [hdecomp, intervalIntegral.integral_add (h1.sub h2) h3,
    intervalIntegral.integral_sub h1 h2, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const, smul_eq_mul] at hnn
  change 0 ≤ (∫ t in a..b, g t ^ 2) - (2 * c) * I + (b - a) * c ^ 2 at hnn
  have hz : (b - a) * c ^ 2 = c * I := calc
    _ = c * (c * (b - a)) := by ring
    _ = c * I := by rw [hc]
  rw [hz] at hnn
  have hbound : c * I ≤ ∫ t in a..b, g t ^ 2 := by linarith only [hnn]
  calc
    I ^ 2 = (c * (b - a)) * I := by rw [hc]; ring
    _ = (b - a) * (c * I) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hbound (sub_nonneg.mpr hab)

/-- The sharp Dirichlet point-evaluation bound follows from the two
fundamental theorem of calculus identities with the same endpoint value. -/
theorem tailEdge_value_sq_le_green_energy {a b s : ℝ} {u : ℝ → ℝ}
    (hab : a < b) (hs : s ∈ Icc a b) (hu : ContDiff ℝ 1 u)
    (hua : u a = 0) (hub : u b = 0) :
    u s ^ 2 ≤ tailEdgeGreen a b s s * ∫ t in a..b, deriv u t ^ 2 := by
  have hd : Continuous (deriv u) := hu.continuous_deriv (by simp)
  have hf (l h : ℝ) : (∫ t in l..h, deriv u t) = u h - u l :=
    intervalIntegral.integral_deriv_eq_sub (fun t _ => hu.differentiable (by simp) t)
      (hd.intervalIntegrable l h)
  have hl := integral_sq_ge_mean_sq hd hs.1
  have hr := integral_sq_ge_mean_sq hd hs.2
  rw [hf, hua, sub_zero] at hl
  rw [hf, hub, zero_sub, neg_sq] at hr
  have hleft := mul_le_mul_of_nonneg_left hl (sub_nonneg.mpr hs.2)
  have hright := mul_le_mul_of_nonneg_left hr (sub_nonneg.mpr hs.1)
  have hadd : (∫ t in a..s, deriv u t ^ 2) + (∫ t in s..b, deriv u t ^ 2) =
      ∫ t in a..b, deriv u t ^ 2 :=
    intervalIntegral.integral_add_adjacent_intervals
      ((hd.pow 2).intervalIntegrable a s) ((hd.pow 2).intervalIntegrable s b)
  have hprod : (b - a) * u s ^ 2 ≤
      (s - a) * (b - s) * ∫ t in a..b, deriv u t ^ 2 := by
    rw [← hadd]
    calc
      _ = (b - s) * u s ^ 2 + (s - a) * u s ^ 2 := by ring
      _ ≤ (b - s) * ((s - a) * ∫ t in a..s, deriv u t ^ 2) +
          (s - a) * ((b - s) * ∫ t in s..b, deriv u t ^ 2) :=
        add_le_add hleft hright
      _ = _ := by ring
  rw [tailEdgeGreen_self, div_mul_eq_mul_div]
  exact (le_div_iff₀ (sub_pos.mpr hab)).mpr (by simpa only [mul_comm] using hprod)

/-- The exact smallness parameter on one edge controls the relative mass
form for any smooth Dirichlet test function. -/
theorem tailEdge_weighted_energy_bound {a b Λ : ℝ} {u density : ℝ → ℝ}
    (hab : a < b) (hΛ : 0 ≤ Λ) (hu : ContDiff ℝ 1 u) (hua : u a = 0) (hub : u b = 0)
    (hdensity : ContinuousOn density (Icc a b)) (hdensity₀ : ∀ s ∈ Icc a b, 0 ≤ density s) :
    Λ * (∫ s in a..b, density s * u s ^ 2) ≤
      (Λ * ∫ s in a..b, density s * tailEdgeGreen a b s s) *
        ∫ s in a..b, deriv u s ^ 2 := by
  let E : ℝ := ∫ s in a..b, deriv u s ^ 2
  have hG : Continuous (fun s => tailEdgeGreen a b s s) := by
    simp only [tailEdgeGreen_self]
    exact (((continuous_id.sub continuous_const).mul
      (continuous_const.sub continuous_id)).div_const _)
  have h1 : IntervalIntegrable (fun s => density s * u s ^ 2) volume a b :=
    (hdensity.mul (hu.continuous.pow 2).continuousOn).intervalIntegrable_of_Icc hab.le
  have h2 : IntervalIntegrable (fun s => (density s * tailEdgeGreen a b s s) * E) volume a b :=
    ((hdensity.mul hG.continuousOn).mul continuousOn_const).intervalIntegrable_of_Icc hab.le
  have hle := intervalIntegral.integral_mono_on hab.le h1 h2 (fun s hs => by
    rw [mul_assoc]
    exact mul_le_mul_of_nonneg_left (tailEdge_value_sq_le_green_energy hab hs hu hua hub)
      (hdensity₀ s hs))
  rw [intervalIntegral.integral_mul_const] at hle
  exact (mul_le_mul_of_nonneg_left hle hΛ).trans_eq (by ring)

end ContinuousFlexibility.Radial
