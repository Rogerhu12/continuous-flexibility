module

public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.Analysis.Calculus.Deriv.Slope
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring

/-!
# Uniform first variation of an actual flow about a radial speed

The reference speed depends only on the interval variable. An actual
trajectory's integral equation and a uniform velocity expansion therefore
give its first variation directly. First bound the trajectory displacement
by the interval length times the velocity displacement. Then use only the
Lipschitz bound of the first-order velocity to replace the perturbed
trajectory in that first-order term by the reference translation.

No parameter derivative of the trajectory, angular derivative of the
remainder, or parameter regularity of a chosen chart is assumed. Applying
these lemmas to an N04b witness still requires constructing the actual
trajectories and proving their integral equations and velocity bounds.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter MeasureTheory
open scoped Topology

/-- The actual reference trajectory for an angle-independent speed. -/
def n04bFlowReference (v₀ : ℝ → ℝ) (a t θ : ℝ) : ℝ :=
  θ + ∫ r in a..t, v₀ r

/-- Integrate the first-order velocity along the reference trajectory. -/
def n04bFlowFirstVariation (v₀ : ℝ → ℝ) (v₁ : ℝ → ℝ → ℝ)
    (a t θ : ℝ) : ℝ :=
  ∫ r in a..t, v₁ r (n04bFlowReference v₀ a r θ)

private theorem n04b_flow_integrable_initial_segment
    {f : ℝ → ℝ} {a b t : ℝ} (hab : a ≤ b)
    (hf : IntervalIntegrable f volume a b) (ht : t ∈ Icc a b) :
    IntervalIntegrable f volume a t := by
  apply hf.mono_set
  rw [uIcc_of_le ht.1, uIcc_of_le hab]
  exact Icc_subset_Icc le_rfl ht.2

private theorem n04b_flow_abs_integral_le
    {f : ℝ → ℝ} {a b C : ℝ} (hab : a ≤ b)
    (hbound : ∀ r ∈ Icc a b, |f r| ≤ C) :
    |∫ r in a..b, f r| ≤ (b - a) * C := by
  have hnorm : ‖∫ r in a..b, f r‖ ≤ C * |b - a| := by
    apply intervalIntegral.norm_integral_le_of_norm_le_const
    intro r hr
    have hr' : r ∈ Ioc a b := by simpa only [uIoc_of_le hab] using hr
    simpa only [Real.norm_eq_abs] using hbound r ⟨hr'.1.le, hr'.2⟩
  simpa only [Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr hab), mul_comm]
    using hnorm

/-- Uniform zeroth-order displacement control, obtained from the actual
integral equation. The same bound works at every intermediate time and
every initial angle. -/
theorem n04b_flow_reference_displacement_bound
    (V Y : ℝ → ℝ → ℝ) (v₀ : ℝ → ℝ) (v₁ : ℝ → ℝ → ℝ)
    (a b q η M : ℝ) (hab : a ≤ b) (hη : 0 ≤ η) (hM : 0 ≤ M)
    (h₀ : IntervalIntegrable v₀ volume a b)
    (hV : ∀ θ, IntervalIntegrable (fun r => V r (Y r θ)) volume a b)
    (hflow : ∀ θ t, t ∈ Icc a b →
      Y t θ = θ + ∫ r in a..t, V r (Y r θ))
    (hfirst : ∀ r ∈ Icc a b, ∀ θ, |v₁ r θ| ≤ M)
    (hrem : ∀ r ∈ Icc a b, ∀ θ,
      |V r θ - v₀ r - q * v₁ r θ| ≤ |q| * η)
    (θ t : ℝ) (ht : t ∈ Icc a b) :
    |Y t θ - n04bFlowReference v₀ a t θ| ≤
      (b - a) * |q| * (M + η) := by
  have hVt := n04b_flow_integrable_initial_segment hab (hV θ) ht
  have h₀t := n04b_flow_integrable_initial_segment hab h₀ ht
  have he : Y t θ - n04bFlowReference v₀ a t θ =
      ∫ r in a..t, V r (Y r θ) - v₀ r := by
    rw [hflow θ t ht, n04bFlowReference, intervalIntegral.integral_sub hVt h₀t]
    ring
  have hpoint (r : ℝ) (hr : r ∈ Icc a b) :
      |V r (Y r θ) - v₀ r| ≤ |q| * (M + η) := by
    calc
      _ = |(V r (Y r θ) - v₀ r - q * v₁ r (Y r θ)) +
          q * v₁ r (Y r θ)| := by congr 1; ring
      _ ≤ |V r (Y r θ) - v₀ r - q * v₁ r (Y r θ)| +
          |q * v₁ r (Y r θ)| := abs_add_le _ _
      _ ≤ |q| * η + |q| * M := by
        rw [abs_mul]
        exact add_le_add (hrem r hr (Y r θ))
          (mul_le_mul_of_nonneg_left (hfirst r hr (Y r θ)) (abs_nonneg q))
      _ = _ := by ring
  rw [he]
  calc
    _ ≤ (t - a) * (|q| * (M + η)) :=
      n04b_flow_abs_integral_le ht.1
        (fun r hr => hpoint r ⟨hr.1, hr.2.trans ht.2⟩)
    _ ≤ (b - a) * (|q| * (M + η)) :=
      mul_le_mul_of_nonneg_right (by linarith [ht.2])
        (mul_nonneg (abs_nonneg q) (add_nonneg hM hη))
    _ = _ := by ring

/-- A uniform velocity remainder `|q|η` produces an explicit uniform
trajectory remainder `length*|q|η + length²*q²*L*(M+η)`.
The first-order term is evaluated on the reference trajectory, and no
trajectory derivative is a premise. -/
theorem n04b_flow_first_variation_bound
    (V Y : ℝ → ℝ → ℝ) (v₀ : ℝ → ℝ) (v₁ : ℝ → ℝ → ℝ)
    (a b q η M L : ℝ) (hab : a ≤ b)
    (hη : 0 ≤ η) (hM : 0 ≤ M) (hL : 0 ≤ L)
    (h₀ : IntervalIntegrable v₀ volume a b)
    (hV : ∀ θ, IntervalIntegrable (fun r => V r (Y r θ)) volume a b)
    (h₁ : ∀ θ, IntervalIntegrable
      (fun r => v₁ r (n04bFlowReference v₀ a r θ)) volume a b)
    (hflow : ∀ θ t, t ∈ Icc a b →
      Y t θ = θ + ∫ r in a..t, V r (Y r θ))
    (hfirst : ∀ r ∈ Icc a b, ∀ θ, |v₁ r θ| ≤ M)
    (hLip : ∀ r ∈ Icc a b, ∀ θ φ, |v₁ r θ - v₁ r φ| ≤ L * |θ - φ|)
    (hrem : ∀ r ∈ Icc a b, ∀ θ,
      |V r θ - v₀ r - q * v₁ r θ| ≤ |q| * η)
    (θ t : ℝ) (ht : t ∈ Icc a b) :
    |Y t θ - n04bFlowReference v₀ a t θ -
        q * n04bFlowFirstVariation v₀ v₁ a t θ| ≤
      (b - a) * |q| * η + (b - a) ^ 2 * q ^ 2 * L * (M + η) := by
  have hdisp := n04b_flow_reference_displacement_bound
    V Y v₀ v₁ a b q η M hab hη hM h₀ hV hflow hfirst hrem
  have hVt := n04b_flow_integrable_initial_segment hab (hV θ) ht
  have h₀t := n04b_flow_integrable_initial_segment hab h₀ ht
  have h₁t := n04b_flow_integrable_initial_segment hab (h₁ θ) ht
  have he : Y t θ - n04bFlowReference v₀ a t θ -
        q * n04bFlowFirstVariation v₀ v₁ a t θ =
      ∫ r in a..t,
        V r (Y r θ) - v₀ r - q * v₁ r (n04bFlowReference v₀ a r θ) := by
    rw [intervalIntegral.integral_sub (hVt.sub h₀t) (h₁t.const_mul q),
      intervalIntegral.integral_sub hVt h₀t, intervalIntegral.integral_const_mul,
      hflow θ t ht, n04bFlowReference, n04bFlowFirstVariation]
    ring
  let C := |q| * η + |q| * (L * ((b - a) * |q| * (M + η)))
  have hC : 0 ≤ C := by
    dsimp only [C]
    exact add_nonneg (mul_nonneg (abs_nonneg q) hη)
      (mul_nonneg (abs_nonneg q) (mul_nonneg hL
        (mul_nonneg (mul_nonneg (sub_nonneg.mpr hab) (abs_nonneg q))
          (add_nonneg hM hη))))
  have hpoint (r : ℝ) (hr : r ∈ Icc a b) :
      |V r (Y r θ) - v₀ r - q * v₁ r (n04bFlowReference v₀ a r θ)| ≤ C := by
    calc
      _ = |(V r (Y r θ) - v₀ r - q * v₁ r (Y r θ)) +
          q * (v₁ r (Y r θ) - v₁ r (n04bFlowReference v₀ a r θ))| := by
        congr 1
        ring
      _ ≤ |V r (Y r θ) - v₀ r - q * v₁ r (Y r θ)| +
          |q * (v₁ r (Y r θ) - v₁ r (n04bFlowReference v₀ a r θ))| :=
        abs_add_le _ _
      _ ≤ |q| * η + |q| * (L * |Y r θ - n04bFlowReference v₀ a r θ|) := by
        rw [abs_mul]
        exact add_le_add (hrem r hr (Y r θ))
          (mul_le_mul_of_nonneg_left
            (hLip r hr (Y r θ) (n04bFlowReference v₀ a r θ)) (abs_nonneg q))
      _ ≤ C := add_le_add le_rfl (mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left (hdisp θ r hr) hL) (abs_nonneg q))
  rw [he]
  calc
    _ ≤ (t - a) * C := n04b_flow_abs_integral_le ht.1
      (fun r hr => hpoint r ⟨hr.1, hr.2.trans ht.2⟩)
    _ ≤ (b - a) * C := mul_le_mul_of_nonneg_right (by linarith [ht.2]) hC
    _ = _ := by
      dsimp only [C]
      rw [← sq_abs q]
      ring

end ContinuousFlexibility.Analysis
