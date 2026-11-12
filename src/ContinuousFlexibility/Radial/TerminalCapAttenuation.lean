import ContinuousFlexibility.Radial.TerminalCapLift
import ContinuousFlexibility.Radial.PositiveBufferComparison
import ContinuousFlexibility.Radial.InnerBufferDerivative

/-!
# Attenuation of the same terminal cap through a Liouville coordinate

A genuine Dirichlet solution of p'' = q p, with q ≥ m², is compared
with the inward exponential. A local potential bound on a layer of
width 1/m then controls its derivative. Finally the identity
u (R x) = s x * p x and the actual derivative of R transport both
estimates to the physical solution used by TerminalCapLift.

No exponential bound on p, u, or their derivatives is assumed. The
remaining geometric inputs are the cap equation, its endpoint values,
the lower and layer upper potential bounds, and the Liouville identity.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open Set Filter Real
open scoped Topology ContDiff

/-- The actual positive-cap equation controls both jets on the cutoff
layer. The height is estimated on a complete layer before applying the
derivative estimate, so there is no hidden derivative hypothesis. -/
theorem terminalCap_model_layer_bounds {a b x m A C : ℝ} {p q : ℝ → ℝ}
    (hm : 0 < m) (hA : 0 ≤ A) (hC : 0 ≤ C)
    (hx : a ≤ x) (hxb : x + 1 / m ≤ b)
    (hp : ∀ y ∈ Icc a b, ContDiffAt ℝ ∞ p y)
    (heq : ∀ y ∈ Icc a b, deriv (deriv p) y = q y * p y)
    (hqlower : ∀ y ∈ Icc a b, m ^ 2 ≤ q y)
    (hqupper : ∀ y ∈ Icc x (x + 1 / m), |q y| ≤ C * m ^ 2)
    (hleft : p a = A) (hwall : p b = 0) :
    |p x| ≤ A * exp (-(m * (x - a))) ∧
      |deriv p x| ≤ (2 + C) * m * (A * exp (-(m * (x - a)))) := by
  have hc : ContinuousOn p (Icc a b) :=
    fun y hy => (hp y hy).continuousAt.continuousWithinAt
  have hd : ∀ y ∈ Ioo a b, HasDerivAt p (deriv p y) y :=
    fun y hy => ((hp y (Ioo_subset_Icc_self hy)).differentiableAt (by simp)).hasDerivAt
  have hdd : ∀ y ∈ Ioo a b, HasDerivAt (deriv p) (q y * p y) y := by
    intro y hy
    rw [← heq y (Ioo_subset_Icc_self hy)]
    exact (((hp y (Ioo_subset_Icc_self hy)).derivWithin (m := ∞) (by simp)).differentiableAt
      (by simp)).hasDerivAt
  have hnonneg := positiveBuffer_solution_nonneg hc hd hdd
    (fun y hy => (sq_pos_of_pos hm).trans_le (hqlower y (Ioo_subset_Icc_self hy)))
    (by rw [hleft]; exact hA) (by rw [hwall])
  have hexp := positiveBuffer_dirichlet_exponential_bound hm hA hc hd hdd
    (fun y hy => hqlower y (Ioo_subset_Icc_self hy))
    (by rw [hleft]) (by rw [hwall])
  have hsub : Icc x (x + 1 / m) ⊆ Icc a b := Icc_subset_Icc hx hxb
  have hheight : ∀ y ∈ Icc x (x + 1 / m), |p y| ≤ A * exp (-(m * (x - a))) := by
    intro y hy
    rw [abs_of_nonneg (hnonneg y (hsub hy))]
    refine (hexp y (hsub hy)).trans (mul_le_mul_of_nonneg_left (exp_le_exp.mpr ?_) hA)
    nlinarith only [mul_le_mul_of_nonneg_left hy.1 hm.le]
  have hxin : x ∈ Icc x (x + 1 / m) :=
    ⟨le_rfl, le_add_of_nonneg_right (one_div_nonneg.mpr hm.le)⟩
  refine ⟨hheight x hxin, ?_⟩
  exact innerBuffer_mass_scale_derivative hm (mul_nonneg hA (exp_pos _).le) hC
    (fun y hy => (hp y (hsub hy)).differentiableAt (by simp))
    (fun y hy => ((hp y (hsub hy)).derivWithin (m := ∞) (by simp)).differentiableAt (by simp))
    hheight hqupper (fun y hy => heq y (hsub hy))

/-- The derivative identity uses the same physical solution, coordinate
map, and amplitude as the pointwise Liouville identity. -/
theorem terminalCap_liouville_derivative {x ρ : ℝ} {u R s p : ℝ → ℝ}
    (hR : HasDerivAt R ρ x) (hu : DifferentiableAt ℝ u (R x))
    (hs : DifferentiableAt ℝ s x) (hp : DifferentiableAt ℝ p x)
    (hidentity : (fun y => u (R y)) =ᶠ[𝓝 x] fun y => s y * p y) :
    deriv u (R x) * ρ = deriv s x * p x + s x * deriv p x := by
  have hc := hu.hasDerivAt.comp x hR
  have ht := (hs.hasDerivAt.mul hp.hasDerivAt).congr_of_eventuallyEq hidentity
  exact hc.unique ht

/-- Transfer the derived model attenuation to the actual physical
height and its radial derivative on this cap. -/
theorem terminalCap_liouville_layer_bounds {a b x m A C S S₁ ρ : ℝ}
    {p q u R s : ℝ → ℝ}
    (hm : 0 < m) (hA : 0 ≤ A) (hC : 0 ≤ C)
    (hx : a ≤ x) (hxb : x + 1 / m ≤ b)
    (hp : ∀ y ∈ Icc a b, ContDiffAt ℝ ∞ p y)
    (heq : ∀ y ∈ Icc a b, deriv (deriv p) y = q y * p y)
    (hqlower : ∀ y ∈ Icc a b, m ^ 2 ≤ q y)
    (hqupper : ∀ y ∈ Icc x (x + 1 / m), |q y| ≤ C * m ^ 2)
    (hleft : p a = A) (hwall : p b = 0)
    (hR : HasDerivAt R ρ x) (hρ : ρ ≠ 0)
    (hu : DifferentiableAt ℝ u (R x)) (hs : DifferentiableAt ℝ s x)
    (hidentity : (fun y => u (R y)) =ᶠ[𝓝 x] fun y => s y * p y)
    (hs₀ : |s x| ≤ S) (hs₁ : |deriv s x| ≤ S₁) :
    |u (R x)| ≤ (S * A) * exp (-(m * (x - a))) ∧
      |deriv u (R x)| ≤
        ((S₁ + S * (2 + C) * m) * A / |ρ|) * exp (-(m * (x - a))) := by
  have hjet := terminalCap_model_layer_bounds hm hA hC hx hxb hp heq
    hqlower hqupper hleft hwall
  have hS : 0 ≤ S := (abs_nonneg _).trans hs₀
  have hS₁ : 0 ≤ S₁ := (abs_nonneg _).trans hs₁
  have hxclosed : x ∈ Icc a b :=
    ⟨hx, (le_add_of_nonneg_right (one_div_nonneg.mpr hm.le)).trans hxb⟩
  have hderiv := terminalCap_liouville_derivative hR hu hs
    ((hp x hxclosed).differentiableAt (by simp)) hidentity
  have hvalue : u (R x) = s x * p x := hidentity.eq_of_nhds
  constructor
  · rw [hvalue, abs_mul]
    calc
      _ ≤ S * (A * exp (-(m * (x - a)))) :=
        mul_le_mul hs₀ hjet.1 (abs_nonneg _) hS
      _ = _ := by ring
  · have hprod : |deriv u (R x)| * |ρ| ≤
        (S₁ + S * (2 + C) * m) * A * exp (-(m * (x - a))) := by
      calc
        _ = |deriv s x * p x + s x * deriv p x| := by rw [← abs_mul, hderiv]
        _ ≤ |deriv s x * p x| + |s x * deriv p x| := abs_add_le _ _
        _ = |deriv s x| * |p x| + |s x| * |deriv p x| := by rw [abs_mul, abs_mul]
        _ ≤ S₁ * (A * exp (-(m * (x - a)))) +
            S * ((2 + C) * m * (A * exp (-(m * (x - a))))) :=
          add_le_add (mul_le_mul hs₁ hjet.1 (abs_nonneg _) hS₁)
            (mul_le_mul hs₀ hjet.2 (abs_nonneg _) hS)
        _ = _ := by ring
    calc
      _ ≤ ((S₁ + S * (2 + C) * m) * A * exp (-(m * (x - a)))) / |ρ| :=
        (le_div_iff₀ (abs_pos.mpr hρ)).mpr hprod
      _ = _ := by ring

/-- Combining the actual cap comparison with the actual Jacobi
commutator supplies the attenuated residual, with no residual smallness
hypothesis and no independently chosen physical solution. -/
theorem terminalCap_residual_from_liouville
    {a b x m A C S S₁ ρ lam W W₁ C₁ C₂ : ℝ} {p q u R s w χ : ℝ → ℝ}
    (hm : 0 < m) (hA : 0 ≤ A) (hC : 0 ≤ C)
    (hx : a ≤ x) (hxb : x + 1 / m ≤ b)
    (hp : ∀ y ∈ Icc a b, ContDiffAt ℝ ∞ p y)
    (heq : ∀ y ∈ Icc a b, deriv (deriv p) y = q y * p y)
    (hqlower : ∀ y ∈ Icc a b, m ^ 2 ≤ q y)
    (hqupper : ∀ y ∈ Icc x (x + 1 / m), |q y| ≤ C * m ^ 2)
    (hleft : p a = A) (hwall : p b = 0)
    (hR : HasDerivAt R ρ x) (hρ : ρ ≠ 0)
    (hu : DifferentiableAt ℝ u (R x)) (hs : DifferentiableAt ℝ s x)
    (hidentity : (fun y => u (R y)) =ᶠ[𝓝 x] fun y => s y * p y)
    (hs₀ : |s x| ≤ S) (hs₁ : |deriv s x| ≤ S₁)
    (hlam : 0 < lam) (hw : |w (R x)| ≤ W) (hw₁ : |deriv w (R x)| ≤ W₁)
    (hχ₁ : |deriv χ (R x)| ≤ C₁) (hχ₂ : |deriv (deriv χ) (R x)| ≤ C₂) :
    |terminalCapResidual lam w χ u (R x)| ≤
      ((2 * W * C₁ * ((S₁ + S * (2 + C) * m) * A / |ρ|) +
        (W₁ * C₁ + W * C₂) * (S * A)) / sqrt lam) * exp (-(m * (x - a))) := by
  have hjet := terminalCap_liouville_layer_bounds hm hA hC hx hxb hp heq hqlower hqupper
    hleft hwall hR hρ hu hs hidentity hs₀ hs₁
  exact terminalCapResidual_abs_le hlam hw hw₁ hχ₁ hχ₂ hjet.1 hjet.2

end ContinuousFlexibility.Radial
