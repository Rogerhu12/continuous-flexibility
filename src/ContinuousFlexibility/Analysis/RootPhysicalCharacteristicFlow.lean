import ContinuousFlexibility.Analysis.RootFlowSymmetry
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Ordinary physical characteristics behind the regularized root flow

For any fixed signed parameter σ, the physical speed is
d(r,θ) + σ sqrt(r) c₀(r,θ). It is continuous in time at the root and has
a continuous periodic actual angular derivative, which is sufficient for
the existing Picard construction. The substitution r = x t² converts
its genuine closed-interval ODE to the displayed regularized root ODE
at the parameter ζ = σ x^(3/2), including t = 0. Uniqueness identifies
the time-one maps without assuming their differential equation in x.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set
open scoped ContDiff

set_option backward.isDefEq.respectTransparency false

def rootPhysicalSpeed (d c₀ : ℝ × ℝ → ℝ) (σ : ℝ) (p : ℝ × ℝ) : ℝ :=
  d p + σ * Real.sqrt p.1 * c₀ p

/-- Picard requires time continuity, so the square root at the initial
time causes no loss in the construction of actual physical trajectories. -/
theorem exists_rootPhysicalFlow_on_Icc
    {d c₀ : ℝ × ℝ → ℝ} {R T : ℝ}
    (hR : 0 ≤ R) (hT : T ≠ 0)
    (hd : ContDiff ℝ ∞ d) (hc₀ : ContDiff ℝ ∞ c₀)
    (hdperiod : ∀ r, Function.Periodic (fun θ => d (r, θ)) T)
    (hc₀period : ∀ r, Function.Periodic (fun θ => c₀ (r, θ)) T)
    (σ : ℝ) :
    ∃ Φ : ℝ → ℝ → ℝ,
      (∀ θ, Φ θ 0 = θ) ∧
      (∀ θ r, r ∈ Icc (0 : ℝ) R →
        HasDerivWithinAt (Φ θ) (rootPhysicalSpeed d c₀ σ (r, Φ θ r))
          (Icc (0 : ℝ) R) r) ∧
      (∀ θ r, r ∈ Icc (0 : ℝ) R → Φ (θ + T) r = Φ θ r + T) := by
  let D : ℝ × ℝ → ℝ := fun p =>
    fderiv ℝ d p (0, 1) + σ * Real.sqrt p.1 * fderiv ℝ c₀ p (0, 1)
  have hFd : Continuous (fun p : ℝ × ℝ => fderiv ℝ d p (0, 1)) :=
    (hd.continuous_fderiv (by simp)).clm_apply continuous_const
  have hFc : Continuous (fun p : ℝ × ℝ => fderiv ℝ c₀ p (0, 1)) :=
    (hc₀.continuous_fderiv (by simp)).clm_apply continuous_const
  have hs : Continuous (fun p : ℝ × ℝ => σ * Real.sqrt p.1) :=
    continuous_const.mul (Real.continuous_sqrt.comp continuous_fst)
  apply exists_periodicScalarFlow_on_Icc (F := rootPhysicalSpeed d c₀ σ) (D := D) hR hT
    (hd.continuous.add (hs.mul hc₀.continuous)).continuousOn
    (hFd.add (hs.mul hFc)).continuousOn
  · intro r _ θ
    simp only [rootPhysicalSpeed, hdperiod r θ, hc₀period r θ]
  · intro r _ θ
    dsimp only [D]
    rw [fderiv_periodic_snd hdperiod r θ, fderiv_periodic_snd hc₀period r θ]
  · intro r _ θ
    have hp : HasDerivAt (fun η : ℝ => (r, η)) (0, 1) θ :=
      (hasDerivAt_const θ r).prodMk (hasDerivAt_id θ)
    have hdd := (hd.differentiable (by simp) (r, θ)).hasFDerivAt.comp_hasDerivAt θ hp
    have hcd := (hc₀.differentiable (by simp) (r, θ)).hasFDerivAt.comp_hasDerivAt θ hp
    have he (f : ℝ × ℝ → ℝ) :
        f ∘ (fun η : ℝ => (r, η)) = (fun η : ℝ => f (r, η)) := by
      funext η
      exact Function.comp_apply
    rw [he] at hdd hcd
    exact hdd.fun_add (hcd.const_mul (σ * Real.sqrt r))

theorem rpow_three_halves_eq_mul_sqrt {x : ℝ} (hx : 0 ≤ x) :
    x ^ (3 / 2 : ℝ) = x * Real.sqrt x := by
  rw [show (3 / 2 : ℝ) = (1 : ℝ) + 1 / 2 by norm_num,
    Real.rpow_add' (y := (1 : ℝ)) (z := (1 / 2 : ℝ)) hx (by norm_num),
    Real.rpow_one, ← Real.sqrt_eq_rpow]

theorem root_squareTime_mem {x R t : ℝ}
    (hx : x ∈ Icc (0 : ℝ) R) (ht : t ∈ Icc (0 : ℝ) 1) :
    x * t ^ 2 ∈ Icc (0 : ℝ) R := by
  have ht1 : t ^ 2 ≤ 1 := by
    simpa only [pow_two, mul_one] using mul_le_mul ht.2 ht.2 ht.1 zero_le_one
  refine ⟨mul_nonneg hx.1 (sq_nonneg t), ?_⟩
  calc
    x * t ^ 2 ≤ x * 1 := mul_le_mul_of_nonneg_left ht1 hx.1
    _ = x := mul_one x
    _ ≤ R := hx.2

/-- The exact chain rule holds at both endpoints of the time interval. -/
theorem rootPhysicalFlow_squareTime_hasDerivWithinAt
    {d c₀ : ℝ × ℝ → ℝ} {Φ : ℝ → ℝ → ℝ} {σ R x t : ℝ}
    (hΦ : ∀ θ r, r ∈ Icc (0 : ℝ) R →
      HasDerivWithinAt (Φ θ) (rootPhysicalSpeed d c₀ σ (r, Φ θ r))
        (Icc (0 : ℝ) R) r)
    (hx : x ∈ Icc (0 : ℝ) R) (ht : t ∈ Icc (0 : ℝ) 1) (θ : ℝ) :
    HasDerivWithinAt (fun s => Φ θ (x * s ^ 2))
      (rootRegularizedField d c₀
        (t, ((x, σ * x ^ (3 / 2 : ℝ)), Φ θ (x * t ^ 2))))
      (Icc (0 : ℝ) 1) t := by
  have hg : HasDerivAt (fun s : ℝ => x * s ^ 2) (2 * x * t) t := by
    convert ((hasDerivAt_id t).pow 2).const_mul x using 1 <;> ring
  have hc := (hΦ θ _ (root_squareTime_mem hx ht)).comp t hg.hasDerivWithinAt
    (fun s hs => root_squareTime_mem hx hs)
  have he : (Φ θ) ∘ (fun s : ℝ => x * s ^ 2) =
      (fun s : ℝ => Φ θ (x * s ^ 2)) := by
    funext s
    exact Function.comp_apply
  rw [he] at hc
  apply hc.congr_deriv
  dsimp only [rootPhysicalSpeed, rootRegularizedField]
  rw [Real.sqrt_mul hx.1, Real.sqrt_sq ht.1, rpow_three_halves_eq_mul_sqrt hx.1]
  ring

/-- The actual regularized endpoint at ζ = σ x^(3/2) is the true
ordinary physical characteristic at radial time x. -/
theorem rootRegularizedFlow_eq_physicalFlow
    {d c₀ : ℝ × ℝ → ℝ} {Θ : (ℝ × ℝ) → ℝ → ℝ → ℝ}
    {Φ : ℝ → ℝ → ℝ} {R T σ x : ℝ}
    (hT : T ≠ 0)
    (hd : ContDiff ℝ ∞ d) (hc₀ : ContDiff ℝ ∞ c₀)
    (hdperiod : ∀ r, Function.Periodic (fun θ => d (r, θ)) T)
    (hc₀period : ∀ r, Function.Periodic (fun θ => c₀ (r, θ)) T)
    (hinit : ∀ p θ, Θ p 0 θ = θ)
    (hflow : ∀ p θ t, t ∈ Icc (0 : ℝ) 1 →
      HasDerivWithinAt (fun r => Θ p r θ)
        (2 * p.1 * t * d (p.1 * t ^ 2, Θ p t θ) +
          2 * p.2 * t ^ 2 * c₀ (p.1 * t ^ 2, Θ p t θ))
        (Icc (0 : ℝ) 1) t)
    (hΦinit : ∀ θ, Φ θ 0 = θ)
    (hΦ : ∀ θ r, r ∈ Icc (0 : ℝ) R →
      HasDerivWithinAt (Φ θ) (rootPhysicalSpeed d c₀ σ (r, Φ θ r))
        (Icc (0 : ℝ) R) r)
    (hx : x ∈ Icc (0 : ℝ) R) (θ : ℝ) :
    Θ (x, σ * x ^ (3 / 2 : ℝ)) 1 θ = Φ θ x := by
  have hm : ContDiff ℝ ∞
      (fun q : ℝ × ℝ => (q.1, ((x, σ * x ^ (3 / 2 : ℝ)), q.2))) :=
    contDiff_fst.prodMk (contDiff_const.prodMk contDiff_snd)
  have hs : ContDiff ℝ ∞
      (fun q : ℝ × ℝ =>
        rootRegularizedField d c₀ (q.1, ((x, σ * x ^ (3 / 2 : ℝ)), q.2))) :=
    (contDiff_rootRegularizedField hd hc₀).comp hm
  obtain ⟨K, hK⟩ := exists_uniform_angle_lipschitz_of_contDiff
    (a := 0) (b := 1) hs hT
    (fun t => rootRegularizedField_periodic hdperiod hc₀period t
      (x, σ * x ^ (3 / 2 : ℝ)))
  have hi : Θ (x, σ * x ^ (3 / 2 : ℝ)) 0 θ = Φ θ (x * (0 : ℝ) ^ 2) := by
    simp only [hinit, pow_two, mul_zero, hΦinit]
  have he := eqOn_scalarFlow_of_same_initial
    (F := fun t η => rootRegularizedField d c₀
      (t, ((x, σ * x ^ (3 / 2 : ℝ)), η)))
    (u := fun t => Θ (x, σ * x ^ (3 / 2 : ℝ)) t θ)
    (v := fun t => Φ θ (x * t ^ 2)) hK
    (fun t ht => hflow (x, σ * x ^ (3 / 2 : ℝ)) θ t ht)
    (fun t ht => rootPhysicalFlow_squareTime_hasDerivWithinAt hΦ hx ht θ) hi
    (show (1 : ℝ) ∈ Icc 0 1 from ⟨zero_le_one, le_rfl⟩)
  simpa only [one_pow, mul_one] using he

end ContinuousFlexibility.Analysis
