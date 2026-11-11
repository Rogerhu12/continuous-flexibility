import ContinuousFlexibility.Radial.TailEdgeFluxBounds
import Mathlib.Tactic.LinearCombination

/-!
# The explicit classical Dirichlet kernel on one edge

For the left and right Poisson heights, the conserved Wronskian is the
off-diagonal flux coefficient. Their product at the ordered pair of points
therefore gives a symmetric, jointly continuous kernel. Splitting its integral
at the evaluation point proves the actual inhomogeneous differential equation.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open Set MeasureTheory

/-- The Wronskian with the sign that makes the free coupling positive. -/
def tailEdgeClassicalWronskian (u₀ u₁ : ℝ → ℝ) (s : ℝ) : ℝ :=
  u₀ s * deriv u₁ s - deriv u₀ s * u₁ s

theorem hasDerivAt_tailEdgeClassicalWronskian {u₀ u₁ : ℝ → ℝ} {q s : ℝ}
    (h₀ : DifferentiableAt ℝ u₀ s) (h₁ : DifferentiableAt ℝ u₁ s)
    (hD₀ : HasDerivAt (deriv u₀) (-(q * u₀ s)) s)
    (hD₁ : HasDerivAt (deriv u₁) (-(q * u₁ s)) s) :
    HasDerivAt (tailEdgeClassicalWronskian u₀ u₁) 0 s := by
  have h := (h₀.hasDerivAt.mul hD₁).sub (hD₀.mul h₁.hasDerivAt)
  exact h.congr_deriv (by ring)

/-- The Wronskian is constant up to both regular endpoints. The second
derivatives need only exist on this closed edge. -/
theorem tailEdgeClassicalWronskian_eq_left {a b : ℝ} {q u₀ u₁ : ℝ → ℝ}
    (h₀ : Differentiable ℝ u₀) (h₁ : Differentiable ℝ u₁)
    (hode : ∀ s ∈ Icc a b,
      HasDerivAt (deriv u₀) (-(q s * u₀ s)) s ∧
        HasDerivAt (deriv u₁) (-(q s * u₁ s)) s)
    {s : ℝ} (hs : s ∈ Icc a b) :
    tailEdgeClassicalWronskian u₀ u₁ s = tailEdgeClassicalWronskian u₀ u₁ a := by
  have hW (x : ℝ) (hx : x ∈ Icc a b) :
      HasDerivAt (tailEdgeClassicalWronskian u₀ u₁) 0 x :=
    hasDerivAt_tailEdgeClassicalWronskian (h₀ x) (h₁ x) (hode x hx).1 (hode x hx).2
  rcases eq_or_lt_of_le hs.1 with heq | has
  · rw [heq]
  · have hcont : ContinuousOn (tailEdgeClassicalWronskian u₀ u₁) (Icc a s) :=
      fun x hx => (hW x ⟨hx.1, hx.2.trans hs.2⟩).continuousAt.continuousWithinAt
    have hdiff : DifferentiableOn ℝ (tailEdgeClassicalWronskian u₀ u₁) (Ioo a s) :=
      fun x hx => (hW x ⟨hx.1.le, hx.2.le.trans hs.2⟩).differentiableAt.differentiableWithinAt
    obtain ⟨x, hx, h⟩ :=
      exists_deriv_eq_slope (tailEdgeClassicalWronskian u₀ u₁) has hcont hdiff
    rw [(hW x ⟨hx.1.le, hx.2.le.trans hs.2⟩).deriv] at h
    have he := (eq_div_iff (sub_pos.mpr has).ne').mp h
    linarith only [he]

theorem tailEdgeClassicalWronskian_eq_c {a b c : ℝ} {q u₀ u₁ : ℝ → ℝ}
    (h₀ : Differentiable ℝ u₀) (h₁ : Differentiable ℝ u₁)
    (hode : ∀ s ∈ Icc a b,
      HasDerivAt (deriv u₀) (-(q s * u₀ s)) s ∧
        HasDerivAt (deriv u₁) (-(q s * u₁ s)) s)
    (ha₀ : u₀ a = 1) (ha₁ : u₁ a = 0) (hca : deriv u₁ a = c)
    {s : ℝ} (hs : s ∈ Icc a b) : tailEdgeClassicalWronskian u₀ u₁ s = c := by
  rw [tailEdgeClassicalWronskian_eq_left h₀ h₁ hode hs]
  simp only [tailEdgeClassicalWronskian, ha₀, ha₁, hca, one_mul, mul_zero, sub_zero]

/-- The explicit kernel uses the right height at the smaller point and the
left height at the larger point. -/
def tailEdgeClassicalKernel (c : ℝ) (u₀ u₁ : ℝ → ℝ) (s t : ℝ) : ℝ :=
  u₁ (min s t) * u₀ (max s t) / c

theorem tailEdgeClassicalKernel_comm (c : ℝ) (u₀ u₁ : ℝ → ℝ) (s t : ℝ) :
    tailEdgeClassicalKernel c u₀ u₁ s t = tailEdgeClassicalKernel c u₀ u₁ t s := by
  unfold tailEdgeClassicalKernel
  rw [min_comm s t, max_comm s t]

theorem continuous_tailEdgeClassicalKernel {u₀ u₁ : ℝ → ℝ}
    (h₀ : Continuous u₀) (h₁ : Continuous u₁) (c : ℝ) :
    Continuous (fun z : ℝ × ℝ => tailEdgeClassicalKernel c u₀ u₁ z.1 z.2) :=
  ((h₁.comp (continuous_fst.min continuous_snd)).mul
    (h₀.comp (continuous_fst.max continuous_snd))).div_const c

theorem measurable_tailEdgeClassicalKernel {u₀ u₁ : ℝ → ℝ}
    (h₀ : Continuous u₀) (h₁ : Continuous u₁) (c : ℝ) :
    Measurable (fun z : ℝ × ℝ => tailEdgeClassicalKernel c u₀ u₁ z.1 z.2) :=
  (continuous_tailEdgeClassicalKernel h₀ h₁ c).measurable

theorem tailEdgeClassicalKernel_endpoints {a b c : ℝ} {u₀ u₁ : ℝ → ℝ}
    (ha : u₁ a = 0) (hb : u₀ b = 0) {t : ℝ} (ht : t ∈ Icc a b) :
    tailEdgeClassicalKernel c u₀ u₁ a t = 0 ∧
      tailEdgeClassicalKernel c u₀ u₁ b t = 0 := by
  simp only [tailEdgeClassicalKernel, min_eq_left ht.1, max_eq_right ht.1,
    min_eq_right ht.2, max_eq_left ht.2, ha, hb, zero_mul, mul_zero, zero_div,
    and_self]

/-- The split-integral expression for the classical zero-boundary solution. -/
def tailEdgeClassicalSolve (a b c : ℝ) (u₀ u₁ f : ℝ → ℝ) (s : ℝ) : ℝ :=
  (u₀ s * (∫ t in a..s, u₁ t * f t) +
    u₁ s * (∫ t in s..b, u₀ t * f t)) / c

private theorem tailClassical_hasDerivAt_leftIntegral {g : ℝ → ℝ}
    (hg : Continuous g) (a s : ℝ) :
    HasDerivAt (fun x => ∫ t in a..x, g t) (g s) s :=
  intervalIntegral.integral_hasDerivAt_right (hg.intervalIntegrable a s)
    hg.aestronglyMeasurable.stronglyMeasurableAtFilter hg.continuousAt

private theorem tailClassical_hasDerivAt_rightIntegral {g : ℝ → ℝ}
    (hg : Continuous g) (b s : ℝ) :
    HasDerivAt (fun x => ∫ t in x..b, g t) (-g s) s :=
  intervalIntegral.integral_hasDerivAt_left (hg.intervalIntegrable s b)
    hg.aestronglyMeasurable.stronglyMeasurableAtFilter hg.continuousAt

/-- The two terms from differentiating the moving integration point cancel. -/
theorem hasDerivAt_tailEdgeClassicalSolve {u₀ u₁ f : ℝ → ℝ}
    (h₀ : Differentiable ℝ u₀) (h₁ : Differentiable ℝ u₁) (hf : Continuous f)
    (a b c s : ℝ) :
    HasDerivAt (tailEdgeClassicalSolve a b c u₀ u₁ f)
      ((deriv u₀ s * (∫ t in a..s, u₁ t * f t) +
        deriv u₁ s * (∫ t in s..b, u₀ t * f t)) / c) s := by
  have hL := (h₀ s).hasDerivAt.mul
    (tailClassical_hasDerivAt_leftIntegral (h₁.continuous.mul hf) a s)
  have hR := (h₁ s).hasDerivAt.mul
    (tailClassical_hasDerivAt_rightIntegral (h₀.continuous.mul hf) b s)
  convert (hL.add hR).div_const c using 1
  · funext x
    rfl
  · simp only [Pi.mul_apply]
    ring

/-- The Wronskian gives exactly the coefficient of the source term. -/
theorem hasDerivAt_deriv_tailEdgeClassicalSolve {a b c q s : ℝ}
    {u₀ u₁ f : ℝ → ℝ}
    (h₀ : Differentiable ℝ u₀) (h₁ : Differentiable ℝ u₁) (hf : Continuous f)
    (hc : c ≠ 0)
    (hD₀ : HasDerivAt (deriv u₀) (-(q * u₀ s)) s)
    (hD₁ : HasDerivAt (deriv u₁) (-(q * u₁ s)) s)
    (hW : tailEdgeClassicalWronskian u₀ u₁ s = c) :
    HasDerivAt (deriv (tailEdgeClassicalSolve a b c u₀ u₁ f))
      (-(q * tailEdgeClassicalSolve a b c u₀ u₁ f s) - f s) s := by
  rw [show deriv (tailEdgeClassicalSolve a b c u₀ u₁ f) = _ from
    funext fun x => (hasDerivAt_tailEdgeClassicalSolve h₀ h₁ hf a b c x).deriv]
  have hL := hD₀.mul
    (tailClassical_hasDerivAt_leftIntegral (h₁.continuous.mul hf) a s)
  have hR := hD₁.mul
    (tailClassical_hasDerivAt_rightIntegral (h₀.continuous.mul hf) b s)
  apply ((hL.add hR).div_const c).congr_deriv
  dsimp only [tailEdgeClassicalSolve, tailEdgeClassicalWronskian] at hW ⊢
  simp only [Pi.mul_apply]
  field_simp [hc]
  linear_combination -(f s) * hW

theorem tailEdgeClassicalSolve_equation {a b c q s : ℝ} {u₀ u₁ f : ℝ → ℝ}
    (h₀ : Differentiable ℝ u₀) (h₁ : Differentiable ℝ u₁) (hf : Continuous f)
    (hc : c ≠ 0)
    (hD₀ : HasDerivAt (deriv u₀) (-(q * u₀ s)) s)
    (hD₁ : HasDerivAt (deriv u₁) (-(q * u₁ s)) s)
    (hW : tailEdgeClassicalWronskian u₀ u₁ s = c) :
    -deriv (deriv (tailEdgeClassicalSolve a b c u₀ u₁ f)) s -
      q * tailEdgeClassicalSolve a b c u₀ u₁ f s = f s := by
  rw [(hasDerivAt_deriv_tailEdgeClassicalSolve h₀ h₁ hf hc hD₀ hD₁ hW).deriv]
  ring

theorem tailEdgeClassicalSolve_endpoints {a b c : ℝ} {u₀ u₁ : ℝ → ℝ}
    (ha : u₁ a = 0) (hb : u₀ b = 0) (f : ℝ → ℝ) :
    tailEdgeClassicalSolve a b c u₀ u₁ f a = 0 ∧
      tailEdgeClassicalSolve a b c u₀ u₁ f b = 0 := by
  simp [tailEdgeClassicalSolve, ha, hb]

/-- The classical solution is the integral against the same jointly
continuous symmetric kernel, rather than a separate choice of Green columns. -/
theorem tailEdgeClassicalSolve_eq_integral {a b c s : ℝ} {u₀ u₁ f : ℝ → ℝ}
    (h₀ : Continuous u₀) (h₁ : Continuous u₁) (hf : Continuous f)
    (hs : s ∈ Icc a b) :
    tailEdgeClassicalSolve a b c u₀ u₁ f s =
      ∫ t in a..b, tailEdgeClassicalKernel c u₀ u₁ s t * f t := by
  have hcont : Continuous (fun t => tailEdgeClassicalKernel c u₀ u₁ s t * f t) :=
    (((h₁.comp (continuous_const.min continuous_id)).mul
      (h₀.comp (continuous_const.max continuous_id))).div_const c).mul hf
  have hL : (∫ t in a..s, tailEdgeClassicalKernel c u₀ u₁ s t * f t) =
      (u₀ s / c) * (∫ t in a..s, u₁ t * f t) := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    rw [uIcc_of_le hs.1]
    intro t ht
    simp only [tailEdgeClassicalKernel, min_eq_right ht.2, max_eq_left ht.2]
    ring
  have hR : (∫ t in s..b, tailEdgeClassicalKernel c u₀ u₁ s t * f t) =
      (u₁ s / c) * (∫ t in s..b, u₀ t * f t) := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    rw [uIcc_of_le hs.2]
    intro t ht
    simp only [tailEdgeClassicalKernel, min_eq_left ht.1, max_eq_right ht.1]
    ring
  rw [← intervalIntegral.integral_add_adjacent_intervals (hcont.intervalIntegrable a s)
    (hcont.intervalIntegrable s b), hL, hR, tailEdgeClassicalSolve]
  ring

/-- Poisson comparison and the free lower bound for the coupling give a
uniform Green majorant. The exponent two comes from the two height factors. -/
theorem tailEdgeClassicalKernel_bounds {a b c δ : ℝ} {u₀ u₁ : ℝ → ℝ}
    (hab : a < b) (hδ : δ < 1) (hc : 1 / (b - a) ≤ c)
    (h₀ : ∀ s ∈ Icc a b, tailEdgeLeftHeight a b s ≤ u₀ s ∧
      u₀ s ≤ tailEdgeLeftHeight a b s / (1 - δ))
    (h₁ : ∀ s ∈ Icc a b, tailEdgeRightHeight a b s ≤ u₁ s ∧
      u₁ s ≤ tailEdgeRightHeight a b s / (1 - δ))
    {s t : ℝ} (hs : s ∈ Icc a b) (ht : t ∈ Icc a b) :
    0 ≤ tailEdgeClassicalKernel c u₀ u₁ s t ∧
      tailEdgeClassicalKernel c u₀ u₁ s t ≤ tailEdgeGreen a b s t / (1 - δ) ^ 2 := by
  have hL : 0 < b - a := sub_pos.mpr hab
  have hd : 0 < 1 - δ := sub_pos.mpr hδ
  have hcpos : 0 < c := (one_div_pos.mpr hL).trans_le hc
  have hmin : min s t ∈ Icc a b :=
    ⟨le_min hs.1 ht.1, (min_le_left s t).trans hs.2⟩
  have hmax : max s t ∈ Icc a b :=
    ⟨hs.1.trans (le_max_left s t), max_le hs.2 ht.2⟩
  have hleft := tailEdgeLeftHeight_nonneg hab hmax
  have hright := tailEdgeRightHeight_nonneg hab hmin
  have hu₀ := hleft.trans (h₀ _ hmax).1
  have hu₁ := hright.trans (h₁ _ hmin).1
  refine ⟨div_nonneg (mul_nonneg hu₁ hu₀) hcpos.le, ?_⟩
  apply (div_le_iff₀ hcpos).mpr
  calc
    u₁ (min s t) * u₀ (max s t) ≤
        (tailEdgeRightHeight a b (min s t) / (1 - δ)) *
          (tailEdgeLeftHeight a b (max s t) / (1 - δ)) :=
      mul_le_mul (h₁ _ hmin).2 (h₀ _ hmax).2 hu₀ (div_nonneg hright hd.le)
    _ = (tailEdgeGreen a b s t / (1 - δ) ^ 2) * (1 / (b - a)) := by
      unfold tailEdgeRightHeight tailEdgeLeftHeight tailEdgeGreen
      field_simp [hL.ne', hd.ne'] <;> ring
    _ ≤ (tailEdgeGreen a b s t / (1 - δ) ^ 2) * c :=
      mul_le_mul_of_nonneg_left hc
        (div_nonneg (tailEdgeGreen_nonneg hab hs ht) (sq_nonneg _))

/-- The actual Poisson construction supplies a single symmetric continuous
kernel for every continuous source on the edge. -/
theorem exists_tailEdgeClassicalKernel {a b : ℝ} (hab : a < b)
    {q : TailEdgeContinuous a b} (hq : ∀ s, 0 ≤ q s)
    (hδ : tailEdgeDiagonalSize hab q < 1) :
    ∃ κ : ℝ → ℝ → ℝ,
      Continuous (fun z : ℝ × ℝ => κ z.1 z.2) ∧
      (∀ s t, κ s t = κ t s) ∧
      (∀ s ∈ Icc a b, ∀ t ∈ Icc a b,
        0 ≤ κ s t ∧ κ s t ≤ tailEdgeGreen a b s t / (1 - tailEdgeDiagonalSize hab q) ^ 2) ∧
      (∀ f : ℝ → ℝ, Continuous f → ∃ u : ℝ → ℝ,
        Differentiable ℝ u ∧ u a = 0 ∧ u b = 0 ∧
        (∀ s (hs : s ∈ Icc a b),
          HasDerivAt (deriv u) (-(q ⟨s, hs⟩ * u s) - f s) s) ∧
        (∀ s ∈ Icc a b, u s = ∫ t in a..b, κ s t * f t)) := by
  obtain ⟨u₀, u₁, h₀, h₁, ha₀, hb₀, ha₁, hb₁, hode, hbound, hflux⟩ :=
    exists_tailEdgeFluxMatrix hab hq hδ
  let c : ℝ := 1 / (b - a) +
    (∫ s in a..b, tailEdgeLeftHeight a b s * IccExtend hab.le q s * u₁ s)
  have hc : 1 / (b - a) ≤ c := by
    change 1 / (b - a) ≤ 1 / (b - a) +
      (∫ s in a..b, tailEdgeLeftHeight a b s * IccExtend hab.le q s * u₁ s)
    simpa only [one_div] using
      (tailEdge_flux_coupling_bounds hab hq hδ h₁.continuous (fun s hs => (hbound s hs).2)).1
  have hcpos : 0 < c := (one_div_pos.mpr (sub_pos.mpr hab)).trans_le hc
  have hca : deriv u₁ a = c := by
    have h := (hflux 0 1).1
    simp only [zero_mul, one_mul, zero_add, mul_zero, mul_one, zero_sub] at h
    change -deriv u₁ a = -c at h
    exact neg_injective h
  have hode' (s : ℝ) (hs : s ∈ Icc a b) :
      HasDerivAt (deriv u₀) (-(IccExtend hab.le q s * u₀ s)) s ∧
        HasDerivAt (deriv u₁) (-(IccExtend hab.le q s * u₁ s)) s := by
    rw [IccExtend_of_mem hab.le q hs]
    exact hode s hs
  have hW (s : ℝ) (hs : s ∈ Icc a b) : tailEdgeClassicalWronskian u₀ u₁ s = c :=
    tailEdgeClassicalWronskian_eq_c h₀ h₁ hode' ha₀ ha₁ hca hs
  refine ⟨tailEdgeClassicalKernel c u₀ u₁,
    continuous_tailEdgeClassicalKernel h₀.continuous h₁.continuous c,
    tailEdgeClassicalKernel_comm c u₀ u₁, ?_, ?_⟩
  · intro s hs t ht
    exact tailEdgeClassicalKernel_bounds hab hδ hc
      (fun x hx => (hbound x hx).1) (fun x hx => (hbound x hx).2) hs ht
  · intro f hf
    obtain ⟨hea, heb⟩ := tailEdgeClassicalSolve_endpoints (c := c) ha₁ hb₀ f
    refine ⟨tailEdgeClassicalSolve a b c u₀ u₁ f,
      fun s => (hasDerivAt_tailEdgeClassicalSolve h₀ h₁ hf a b c s).differentiableAt,
      hea, heb, ?_, ?_⟩
    · intro s hs
      exact hasDerivAt_deriv_tailEdgeClassicalSolve h₀ h₁ hf hcpos.ne'
        (hode s hs).1 (hode s hs).2 (hW s hs)
    · intro s hs
      exact tailEdgeClassicalSolve_eq_integral h₀.continuous h₁.continuous hf hs

end ContinuousFlexibility.Radial
