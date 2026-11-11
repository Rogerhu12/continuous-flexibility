import ContinuousFlexibility.Radial.Gauge
import Mathlib.Analysis.ODE.Gronwall

/-!
# Transfer of the boundary state across a short positive join

This file formalizes the elementary transfer estimate of paper §5, eqs. (js5)–(js14).

* `norm_sub_le_exp_sub_one_mul_norm`: a two-sided Gronwall estimate for a curve whose
  derivative grows at most linearly in its own norm.
* `joinState`: the state `(u, w ζ / W)` with `ζ = r u' / J - u`; this is the project's
  `radialState` with `J = j ^ 2` and `W = scale`.
* `hasDerivAt_joinState`: the first-order linear system satisfied by `joinState` when
  `radialJacobi J w u = 0`.
* `joinState_transfer` and `joinState_transfer_coord`: the transfer estimate in the max norm
  on `ℝ × ℝ`, and its coordinatewise form.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open Set Real

/-- Forward Gronwall estimate for linear growth. -/
private theorem norm_sub_le_exp_sub_one_mul_norm_forward {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {Y Y' : ℝ → E} {α β K : ℝ} (hK : 0 ≤ K)
    (hY : ∀ t ∈ Icc α β, HasDerivAt Y (Y' t) t)
    (hbound : ∀ t ∈ Icc α β, ‖Y' t‖ ≤ K * ‖Y t‖) :
    ∀ s ∈ Icc α β, ∀ t ∈ Icc α β, s ≤ t →
      ‖Y t - Y s‖ ≤ (Real.exp (K * (t - s)) - 1) * ‖Y s‖ := by
  intro s hs t ht hst
  have hsub : ∀ x ∈ Icc s t, x ∈ Icc α β := fun x hx => ⟨hs.1.trans hx.1, hx.2.trans ht.2⟩
  have hcont : ContinuousOn (fun x => Y x - Y s) (Icc s t) := fun x hx =>
    ((hY x (hsub x hx)).continuousAt.sub continuousAt_const).continuousWithinAt
  have hder : ∀ x ∈ Ico s t, HasDerivWithinAt (fun x => Y x - Y s) (Y' x) (Ici x) x :=
    fun x hx => ((hY x (hsub x (Ico_subset_Icc_self hx))).sub_const (Y s)).hasDerivWithinAt
  have hb : ∀ x ∈ Ico s t, ‖Y' x‖ ≤ K * ‖Y x - Y s‖ + K * ‖Y s‖ := by
    intro x hx
    have h1 := hbound x (hsub x (Ico_subset_Icc_self hx))
    have h2 : ‖Y x‖ ≤ ‖Y x - Y s‖ + ‖Y s‖ := by
      simpa using norm_add_le (Y x - Y s) (Y s)
    have h3 := mul_le_mul_of_nonneg_left h2 hK
    linarith
  have h0 : ‖Y s - Y s‖ ≤ 0 := by simp
  have h := norm_le_gronwallBound_of_norm_deriv_right_le hcont hder h0 hb t ⟨hst, le_rfl⟩
  rcases eq_or_ne K 0 with hK0 | hK0
  · subst hK0
    rw [gronwallBound_K0] at h
    simpa using h
  · rw [gronwallBound_of_K_ne_0 hK0] at h
    have hc : K * ‖Y s‖ / K = ‖Y s‖ := by field_simp
    simp only [hc, zero_mul, zero_add] at h
    linarith

/-- Two-sided Gronwall estimate for linear growth. -/
theorem norm_sub_le_exp_sub_one_mul_norm {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {Y Y' : ℝ → E} {α β K : ℝ} (hK : 0 ≤ K)
    (hY : ∀ t ∈ Icc α β, HasDerivAt Y (Y' t) t)
    (hbound : ∀ t ∈ Icc α β, ‖Y' t‖ ≤ K * ‖Y t‖) :
    ∀ s ∈ Icc α β, ∀ t ∈ Icc α β, ‖Y t - Y s‖ ≤ (Real.exp (K * |t - s|) - 1) * ‖Y s‖ := by
  intro s hs t ht
  rcases le_total s t with hst | hts
  · rw [abs_of_nonneg (sub_nonneg.2 hst)]
    exact norm_sub_le_exp_sub_one_mul_norm_forward hK hY hbound s hs t ht hst
  · rw [abs_of_nonpos (sub_nonpos.2 hts)]
    have hmem : ∀ x, x ∈ Icc (-β) (-α) → -x ∈ Icc α β := fun x hx =>
      ⟨by linarith [hx.2], by linarith [hx.1]⟩
    have hZ : ∀ x ∈ Icc (-β) (-α),
        HasDerivAt (fun x => Y (-x)) (-Y' (-x)) x := by
      intro x hx
      have h := (hY (-x) (hmem x hx)).scomp x (hasDerivAt_neg x)
      simpa [Function.comp_def] using h
    have hZb : ∀ x ∈ Icc (-β) (-α), ‖-Y' (-x)‖ ≤ K * ‖Y (-x)‖ := by
      intro x hx
      rw [norm_neg]
      exact hbound (-x) (hmem x hx)
    have h := norm_sub_le_exp_sub_one_mul_norm_forward (Y := fun x => Y (-x)) hK hZ hZb
      (-s) ⟨by linarith [hs.2], by linarith [hs.1]⟩ (-t) ⟨by linarith [ht.2], by linarith [ht.1]⟩
      (by linarith)
    simp only [neg_neg] at h
    have he : -t - -s = -(t - s) := by ring
    rw [he] at h
    exact h

/-- The boundary state transported across a join: `(u, w ζ / W)` with `ζ = r u' / J - u`. -/
def joinState (J W : ℝ) (w u : ℝ → ℝ) (r : ℝ) : ℝ × ℝ :=
  (u r, w r / W * (r * deriv u r / J - u r))

/-- The first-order linear system satisfied by `joinState` along a solution of
`radialJacobi J w u = 0`. -/
theorem hasDerivAt_joinState {J W r : ℝ} {w u : ℝ → ℝ} (hr : 0 < r) (hJ : J ≠ 0)
    (hW : W ≠ 0) (hwr : w r ≠ 0) (hw : DifferentiableAt ℝ w r)
    (hu : DifferentiableAt ℝ u r) (hu' : DifferentiableAt ℝ (deriv u) r)
    (hode : radialJacobi J w u r = 0) :
    HasDerivAt (joinState J W w u)
      (J / r * u r + J * W / (r * w r) * (joinState J W w u r).2,
       -((J - 1) * w r / (W * r)) * u r - (J - 1) / r * (joinState J W w u r).2) r := by
  have hr0 : r ≠ 0 := hr.ne'
  have hwd := hw.hasDerivAt
  have hud := hu.hasDerivAt
  have hu'd := hu'.hasDerivAt
  have hprod : deriv (fun t => w t * deriv u t) r =
      deriv w r * deriv u r + w r * deriv (deriv u) r := (hwd.mul hu'd).deriv
  unfold radialJacobi at hode
  rw [hprod] at hode
  have hu2 : deriv (deriv u) r =
      (J * deriv w r / r * u r - deriv w r * deriv u r) / w r := by
    have hode' : deriv w r * deriv u r + w r * deriv (deriv u) r =
        J * deriv w r / r * u r := by linarith
    rw [eq_div_iff hwr]
    linear_combination hode'
  have hζ : HasDerivAt (fun t => t * deriv u t / J - u t)
      ((1 * deriv u r + r * deriv (deriv u) r) / J - deriv u r) r :=
    (((hasDerivAt_id' r).mul hu'd).div_const J).sub hud
  have h2 := (hwd.div_const W).mul hζ
  have key := hud.prodMk h2
  convert key using 1
  · funext x; rfl
  refine Prod.ext ?_ ?_
  · simp only [joinState]
    field_simp
    ring
  · simp only [joinState]
    rw [hu2]
    field_simp
    ring

private theorem abs_lin_le {c₁ c₂ y₁ y₂ N A B : ℝ} (h₁ : |c₁| ≤ A) (h₂ : |c₂| ≤ B)
    (hy₁ : |y₁| ≤ N) (hy₂ : |y₂| ≤ N) : |c₁ * y₁ + c₂ * y₂| ≤ (A + B) * N := by
  calc |c₁ * y₁ + c₂ * y₂| ≤ |c₁ * y₁| + |c₂ * y₂| := abs_add_le _ _
    _ = |c₁| * |y₁| + |c₂| * |y₂| := by rw [abs_mul, abs_mul]
    _ ≤ A * N + B * N :=
        add_le_add (mul_le_mul h₁ hy₁ (abs_nonneg _) ((abs_nonneg _).trans h₁))
          (mul_le_mul h₂ hy₂ (abs_nonneg _) ((abs_nonneg _).trans h₂))
    _ = (A + B) * N := by ring

/-- Transfer of the join state across `[r₀, r₁]` in the max norm on `ℝ × ℝ`. -/
theorem joinState_transfer {J W Λ r₀ r₁ : ℝ} {w u : ℝ → ℝ}
    (hr₀ : 0 < r₀) (hJ : 1 ≤ J) (hW : 0 < W) (hΛ : 1 ≤ Λ)
    (hreg : ∀ r ∈ Icc r₀ r₁, DifferentiableAt ℝ w r ∧ DifferentiableAt ℝ u r ∧
      DifferentiableAt ℝ (deriv u) r)
    (hw : ∀ r ∈ Icc r₀ r₁, 0 < w r ∧ w r ≤ Λ * W ∧ W ≤ Λ * w r)
    (hode : ∀ r ∈ Icc r₀ r₁, radialJacobi J w u r = 0) :
    ∀ s ∈ Icc r₀ r₁, ∀ t ∈ Icc r₀ r₁,
      ‖joinState J W w u t - joinState J W w u s‖ ≤
        (Real.exp (2 * J * Λ / r₀ * |t - s|) - 1) * ‖joinState J W w u s‖ := by
  have hJ0 : 0 < J := by linarith
  have hΛ0 : 0 < Λ := by linarith
  have hK : 0 ≤ 2 * J * Λ / r₀ := by positivity
  refine norm_sub_le_exp_sub_one_mul_norm hK
    (Y' := fun r => (J / r * u r + J * W / (r * w r) * (joinState J W w u r).2,
       -((J - 1) * w r / (W * r)) * u r - (J - 1) / r * (joinState J W w u r).2)) ?_ ?_
  · intro r hr
    obtain ⟨h1, h2, h3⟩ := hreg r hr
    exact hasDerivAt_joinState (by linarith [hr.1]) hJ0.ne' hW.ne' (hw r hr).1.ne' h1 h2 h3
      (hode r hr)
  · intro r hr
    obtain ⟨hwpos, hwW, hWw⟩ := hw r hr
    have hrr : r₀ ≤ r := hr.1
    have hrpos : 0 < r := by linarith
    set N := ‖joinState J W w u r‖
    have hy₁ : |(joinState J W w u r).1| ≤ N := by
      rw [← Real.norm_eq_abs]; exact norm_fst_le _
    have hy₂ : |(joinState J W w u r).2| ≤ N := by
      rw [← Real.norm_eq_abs]; exact norm_snd_le _
    have hN : 0 ≤ N := norm_nonneg _
    have hsum : J / r₀ + J * Λ / r₀ ≤ 2 * J * Λ / r₀ := by
      rw [← add_div]
      apply div_le_div_of_nonneg_right _ hr₀.le
      nlinarith
    have hsum' : J * Λ / r₀ + J / r₀ ≤ 2 * J * Λ / r₀ := by linarith
    have ha : |J / r| ≤ J / r₀ := by
      rw [abs_of_nonneg (by positivity)]
      exact div_le_div_of_nonneg_left hJ0.le hr₀ hrr
    have hb : |J * W / (r * w r)| ≤ J * Λ / r₀ := by
      rw [abs_of_nonneg (by positivity), div_le_div_iff₀ (by positivity) hr₀]
      nlinarith [mul_le_mul_of_nonneg_left hWw (le_of_lt (mul_pos hJ0 hr₀)),
        mul_le_mul_of_nonneg_left hrr (le_of_lt (mul_pos (mul_pos hJ0 hΛ0) hwpos))]
    have hc : |-((J - 1) * w r / (W * r))| ≤ J * Λ / r₀ := by
      have hJ1 : 0 ≤ J - 1 := by linarith
      rw [abs_neg, abs_of_nonneg (by positivity), div_le_div_iff₀ (by positivity) hr₀]
      nlinarith [mul_le_mul_of_nonneg_right (show J - 1 ≤ J by linarith)
          (le_of_lt (mul_pos hwpos hr₀)),
        mul_le_mul_of_nonneg_left hwW (le_of_lt (mul_pos hJ0 hr₀)),
        mul_le_mul_of_nonneg_left hrr (le_of_lt (mul_pos (mul_pos hJ0 hΛ0) hW))]
    have hd : |-((J - 1) / r)| ≤ J / r₀ := by
      have hJ1 : 0 ≤ J - 1 := by linarith
      rw [abs_neg, abs_of_nonneg (by positivity), div_le_div_iff₀ hrpos hr₀]
      nlinarith [mul_le_mul_of_nonneg_left hrr hJ0.le]
    rw [norm_prod_le_iff, Real.norm_eq_abs, Real.norm_eq_abs]
    constructor
    · exact (abs_lin_le ha hb hy₁ hy₂).trans (mul_le_mul_of_nonneg_right hsum hN)
    · have he : -((J - 1) * w r / (W * r)) * u r - (J - 1) / r * (joinState J W w u r).2 =
          -((J - 1) * w r / (W * r)) * (joinState J W w u r).1 +
            -((J - 1) / r) * (joinState J W w u r).2 := by
        simp only [joinState]; ring
      rw [he]
      exact (abs_lin_le hc hd hy₁ hy₂).trans (mul_le_mul_of_nonneg_right hsum' hN)

/-- Coordinatewise form of `joinState_transfer`. -/
theorem joinState_transfer_coord {J W Λ r₀ r₁ : ℝ} {w u : ℝ → ℝ}
    (hr₀ : 0 < r₀) (hJ : 1 ≤ J) (hW : 0 < W) (hΛ : 1 ≤ Λ)
    (hreg : ∀ r ∈ Icc r₀ r₁, DifferentiableAt ℝ w r ∧ DifferentiableAt ℝ u r ∧
      DifferentiableAt ℝ (deriv u) r)
    (hw : ∀ r ∈ Icc r₀ r₁, 0 < w r ∧ w r ≤ Λ * W ∧ W ≤ Λ * w r)
    (hode : ∀ r ∈ Icc r₀ r₁, radialJacobi J w u r = 0) :
    ∀ s ∈ Icc r₀ r₁, ∀ t ∈ Icc r₀ r₁,
      |(joinState J W w u t).1 - (joinState J W w u s).1| ≤
          (Real.exp (2 * J * Λ / r₀ * |t - s|) - 1) * ‖joinState J W w u s‖ ∧
        |(joinState J W w u t).2 - (joinState J W w u s).2| ≤
          (Real.exp (2 * J * Λ / r₀ * |t - s|) - 1) * ‖joinState J W w u s‖ := by
  intro s hs t ht
  have h := joinState_transfer hr₀ hJ hW hΛ hreg hw hode s hs t ht
  refine ⟨?_, ?_⟩
  · rw [← Real.norm_eq_abs, ← Prod.fst_sub]
    exact (norm_fst_le _).trans h
  · rw [← Real.norm_eq_abs, ← Prod.snd_sub]
    exact (norm_snd_le _).trans h

end ContinuousFlexibility.Radial
