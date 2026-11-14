module

public import ContinuousFlexibility.Statements.Nonlinear
public import Mathlib.Analysis.Calculus.Deriv.Prod
public import Mathlib.Analysis.Calculus.MeanValue

/-!
# Values and zero-order bounds for substitution at a root

The even average preserves the supremum bound. The odd divided difference
is controlled by the first Fréchet derivative on the source rectangle; at
zero its prescribed value has the same bound. All norms here are the actual
product norms of the statement layer. In particular the middle coordinate
direction `(0, 1, 0)` has norm one, and the distance between the two sampled
points is exactly twice the nonnegative root power.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Statements

open Set
open scoped ContDiff

section Bounds

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {s : ℕ} {K : Set E} {f : E → ℝ} {M : ℝ}

/-- The order-zero part of a `CSBound` controls the function itself. -/
theorem CSBound.norm_le (h : CSBound s K f M) {x : E} (hx : x ∈ K) :
    ‖f x‖ ≤ M := by
  simpa only [norm_iteratedFDeriv_zero] using h 0 (Nat.zero_le s) x hx

/-- At order one the multilinear derivative norm is the operator norm
of the actual Fréchet derivative. -/
theorem CSBound.fderiv_norm_le (h : CSBound s K f M) (hs : 1 ≤ s)
    {x : E} (hx : x ∈ K) : ‖fderiv ℝ f x‖ ≤ M := by
  simpa only [norm_iteratedFDeriv_one] using h 1 hs x hx

/-- At zero order `CSBound` is precisely a pointwise norm bound. -/
theorem csBound_zero_iff : CSBound 0 K f M ↔ ∀ x ∈ K, ‖f x‖ ≤ M := by
  constructor
  · exact fun h x hx => h.norm_le hx
  · intro h n hn x hx
    have hn0 : n = 0 := Nat.eq_zero_of_le_zero hn
    subst n
    simpa only [norm_iteratedFDeriv_zero] using h x hx

end Bounds

/-- The root power stays in the unit interval on the unit radial interval. -/
theorem rpow_three_halves_mem_Icc {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) :
    x ^ (3 / 2 : ℝ) ∈ Icc (0 : ℝ) 1 :=
  ⟨Real.rpow_nonneg hx.1 _, Real.rpow_le_one hx.1 hx.2 (by norm_num)⟩

theorem rootEven_zero (G : ℝ × ℝ × ℝ → ℝ) (θ : ℝ) :
    rootEven G (0, θ) = G (0, 0, θ) := by
  have hz : (0 : ℝ) ^ (3 / 2 : ℝ) = 0 := Real.zero_rpow (by norm_num)
  simp only [rootEven, hz, neg_zero]
  ring

theorem rootOdd_zero (G : ℝ × ℝ × ℝ → ℝ) (θ : ℝ) :
    rootOdd G (0, θ) = deriv (fun t => G (0, t, θ)) 0 := by
  simp only [rootOdd, ↓reduceIte]

theorem rootOdd_of_ne_zero (G : ℝ × ℝ × ℝ → ℝ) {p : PolarPoint}
    (hp : p.1 ≠ 0) :
    rootOdd G p =
      (G (p.1, p.1 ^ (3 / 2 : ℝ), p.2) -
        G (p.1, -(p.1 ^ (3 / 2 : ℝ)), p.2)) / (2 * p.1 ^ (3 / 2 : ℝ)) := by
  rw [rootOdd, ite_eq_right hp]

/-- A derivative along the middle coordinate is bounded by the full
Fréchet derivative norm, with constant one in the product norm. -/
theorem norm_deriv_middle_le_fderiv {G : ℝ × ℝ × ℝ → ℝ} {x t θ : ℝ}
    (hG : DifferentiableAt ℝ G (x, t, θ)) :
    ‖deriv (fun u : ℝ => G (x, u, θ)) t‖ ≤ ‖fderiv ℝ G (x, t, θ)‖ := by
  have hcurve : HasDerivAt (fun u : ℝ => (x, u, θ)) (0, 1, 0) t :=
    (hasDerivAt_const t x).prodMk ((hasDerivAt_id' t).prodMk (hasDerivAt_const t θ))
  have hderiv : deriv (fun u : ℝ => G (x, u, θ)) t =
      fderiv ℝ G (x, t, θ) (0, 1, 0) := by
    simpa only [Function.comp_def] using (hG.hasFDerivAt.comp_hasDerivAt t hcurve).deriv
  have hv : ‖((0, 1, 0) : ℝ × ℝ × ℝ)‖ = 1 := by norm_num [Prod.norm_mk]
  rw [hderiv]
  simpa only [hv, mul_one] using
    (fderiv ℝ G (x, t, θ)).le_opNorm ((0, 1, 0) : ℝ × ℝ × ℝ)

/-- The even root substitution has zero-order bound with constant one. -/
theorem csBound_rootEven_zero {G : ℝ × ℝ × ℝ → ℝ} {M : ℝ}
    (hG : CSBound 0
      (Icc (0 : ℝ) 1 ×ˢ Icc (-1 : ℝ) 1 ×ˢ Icc (-Real.pi) Real.pi) G M) :
    CSBound 0 (Icc (0 : ℝ) 1 ×ˢ Icc (-Real.pi) Real.pi) (rootEven G) M := by
  apply csBound_zero_iff.mpr
  intro p hp
  have ha := rpow_three_halves_mem_Icc hp.1
  have hpPlus : (p.1, p.1 ^ (3 / 2 : ℝ), p.2) ∈
      Icc (0 : ℝ) 1 ×ˢ Icc (-1 : ℝ) 1 ×ˢ Icc (-Real.pi) Real.pi :=
    ⟨hp.1, ⟨by linarith only [ha.1], ha.2⟩, hp.2⟩
  have hpMinus : (p.1, -(p.1 ^ (3 / 2 : ℝ)), p.2) ∈
      Icc (0 : ℝ) 1 ×ˢ Icc (-1 : ℝ) 1 ×ˢ Icc (-Real.pi) Real.pi :=
    ⟨hp.1, ⟨by linarith only [ha.2], by linarith only [ha.1]⟩, hp.2⟩
  rw [rootEven, norm_div, Real.norm_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
  apply (div_le_iff₀ (by norm_num : (0 : ℝ) < 2)).mpr
  have hsum := (norm_add_le _ _).trans (add_le_add (hG.norm_le hpPlus) (hG.norm_le hpMinus))
  simpa only [mul_two] using hsum

/-- The odd root substitution has zero-order bound with constant one
and one derivative of its input. -/
theorem csBound_rootOdd_zero {G : ℝ × ℝ × ℝ → ℝ} {M : ℝ}
    (hG : ContDiff ℝ ∞ G)
    (hB : CSBound 1
      (Icc (0 : ℝ) 1 ×ˢ Icc (-1 : ℝ) 1 ×ˢ Icc (-Real.pi) Real.pi) G M) :
    CSBound 0 (Icc (0 : ℝ) 1 ×ˢ Icc (-Real.pi) Real.pi) (rootOdd G) M := by
  apply csBound_zero_iff.mpr
  intro p hp
  by_cases hx : p.1 = 0
  · rw [rootOdd, ite_eq_left hx]
    have hmem : ((0, 0, p.2) : ℝ × ℝ × ℝ) ∈
        Icc (0 : ℝ) 1 ×ˢ Icc (-1 : ℝ) 1 ×ˢ Icc (-Real.pi) Real.pi :=
      ⟨⟨le_rfl, zero_le_one⟩, ⟨by norm_num, by norm_num⟩, hp.2⟩
    exact (norm_deriv_middle_le_fderiv (hG.differentiable (by simp) (0, 0, p.2))).trans
      (hB.fderiv_norm_le le_rfl hmem)
  · have hxpos : 0 < p.1 := lt_of_le_of_ne hp.1.1 (Ne.symm hx)
    have ha := rpow_three_halves_mem_Icc hp.1
    have hapos : 0 < p.1 ^ (3 / 2 : ℝ) := Real.rpow_pos_of_pos hxpos _
    have hden : 0 < 2 * p.1 ^ (3 / 2 : ℝ) := mul_pos (by norm_num) hapos
    have hpPlus : (p.1, p.1 ^ (3 / 2 : ℝ), p.2) ∈
        Icc (0 : ℝ) 1 ×ˢ Icc (-1 : ℝ) 1 ×ˢ Icc (-Real.pi) Real.pi :=
      ⟨hp.1, ⟨by linarith only [ha.1], ha.2⟩, hp.2⟩
    have hpMinus : (p.1, -(p.1 ^ (3 / 2 : ℝ)), p.2) ∈
        Icc (0 : ℝ) 1 ×ˢ Icc (-1 : ℝ) 1 ×ˢ Icc (-Real.pi) Real.pi :=
      ⟨hp.1, ⟨by linarith only [ha.2], by linarith only [ha.1]⟩, hp.2⟩
    have hconv : Convex ℝ
        (Icc (0 : ℝ) 1 ×ˢ Icc (-1 : ℝ) 1 ×ˢ Icc (-Real.pi) Real.pi) :=
      (convex_Icc (0 : ℝ) 1).prod
        ((convex_Icc (-1 : ℝ) 1).prod (convex_Icc (-Real.pi) Real.pi))
    have hdiff := hconv.norm_image_sub_le_of_norm_fderiv_le (𝕜 := ℝ)
      (fun z _ => hG.differentiable (by simp) z)
      (fun z hz => hB.fderiv_norm_le le_rfl hz) hpMinus hpPlus
    have hsub : ((p.1, p.1 ^ (3 / 2 : ℝ), p.2) : ℝ × ℝ × ℝ) -
        (p.1, -(p.1 ^ (3 / 2 : ℝ)), p.2) = (0, 2 * p.1 ^ (3 / 2 : ℝ), 0) := by
      simp only [Prod.mk_sub_mk, sub_self, sub_neg_eq_add, two_mul]
    have hnorm : ‖((p.1, p.1 ^ (3 / 2 : ℝ), p.2) : ℝ × ℝ × ℝ) -
        (p.1, -(p.1 ^ (3 / 2 : ℝ)), p.2)‖ = 2 * p.1 ^ (3 / 2 : ℝ) := by
      rw [hsub]
      simp only [Prod.norm_mk, norm_zero, Real.norm_of_nonneg hden.le,
        max_eq_left hden.le, max_eq_right hden.le]
    rw [hnorm] at hdiff
    rw [rootOdd_of_ne_zero G hx, norm_div, Real.norm_of_nonneg hden.le]
    exact (div_le_iff₀ hden).mpr hdiff

end ContinuousFlexibility.Statements
