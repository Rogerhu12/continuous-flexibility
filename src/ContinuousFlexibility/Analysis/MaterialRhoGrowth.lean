import ContinuousFlexibility.Analysis.MaterialEndpointComparison
import Mathlib.Analysis.Calculus.MeanValue

/-!
# Growth of the supplied material coordinate

Near either endpoint the actual coordinate has the same derivative as
the explicit cubic primitive, with the appropriate orientation. Their
difference is constant. This gives a polynomial bound in the endpoint
coordinate, which controls the material volume of a full radial plateau.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open Set
open ContinuousFlexibility.Analysis
  (endpointX endpointEll endpointRho endpointRhoOfDistance hasDerivAt_endpointRhoOfDistance)

set_option backward.isDefEq.respectTransparency false

local instance : NormedSpace ℝ ℝ := NormedField.toNormedSpace

theorem materialRho_endpoint_formulas {D : ReferenceData} {T : MaterialData}
    (hT : IsMaterialData D T) :
    ∃ d₀ δ cL cR : ℝ, 0 < d₀ ∧ 0 < δ ∧ δ < min d₀ ((D.b - D.a) / 2) ∧
      (∀ r ∈ Ioo D.a (D.a + δ), T.rho r = endpointRhoOfDistance d₀ (r - D.a) + cL) ∧
      (∀ r ∈ Ioo (D.b - δ) D.b, T.rho r = -endpointRhoOfDistance d₀ (D.b - r) + cR) := by
  obtain ⟨_, _, hρ, _, _, _, _, _, _, _, hend, _⟩ := hT
  obtain ⟨d₀, δ, hd₀, hδ, hδbound, hleft, hright⟩ := hend
  have hδd₀ : δ < d₀ := hδbound.trans_le (min_le_left _ _)
  have hδhalf : δ < (D.b - D.a) / 2 := hδbound.trans_le (min_le_right _ _)
  have hleftCore {r : ℝ} (hr : r ∈ Ioo D.a (D.a + δ)) : r ∈ Ioo D.a D.b :=
    ⟨hr.1, by linarith [hr.2]⟩
  have hrightCore {r : ℝ} (hr : r ∈ Ioo (D.b - δ) D.b) : r ∈ Ioo D.a D.b :=
    ⟨by linarith [hr.1], hr.2⟩
  have hleftD (r : ℝ) (hr : r ∈ Ioo D.a (D.a + δ)) :
      HasDerivAt (fun t => endpointRhoOfDistance d₀ (t - D.a)) (1 / T.ell r) r := by
    have h := (hasDerivAt_endpointRhoOfDistance hd₀ (sub_pos.mpr hr.1)
      (by linarith [hr.2] : r - D.a < d₀)).comp r ((hasDerivAt_id r).sub_const D.a)
    have h' : HasDerivAt (fun t => endpointRhoOfDistance d₀ (t - D.a))
        ((1 / endpointEll d₀ (r - D.a)) * 1) r := by
      simpa only [Function.comp_def, id_eq] using h
    exact h'.congr_deriv (by simp only [mul_one, (hleft r hr).1, endpointEll])
  have hrightD (r : ℝ) (hr : r ∈ Ioo (D.b - δ) D.b) :
      HasDerivAt (fun t => -endpointRhoOfDistance d₀ (D.b - t)) (1 / T.ell r) r := by
    have h := ((hasDerivAt_endpointRhoOfDistance hd₀ (sub_pos.mpr hr.2)
      (by linarith [hr.1] : D.b - r < d₀)).comp r
        ((hasDerivAt_const r D.b).sub (hasDerivAt_id r))).neg
    have h' : HasDerivAt (fun t => -endpointRhoOfDistance d₀ (D.b - t))
        (-((1 / endpointEll d₀ (D.b - r)) * (0 - 1))) r := by
      simpa only [Function.comp_def, Pi.neg_apply] using h
    exact h'.congr_deriv (by simp only [zero_sub, mul_neg_one, neg_neg, (hright r hr).1, endpointEll])
  obtain ⟨cL, hcL⟩ := isOpen_Ioo.exists_eq_add_of_deriv_eq
    (f := T.rho) (g := fun t => endpointRhoOfDistance d₀ (t - D.a))
    isPreconnected_Ioo
    (fun r hr => (hρ r (hleftCore hr)).differentiableAt.differentiableWithinAt)
    (fun r hr => (hleftD r hr).differentiableAt.differentiableWithinAt)
    (by intro r hr; rw [(hρ r (hleftCore hr)).deriv, (hleftD r hr).deriv])
  obtain ⟨cR, hcR⟩ := isOpen_Ioo.exists_eq_add_of_deriv_eq
    (f := T.rho) (g := fun t => -endpointRhoOfDistance d₀ (D.b - t))
    isPreconnected_Ioo
    (fun r hr => (hρ r (hrightCore hr)).differentiableAt.differentiableWithinAt)
    (fun r hr => (hrightD r hr).differentiableAt.differentiableWithinAt)
    (by intro r hr; rw [(hρ r (hrightCore hr)).deriv, (hrightD r hr).deriv])
  exact ⟨d₀, δ, cL, cR, hd₀, hδ, hδbound, fun r hr => hcL hr, fun r hr => hcR hr⟩

theorem materialRho_endpoint_polynomial_bound {D : ReferenceData} {T : MaterialData}
    (hT : IsMaterialData D T) :
    ∃ d₀ K : ℝ, 0 < d₀ ∧ 0 < K ∧ ∀ r ∈ Ioo D.a D.b,
      |T.rho r| ≤ K + endpointX d₀ (endpointDistance D r) ^ 2 +
        (2 / 3 : ℝ) * endpointX d₀ (endpointDistance D r) ^ 3 := by
  obtain ⟨d₀, δ, cL, cR, hd₀, hδ, hδbound, hleft, hright⟩ :=
    materialRho_endpoint_formulas hT
  have hδhalf : δ < (D.b - D.a) / 2 := hδbound.trans_le (min_le_right _ _)
  have hcore : Icc (D.a + δ) (D.b - δ) ⊆ Ioo D.a D.b := by
    intro r hr
    constructor <;> linarith [hr.1, hr.2]
  obtain ⟨A, hA⟩ := isCompact_Icc.exists_bound_of_continuousOn
    ((hT.1 T.rho (by simp)).continuousOn.mono hcore)
  let K : ℝ := |cL| + |cR| + max A 0 + 1
  have hK : 0 < K := by dsimp only [K]; positivity
  have hLc : |cL| ≤ K := by
    dsimp only [K]
    linarith [abs_nonneg cR, le_max_right A 0]
  have hRc : |cR| ≤ K := by
    dsimp only [K]
    linarith [abs_nonneg cL, le_max_right A 0]
  have hAc : A ≤ K := by
    dsimp only [K]
    have h := le_max_left A 0
    linarith [abs_nonneg cL, abs_nonneg cR]
  have habs (x : ℝ) (hx : 0 ≤ x) : |endpointRho x| = x ^ 2 + (2 / 3 : ℝ) * x ^ 3 := by
    unfold endpointRho
    rw [abs_of_nonpos (by
      nlinarith only [sq_nonneg x, pow_nonneg hx 3] :
        -x ^ 2 - (2 / 3 : ℝ) * x ^ 3 ≤ 0)]
    ring
  refine ⟨d₀, K, hd₀, hK, fun r hr => ?_⟩
  by_cases hl : r < D.a + δ
  · have hd : endpointDistance D r = r - D.a := by
      apply min_eq_left
      linarith only [hl, hδhalf]
    rw [hd, hleft r ⟨hr.1, hl⟩]
    calc
      _ ≤ |endpointRhoOfDistance d₀ (r - D.a)| + |cL| := abs_add_le _ _
      _ = endpointX d₀ (r - D.a) ^ 2 + (2 / 3 : ℝ) * endpointX d₀ (r - D.a) ^ 3 + |cL| := by
        rw [endpointRhoOfDistance,
          habs (endpointX d₀ (r - D.a)) (Real.sqrt_nonneg _)]
      _ ≤ _ := by linarith only [hLc]
  · by_cases hr' : D.b - δ < r
    · have hd : endpointDistance D r = D.b - r := by
        apply min_eq_right
        linarith only [hr', hδhalf]
      rw [hd, hright r ⟨hr', hr.2⟩]
      calc
        _ ≤ |-endpointRhoOfDistance d₀ (D.b - r)| + |cR| := abs_add_le _ _
        _ = endpointX d₀ (D.b - r) ^ 2 + (2 / 3 : ℝ) * endpointX d₀ (D.b - r) ^ 3 + |cR| := by
          rw [abs_neg, endpointRhoOfDistance,
            habs (endpointX d₀ (D.b - r)) (Real.sqrt_nonneg _)]
        _ ≤ _ := by linarith only [hRc]
    · have hb : |T.rho r| ≤ A := by
        simpa only [Real.norm_eq_abs] using hA r ⟨le_of_not_gt hl, le_of_not_gt hr'⟩
      have hx : 0 ≤ endpointX d₀ (endpointDistance D r) := Real.sqrt_nonneg _
      have hc : 0 ≤ (2 / 3 : ℝ) * endpointX d₀ (endpointDistance D r) ^ 3 := by positivity
      linarith [sq_nonneg (endpointX d₀ (endpointDistance D r))]

end ContinuousFlexibility.Statements
