import ContinuousFlexibility.Analysis.RootPowerJets
import ContinuousFlexibility.Analysis.CoordinateCompositionMaterialBounds

/-!
# Polynomial material cost of an actual positive power

The exact scalar power derivatives use only the displayed value and its
reciprocal. No compact value rectangle or chosen smooth extension enters
the estimate. The common low order and loss precede the exponent, all
numerical majorants, the state, and the material envelope.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open ContinuousFlexibility.Statements
open scoped ContDiff

theorem positive_rpow_le_of_value_inverse_bounds
    {x M : ℝ} (hx : 0 < x) (hvalue : x ≤ M) (hinverse : x⁻¹ ≤ M) (a : ℝ) :
    x ^ a ≤ M ^ |a| := by
  by_cases ha : 0 ≤ a
  · rw [abs_of_nonneg ha]
    exact Real.rpow_le_rpow hx.le hvalue ha
  · have ha' : a < 0 := lt_of_not_ge ha
    calc
      x ^ a = (x⁻¹) ^ (-a) := by rw [← Real.rpow_neg_eq_inv_rpow, neg_neg]
      _ ≤ M ^ (-a) :=
        Real.rpow_le_rpow (inv_nonneg.mpr hx.le) hinverse (neg_nonneg.mpr ha'.le)
      _ = M ^ |a| := by rw [abs_of_neg ha']

/-- The actual scalar outer jets have explicit polynomial cost at any
positive value whose value and reciprocal have the same material bound. -/
theorem positivePower_outerJets_le_material (a K : ℝ) (hK : 1 ≤ K) :
    ∃ D : ℕ → ℝ, (∀ k, 0 < D k) ∧
      ∀ W : ℝ, 1 ≤ W → ∀ x : ℝ, 0 < x →
        x ≤ K * W ^ K → x⁻¹ ≤ K * W ^ K →
        ∀ k, ‖iteratedFDeriv ℝ k (fun y : ℝ => y ^ a) x‖ ≤ D k * W ^ (D k) := by
  have hpacked (k : ℕ) : ∃ C : ℝ, 0 < C ∧ ∀ W : ℝ, 1 ≤ W →
      (‖rpowJetCoefficient a k‖ * K ^ |a - (k : ℝ)|) *
        W ^ (K * |a - (k : ℝ)|) ≤ C * W ^ C :=
    coefficientEnvelope_pack _ _
  choose D hD hpack using hpacked
  refine ⟨D, hD, ?_⟩
  intro W hW x hx hvalue hinverse k
  have hW0 : 0 ≤ W := zero_le_one.trans hW
  have hK0 : 0 ≤ K := zero_le_one.trans hK
  rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv, iteratedDeriv_rpow_eq,
    norm_mul, Real.norm_of_nonneg (Real.rpow_nonneg hx.le _)]
  calc
    ‖rpowJetCoefficient a k‖ * x ^ (a - (k : ℝ)) ≤
        ‖rpowJetCoefficient a k‖ * (K * W ^ K) ^ |a - (k : ℝ)| :=
      mul_le_mul_of_nonneg_left
        (positive_rpow_le_of_value_inverse_bounds hx hvalue hinverse _) (norm_nonneg _)
    _ = (‖rpowJetCoefficient a k‖ * K ^ |a - (k : ℝ)|) *
        W ^ (K * |a - (k : ℝ)|) := by
      rw [Real.mul_rpow hK0 (Real.rpow_nonneg hW0 _), ← Real.rpow_mul hW0]
      ring
    _ ≤ D k * W ^ (D k) := hpack k W hW

private theorem positivePower_material_monomial_mono
    {a b W H : ℝ} (hab : a ≤ b) (hb : 0 ≤ b) (hW : 1 ≤ W) (hH : 0 ≤ H) :
    a * W ^ a * H ≤ b * W ^ b * H :=
  mul_le_mul_of_nonneg_right
    (mul_le_mul hab (Real.rpow_le_rpow_of_exponent_le hW hab)
      (Real.rpow_nonneg (zero_le_one.trans hW) _) hb) hH

/-- One common state loss controls every ordinary jet of the actual
power. The only extra zeroth-order data are its positive input value and
reciprocal, both with a displayed material cost. -/
theorem positivePower_polynomial_material_bound
    {E : Type} [AddCommGroup E] [Module ℝ E]
    {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    {p : ℕ → Seminorm ℝ E} (hp : Monotone p) (hI : HasInterpolation p)
    (inputLoss : ℕ) :
    ∃ base loss : ℕ, ∀ a K : ℝ, 1 ≤ K →
      ∀ A : ℕ → ℝ, (∀ k, 1 ≤ A k) →
      ∃ B : ℕ → ℝ, (∀ k, 0 < B k) ∧
      ∀ z : E, p base z ≤ 1 → ∀ W : ℝ, 1 ≤ W →
      ∀ g : X → ℝ, ∀ x : X, ContDiffAt ℝ ∞ g x →
        0 < g x → g x ≤ K * W ^ K → (g x)⁻¹ ≤ K * W ^ K →
        (∀ k, 1 ≤ k → ‖iteratedFDeriv ℝ k g x‖ ≤
          A k * W ^ (A k) * (1 + p (k + inputLoss) z)) →
        ∀ k, ‖iteratedFDeriv ℝ k (fun y => g y ^ a) x‖ ≤
          B k * W ^ (B k) * (1 + p (k + loss) z) := by
  obtain ⟨base, loss, hcomposition⟩ :=
    coordinateComposition_fixed_loss_material_bound (X := X) (Y := ℝ) (Z := ℝ)
      hp hI inputLoss
  refine ⟨base, loss, ?_⟩
  intro a K hK A hA
  obtain ⟨D, hD, houter⟩ := positivePower_outerJets_le_material a K hK
  let M : ℕ → ℝ := fun k => max 1 (max (A k) (D k))
  have hM (k : ℕ) : 1 ≤ M k := le_max_left _ _
  have hAM (k : ℕ) : A k ≤ M k := (le_max_left _ _).trans (le_max_right _ _)
  have hDM (k : ℕ) : D k ≤ M k := (le_max_right _ _).trans (le_max_right _ _)
  obtain ⟨C, hC, hbound⟩ := hcomposition M hM
  let B : ℕ → ℝ := fun k => if k = 0 then D 0 else C (k - 1)
  refine ⟨B, ?_, ?_⟩
  · intro k
    by_cases hk : k = 0
    · simpa only [B, if_pos hk] using hD 0
    · simpa only [B, if_neg hk] using hC (k - 1)
  intro z hz W hW g x hg hx hvalue hinverse hjet k
  have hW0 : 0 ≤ W := zero_le_one.trans hW
  have ho (j : ℕ) (_hj : 1 ≤ j) :
      ‖iteratedFDeriv ℝ j (fun t : ℝ => t ^ a) (g x)‖ ≤
        M j * W ^ (M j) * (1 + p (j + inputLoss) z) := by
    have hS : 1 ≤ 1 + p (j + inputLoss) z :=
      le_add_of_nonneg_right (apply_nonneg _ _)
    have hnonneg : 0 ≤ D j * W ^ (D j) :=
      mul_nonneg (hD j).le (Real.rpow_nonneg hW0 _)
    exact (houter W hW (g x) hx hvalue hinverse j).trans
      ((le_mul_of_one_le_right hnonneg hS).trans
        (positivePower_material_monomial_mono (hDM j) (zero_le_one.trans (hM j))
          hW (zero_le_one.trans hS)))
  have hi (j : ℕ) (hj : 1 ≤ j) : ‖iteratedFDeriv ℝ j g x‖ ≤
      M j * W ^ (M j) * (1 + p (j + inputLoss) z) :=
    (hjet j hj).trans (positivePower_material_monomial_mono
      (hAM j) (zero_le_one.trans (hM j)) hW
      (add_nonneg zero_le_one (apply_nonneg _ _)))
  by_cases hk : k = 0
  · subst k
    have hv : ‖(g x) ^ a‖ ≤ D 0 * W ^ (D 0) := by
      simpa only [norm_iteratedFDeriv_zero] using houter W hW (g x) hx hvalue hinverse 0
    simp only [B, if_pos rfl, norm_iteratedFDeriv_zero]
    exact hv.trans (le_mul_of_one_le_right
      (mul_nonneg (hD 0).le (Real.rpow_nonneg hW0 _))
      (le_add_of_nonneg_right (apply_nonneg _ _)))
  · have hkpos : 1 ≤ k := by omega
    have hpow : ContDiffAt ℝ ∞ (fun t : ℝ => t ^ a) (g x) :=
      contDiffAt_id.rpow_const_of_ne hx.ne'
    have hb := hbound z hz W hW (fun t : ℝ => t ^ a) g x hpow hg ho hi (k - 1)
    rw [Nat.sub_add_cancel hkpos] at hb
    simpa only [B, if_neg hk, Function.comp_def] using hb

end ContinuousFlexibility.Analysis
