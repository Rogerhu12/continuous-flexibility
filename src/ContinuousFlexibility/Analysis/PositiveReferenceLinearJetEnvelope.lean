import ContinuousFlexibility.Analysis.PositiveReferenceAffineDifference
import ContinuousFlexibility.Analysis.BoundaryTaylorBounds
import ContinuousFlexibility.Analysis.LocalMixedProductBounds

/-!
# Linear high-jet bounds at the fixed positive reference collar

The angular mass correction uses the same fixed middle denominator.
Its interval length cancels against the actual lower bound for that
denominator. Only derivatives of the fixed radial cutoffs multiply the
high endpoint data. No high derivative bound is used to choose a width.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set
open ContinuousFlexibility.Statements
open scoped ContDiff BigOperators Interval

private theorem iteratedDeriv_positiveEndpointCutoff_basis
    (a : ℕ) (c δ x : ℝ) :
    iteratedDeriv a (positiveEndpointCutoff c δ) x =
      (δ⁻¹) ^ a * iteratedDeriv a (boundaryTaylorBasis 0) ((x - c) / δ) := by
  have he : positiveEndpointCutoff c δ =
      fun y => boundaryTaylorBasis 0 ((y - c) / δ) := by
    funext y
    simp only [positiveEndpointCutoff, boundaryTaylorBasis, pow_zero,
      Nat.factorial_zero, Nat.cast_one, div_one, mul_one]
  rw [he]
  simp_rw [div_eq_inv_mul]
  rw [iteratedDeriv_comp_sub_const a
    (fun y : ℝ => boundaryTaylorBasis 0 (δ⁻¹ * y)) c,
    iteratedDeriv_comp_const_mul ((contDiff_boundaryTaylorBasis 0).of_le
      (show (a : ℕ∞ω) ≤ ∞ by simp)) δ⁻¹]

theorem exists_positiveReferenceMiddleWeight_jet_bound (N : ℕ) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ {U δ : ℝ}, 1 ≤ U → 0 < δ → δ⁻¹ ≤ U →
      ∀ l r : ℝ, ∀ a, a ≤ N → ∀ x,
      |iteratedDeriv a
        (fun t => 1 - positiveEndpointCutoff l δ t - positiveEndpointCutoff r δ t) x| ≤
        C * U ^ N := by
  classical
  choose K hK hbound using (fun a : ℕ => exists_boundaryTaylorBasis_jet_bound 0 a)
  let B : ℝ := 1 + ∑ a ∈ Finset.range (N + 1), K a
  have hB : 1 ≤ B := by
    have hh := Finset.sum_nonneg (s := Finset.range (N + 1)) (fun a _ => (hK a).le)
    dsimp only [B]
    linarith only [hh]
  have hKB (a : ℕ) (ha : a ≤ N) : K a ≤ B :=
    (Finset.single_le_sum (fun a _ => (hK a).le)
      (Finset.mem_range.mpr (by omega))).trans (le_add_of_nonneg_left zero_le_one)
  refine ⟨1 + 2 * B, by linarith only [hB], ?_⟩
  intro U δ hU hδ hδinv l r a ha x
  have hU0 : 0 ≤ U := zero_le_one.trans hU
  have hpow : 1 ≤ U ^ N := one_le_pow₀ hU
  have hcut (c : ℝ) : |iteratedDeriv a (positiveEndpointCutoff c δ) x| ≤ B * U ^ N := by
    rw [iteratedDeriv_positiveEndpointCutoff_basis, abs_mul,
      abs_of_nonneg (pow_nonneg (inv_nonneg.mpr hδ.le) _)]
    have hi : (δ⁻¹) ^ a ≤ U ^ N :=
      (pow_le_pow_left₀ (inv_nonneg.mpr hδ.le) hδinv a).trans (pow_le_pow_right₀ hU ha)
    exact (mul_le_mul hi ((hbound a 0 (Nat.zero_le 0) _).trans (hKB a ha))
      (abs_nonneg _) (pow_nonneg hU0 N)).trans_eq (mul_comm _ _)
  have hc : |iteratedDeriv a (fun _ : ℝ => (1 : ℝ)) x| ≤ 1 := by
    rw [iteratedDeriv_const]
    split <;> norm_num
  rw [iteratedDeriv_fun_sub
      ((contDiff_const.sub (contDiff_positiveEndpointCutoff l δ)).contDiffAt.of_le (by simp))
      ((contDiff_positiveEndpointCutoff r δ).contDiffAt.of_le (by simp)),
    iteratedDeriv_fun_sub contDiffAt_const
      ((contDiff_positiveEndpointCutoff l δ).contDiffAt.of_le (by simp))]
  calc
    _ ≤ |iteratedDeriv a (fun _ : ℝ => (1 : ℝ)) x| +
        |iteratedDeriv a (positiveEndpointCutoff l δ) x| +
        |iteratedDeriv a (positiveEndpointCutoff r δ) x| :=
      (abs_sub _ _).trans (add_le_add_right (abs_sub _ _) _)
    _ ≤ 1 + B * U ^ N + B * U ^ N := add_le_add (add_le_add hc (hcut l)) (hcut r)
    _ ≤ (1 + 2 * B) * U ^ N := by nlinarith only [hpow]

private theorem iteratedDeriv_positiveReferenceMass_le
    {F : PolarPoint → ℝ} (hF : ContDiff ℝ ∞ F)
    {l r δ B : ℝ} (hδ : 0 < δ) (hgap : 4 * δ ≤ r - l) (hB : 0 ≤ B)
    (b : ℕ) (hjets : ∀ x ∈ Icc l r, ∀ θ, |mixedDerivative 0 b F (x, θ)| ≤ B)
    (θ : ℝ) :
    |iteratedDeriv b
      (fun η => (∫ t in l..r, F (t, η)) / positiveReferenceMiddleMass l r δ) θ| ≤
      2 * B := by
  have hw : 0 < r - l := by linarith
  have hI : 0 < positiveReferenceMiddleMass l r δ :=
    integral_positiveEndpointCutoff_complement_pos hδ (by linarith)
  have hswap : ContDiff ℝ ∞ (fun p : PolarPoint => (p.2, p.1)) :=
    contDiff_snd.prodMk contDiff_fst
  have hcomm : iteratedDeriv b (fun η => ∫ t in l..r, F (t, η)) θ =
      ∫ t in l..r, iteratedDeriv b (fun η => F (t, η)) θ := by
    exact iteratedDeriv_intervalIntegral_parameter (hF.comp hswap) b l r θ
  rw [iteratedDeriv_div_const, hcomm, abs_div, abs_of_pos hI]
  have hi : |∫ t in l..r, iteratedDeriv b (fun η => F (t, η)) θ| ≤ B * (r - l) := by
    have hh := intervalIntegral.norm_integral_le_of_norm_le_const
      (a := l) (b := r) (C := B)
      (f := fun t => iteratedDeriv b (fun η => F (t, η)) θ) (fun x hx => by
        have hx' : x ∈ Ioc l r := by
          simpa only [uIoc_of_le (sub_nonneg.mp hw.le)] using hx
        simpa only [mixedDerivative, iteratedDeriv_zero, Real.norm_eq_abs] using
          hjets x ⟨hx'.1.le, hx'.2⟩ θ)
    simpa only [Real.norm_eq_abs, abs_of_pos hw] using hh
  calc
    _ ≤ (B * (r - l)) / positiveReferenceMiddleMass l r δ :=
      div_le_div_of_nonneg_right hi hI.le
    _ = (B * (r - l)) * (positiveReferenceMiddleMass l r δ)⁻¹ := div_eq_mul_inv _ _
    _ ≤ (B * (r - l)) * (2 / (r - l)) :=
      mul_le_mul_of_nonneg_left (positiveReferenceMiddleMass_inv_le hδ hgap)
        (mul_nonneg hB hw.le)
    _ = 2 * B := by field_simp [hw.ne'] <;> ring

/-- All high data remain linear after the actual fixed mass correction.
The coefficient depends only on the requested derivative order. -/
theorem exists_balancedPositiveReferenceSlope_linear_jet_envelope (N : ℕ) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ {U δ l r B : ℝ}, 1 ≤ U → 0 < δ →
      4 * δ ≤ r - l → δ⁻¹ ≤ U → 0 ≤ B →
      ∀ (F : PolarPoint → ℝ), ContDiff ℝ ∞ F →
      (∀ a b : ℕ, a + b ≤ N → ∀ x ∈ Icc l r, ∀ θ,
        |mixedDerivative a b F (x, θ)| ≤ B) →
      ∀ a b : ℕ, a + b ≤ N → ∀ p : PolarPoint, p.1 ∈ Icc l r →
        |mixedDerivative a b (balancedPositiveReferenceSlope l r δ F) p| ≤
          C * U ^ N * B := by
  obtain ⟨C, hC, hweight⟩ := exists_positiveReferenceMiddleWeight_jet_bound N
  refine ⟨1 + 2 * C, by linarith only [hC], ?_⟩
  intro U δ l r B hU hδ hgap hδinv hB F hF hjets a b hab p hp
  let W : ℝ → ℝ := fun x =>
    1 - positiveEndpointCutoff l δ x - positiveEndpointCutoff r δ x
  let I : ℝ → ℝ := fun θ => (∫ t in l..r, F (t, θ)) / positiveReferenceMiddleMass l r δ
  have hW : ContDiff ℝ ∞ W :=
    (contDiff_const.sub (contDiff_positiveEndpointCutoff l δ)).sub
      (contDiff_positiveEndpointCutoff r δ)
  have hswap : ContDiff ℝ ∞ (fun q : PolarPoint => (q.2, q.1)) :=
    contDiff_snd.prodMk contDiff_fst
  have hI : ContDiff ℝ ∞ I :=
    (contDiff_parametric_intervalIntegral (hF.comp hswap) l r).div_const _
  have hG : ContDiff ℝ ∞ (fun q : PolarPoint => W q.1 * I q.2) :=
    (hW.comp contDiff_fst).mul (hI.comp contDiff_snd)
  have he : balancedPositiveReferenceSlope l r δ F =
      fun q => F q - W q.1 * I q.2 := by
    funext q
    dsimp only [balancedPositiveReferenceSlope, W, I]
    ring
  have hsep : mixedDerivative a b (fun q : PolarPoint => W q.1 * I q.2) p =
      iteratedDeriv a W p.1 * iteratedDeriv b I p.2 := by
    simp only [mixedDerivative, iteratedDeriv_const_mul_field, iteratedDeriv_mul_const_field]
  have hmass : |iteratedDeriv b I p.2| ≤ 2 * B :=
    iteratedDeriv_positiveReferenceMass_le hF hδ hgap hB b
      (hjets 0 b (by omega)) p.2
  have hWbound : |iteratedDeriv a W p.1| ≤ C * U ^ N :=
    hweight hU hδ hδinv l r a (by omega) p.1
  have hpow : 1 ≤ U ^ N := one_le_pow₀ hU
  have hU0 : 0 ≤ U := zero_le_one.trans hU
  rw [he, mixedDerivative_sub_of_contDiffOn isOpen_univ hF.contDiffOn hG.contDiffOn
    a b (mem_univ p), hsep]
  calc
    _ ≤ |mixedDerivative a b F p| + |iteratedDeriv a W p.1 * iteratedDeriv b I p.2| :=
      abs_sub _ _
    _ ≤ B + (C * U ^ N) * (2 * B) := by
      rw [abs_mul]
      exact add_le_add (hjets a b hab p.1 hp p.2)
        (mul_le_mul hWbound hmass (abs_nonneg _)
          (mul_nonneg (zero_le_one.trans hC) (pow_nonneg hU0 N)))
    _ ≤ (1 + 2 * C) * U ^ N * B := by nlinarith only [mul_le_mul_of_nonneg_right hpow hB]

/-- Apply the linear mass estimate to the actual endpoint-slope
deviation, then integrate using the existing physical mass and width. -/
theorem exists_parameterizedPositiveReferenceCoordinate_linear_jet_envelope (N : ℕ) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ {U δ l r B : ℝ}, 1 ≤ U → 0 < δ →
      4 * δ ≤ r - l → δ⁻¹ ≤ U → 0 ≤ B →
      ∀ (A : Bool → PolarPoint → ℝ), (∀ side, ContDiff ℝ ∞ (A side)) →
      (∀ a b : ℕ, a + b ≤ N → ∀ x ∈ Icc l r, ∀ θ,
        |mixedDerivative a b (positiveReferenceSlopeDeviation l r δ A) (x, θ)| ≤ B) →
      ∀ k, k ≤ N → ∀ p : PolarPoint, p.1 ∈ Icc l r →
        ‖iteratedFDeriv ℝ k
          (fun q => parameterizedPositiveReferenceCoordinate l r δ l (r - l) A q - q.1) p‖ ≤
          C * (1 + (r - l)) * U ^ N * B := by
  obtain ⟨C, hC, hbound⟩ := exists_balancedPositiveReferenceSlope_linear_jet_envelope N
  have hCout : 1 ≤ (2 : ℝ) ^ N * C := by
    calc
      1 = 1 * 1 := by ring
      _ ≤ (2 : ℝ) ^ N * C :=
        mul_le_mul (one_le_pow₀ (by norm_num)) hC zero_le_one (by positivity)
  refine ⟨(2 : ℝ) ^ N * C, hCout, ?_⟩
  intro U δ l r B hU hδ hgap hδinv hB A hA hjets k hk p hp
  let F := positiveReferenceSlopeDeviation l r δ A
  have hF : ContDiff ℝ ∞ F := contDiff_positiveReferenceSlopeDeviation hA l r δ
  have hV := contDiff_balancedPositiveReferenceSlope hF l r δ
  have hbound' (a b : ℕ) (hab : a + b ≤ N) (x : ℝ) (hx : x ∈ Icc l r) (θ : ℝ) :
      ‖mixedDerivative a b (balancedPositiveReferenceSlope l r δ F) (x, θ)‖ ≤
        C * U ^ N * B := by
    rw [Real.norm_eq_abs]
    exact hbound hU hδ hgap hδinv hB F hF hjets a b hab (x, θ) hx
  rw [parameterizedPositiveReferenceCoordinate_sub_fst hA hδ (by linarith)]
  calc
    _ ≤ (2 : ℝ) ^ N * (1 + (r - l)) * (C * U ^ N * B) :=
      norm_iteratedFDeriv_radialIntervalPrimitive_le hV (by linarith)
        (mul_nonneg (mul_nonneg (zero_le_one.trans hC)
          (pow_nonneg (zero_le_one.trans hU) N)) hB) N hbound' k hk hp
    _ = _ := by ring

end ContinuousFlexibility.Analysis
