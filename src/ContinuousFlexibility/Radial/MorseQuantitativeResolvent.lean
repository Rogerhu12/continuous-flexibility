module

public import ContinuousFlexibility.Radial.MorseNoWeylResolvent

/-!
# Quantitative zero inverse from an actual Morse eigenvalue gap

If a symmetric inverse has norm `M`, the square of that inverse minus
`M²` cannot be bounded below. A hypothetical `M` larger than the reciprocal
gap gives positive lower bounds at the two energies `±M⁻¹`. Their product
would bound the square away from `M²`.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Radial

open Real
open scoped RealInnerProductSpace InnerProductSpace

set_option backward.isDefEq.respectTransparency false

private theorem morseInverse_shift_factor_boundedBelow (G : MorseL2 →L[ℝ] MorseL2)
    {e c : ℝ} (he : e ≠ 0) (hc : 0 < c)
    (h : ∀ x : MorseL2, c * ‖G x‖ ≤ ‖x - e⁻¹ • G x‖) :
    ∃ d : ℝ, 0 < d ∧ ∀ x : MorseL2, d * ‖x‖ ≤ ‖G x - e • x‖ := by
  let C := 1 + |e⁻¹| / c
  have hC : 0 < C := by dsimp [C]; positivity
  refine ⟨|e| / C, div_pos (abs_pos.mpr he) hC, ?_⟩
  intro x
  let r := x - e⁻¹ • G x
  have hG : ‖G x‖ ≤ ‖r‖ / c := by
    apply (le_div_iff₀ hc).2
    exact (mul_comm ‖G x‖ c).trans_le (h x)
  have hx : ‖x‖ ≤ C * ‖r‖ := calc
    _ = ‖r + e⁻¹ • G x‖ := by dsimp [r]; rw [sub_add_cancel]
    _ ≤ ‖r‖ + ‖e⁻¹ • G x‖ := norm_add_le _ _
    _ = ‖r‖ + |e⁻¹| * ‖G x‖ := by rw [norm_smul, Real.norm_eq_abs]
    _ ≤ ‖r‖ + |e⁻¹| * (‖r‖ / c) := add_le_add le_rfl (mul_le_mul_of_nonneg_left hG (abs_nonneg _))
    _ = _ := by dsimp [C]; ring
  have hquot : ‖x‖ / C ≤ ‖r‖ := (div_le_iff₀ hC).2 (hx.trans_eq (mul_comm _ _))
  have hr : G x - e • x = (-e) • r := by
    dsimp [r]
    rw [smul_sub, smul_smul, neg_mul, mul_inv_cancel₀ he, neg_one_smul, neg_smul]
    abel
  calc
    _ = |e| * (‖x‖ / C) := by ring
    _ ≤ |e| * ‖r‖ := mul_le_mul_of_nonneg_left hquot (abs_nonneg _)
    _ = _ := by rw [hr, norm_smul, Real.norm_eq_abs, abs_neg]

private theorem morseInverse_square_boundedBelow (G : MorseL2 →L[ℝ] MorseL2) (M : ℝ)
    {d₁ d₂ : ℝ} (h₁ : 0 ≤ d₁)
    (hplus : ∀ x : MorseL2, d₁ * ‖x‖ ≤ ‖G x - M • x‖)
    (hminus : ∀ x : MorseL2, d₂ * ‖x‖ ≤ ‖G x - (-M) • x‖) (x : MorseL2) :
    (d₁ * d₂) * ‖x‖ ≤ ‖G (G x) - M ^ 2 • x‖ := by
  let y := G x + M • x
  have h₂ : d₂ * ‖x‖ ≤ ‖y‖ := by
    simpa only [y, neg_smul, sub_neg_eq_add] using hminus x
  have he : G y - M • y = G (G x) - M ^ 2 • x := by
    dsimp [y]
    rw [map_add, map_smul, smul_add, smul_smul, ← pow_two]
    abel
  rw [← he, mul_assoc]
  exact (mul_le_mul_of_nonneg_left h₂ h₁).trans (hplus y)

private theorem morseSymmetricInverse_square_not_boundedBelow (G : MorseL2 →L[ℝ] MorseL2)
    (hSym : ∀ x y : MorseL2, ⟪G x, y⟫_ℝ = ⟪x, G y⟫_ℝ) (hM : 0 < ‖G‖) :
    ¬ ∃ d : ℝ, 0 < d ∧ ∀ x : MorseL2, d * ‖x‖ ≤ ‖G (G x) - ‖G‖ ^ 2 • x‖ := by
  rintro ⟨d, hd, hbound⟩
  let M := ‖G‖
  let k := M ^ 2 - d ^ 2 / (2 * M ^ 2)
  let K := sqrt (max 0 k)
  have hM' : 0 < M := hM
  have hM₂ : 0 < 2 * M ^ 2 := by positivity
  have hK : 0 ≤ K := sqrt_nonneg _
  have hKsq : K ^ 2 = max 0 k := sq_sqrt (le_max_left _ _)
  have hKlt : K < M := by
    apply (sq_lt_sq₀ hK hM'.le).1
    rw [hKsq]
    exact max_lt_iff.mpr ⟨sq_pos_of_pos hM', sub_lt_self _ (div_pos (sq_pos_of_pos hd) hM₂)⟩
  have hboundK (x : MorseL2) : ‖G x‖ ≤ K * ‖x‖ := by
    have hGG : ‖G (G x)‖ ≤ M ^ 2 * ‖x‖ := calc
      _ ≤ M * ‖G x‖ := G.le_opNorm _
      _ ≤ M * (M * ‖x‖) := mul_le_mul_of_nonneg_left (G.le_opNorm _) hM'.le
      _ = _ := by ring
    have hInner : ⟪G (G x), x⟫_ℝ = ‖G x‖ ^ 2 :=
      (hSym (G x) x).trans (real_inner_self_eq_norm_sq _)
    have hR := norm_sub_sq_real (G (G x)) (M ^ 2 • x)
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg M), real_inner_smul_right, hInner] at hR
    have hUp := (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (sq_nonneg M) (norm_nonneg x))).2 hGG
    have hLo := (sq_le_sq₀ (mul_nonneg hd.le (norm_nonneg x)) (norm_nonneg _)).2 (hbound x)
    have hLo' : (d * ‖x‖) ^ 2 ≤ ‖G (G x) - M ^ 2 • x‖ ^ 2 := hLo
    have hS : (2 * M ^ 2) * ‖G x‖ ^ 2 ≤ (2 * M ^ 2 * M ^ 2 - d ^ 2) * ‖x‖ ^ 2 := by
      nlinarith only [hR, hUp, hLo']
    have hmul : (2 * M ^ 2) * (k * ‖x‖ ^ 2) = (2 * M ^ 2 * M ^ 2 - d ^ 2) * ‖x‖ ^ 2 := by
      calc
        _ = (2 * M ^ 2 * M ^ 2 - (2 * M ^ 2) * (d ^ 2 / (2 * M ^ 2))) * ‖x‖ ^ 2 := by
          dsimp [k]
          ring
        _ = _ := by rw [mul_div_cancel₀ _ hM₂.ne']
    apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hK (norm_nonneg x))).1
    rw [mul_pow, hKsq]
    exact (le_of_mul_le_mul_left (hS.trans_eq hmul.symm) hM₂).trans
      (mul_le_mul_of_nonneg_right (le_max_right _ _) (sq_nonneg _))
  exact not_lt_of_ge (G.opNorm_le_bound hK hboundK) hKlt

/-- The actual weak zero inverse has norm at most the reciprocal of a gap
to the threshold and to all genuine subthreshold eigenvalues. -/
theorem morseWeakResolventBound_of_subthreshold_gap {j A B δ : ℝ} (hj : 0 < j) (hA : 0 < A)
    (hδ : 0 < δ) (hδb : δ ≤ j ^ 2 * B)
    (hgap : ∀ E : ℝ, E < j ^ 2 * B → Statements.ActualEigenvalue (Statements.morsePotential j A B) E →
      δ ≤ |E|) :
    Statements.WeakResolventBound (Statements.morsePotential j A B) 0 δ⁻¹ := by
  have hBelow (E : ℝ) (hE : |E| < δ) : E < j ^ 2 * B :=
    (le_abs_self E).trans_lt (hE.trans_le hδb)
  have hNo (E : ℝ) (hE : |E| < δ) : ¬ Statements.ActualEigenvalue (Statements.morsePotential j A B) E := by
    intro he
    exact (not_le.mpr hE) (hgap E (hBelow E hE) he)
  have hzero : |(0 : ℝ)| < δ := by simpa only [abs_zero] using hδ
  obtain ⟨_, _, G, _, hGraph, hUnique⟩ :=
    morseWeakResolventBound_of_noEigen hj hA B 0 (hBelow 0 hzero) (hNo 0 hzero)
  refine ⟨G, ?_, hGraph, hUnique⟩
  have hG₀ (x : MorseL2) : Statements.WeakSchrodingerGraph (Statements.morsePotential j A B) (G x) x := by
    simpa only [zero_smul, add_zero] using hGraph x
  have hSym (x y : MorseL2) : ⟪G x, y⟫_ℝ = ⟪x, G y⟫_ℝ :=
    (morseAssociatedGraph_symmetric _ _ _ (G x, x) (G y, y)
      ((morsePublicWeakGraph_iff_associated hj hA B _ _).mp (hG₀ x))
      ((morsePublicWeakGraph_iff_associated hj hA B _ _).mp (hG₀ y))).symm
  by_contra! hbad
  let M := ‖G‖
  have hM : 0 < M := (inv_pos.mpr hδ).trans hbad
  have hInv : M⁻¹ < δ := (inv_lt_comm₀ hM hδ).2 hbad
  have hPos : |M⁻¹| < δ := by rwa [abs_of_pos (inv_pos.mpr hM)]
  have hNeg : |(-M)⁻¹| < δ := by rwa [inv_neg, abs_neg]
  have hlower (e : ℝ) (he : |e⁻¹| < δ) :
      ∃ c : ℝ, 0 < c ∧ ∀ x : MorseL2, c * ‖G x‖ ≤ ‖x - e⁻¹ • G x‖ := by
    obtain ⟨c, hc, hb⟩ := morseWeakGraph_boundedBelow_of_noEigen hj hA B e⁻¹ (hBelow _ he) (hNo _ he)
    refine ⟨c, hc, fun x => hb _ _ ?_⟩
    rw [sub_add_cancel]
    exact hG₀ x
  obtain ⟨cPos, hcPos, hBPos⟩ := hlower M hPos
  obtain ⟨cNeg, hcNeg, hBNeg⟩ := hlower (-M) hNeg
  obtain ⟨dPos, hdPos, hFactorPos⟩ := morseInverse_shift_factor_boundedBelow G hM.ne' hcPos hBPos
  obtain ⟨dNeg, hdNeg, hFactorNeg⟩ := morseInverse_shift_factor_boundedBelow G (neg_ne_zero.mpr hM.ne') hcNeg hBNeg
  exact morseSymmetricInverse_square_not_boundedBelow G hSym hM
    ⟨dPos * dNeg, mul_pos hdPos hdNeg, morseInverse_square_boundedBelow G M hdPos.le hFactorPos hFactorNeg⟩

end ContinuousFlexibility.Radial
