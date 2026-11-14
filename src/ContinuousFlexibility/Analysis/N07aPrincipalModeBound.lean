module

public import ContinuousFlexibility.Analysis.N07aScaledModeNorms
public import ContinuousFlexibility.Analysis.N07aActualPrincipalRows

/-!
# A principal block is controlled by its original weak mode energy

This estimate consumes the actual first and second weak derivatives.
The eight divergence terms are bounded with their correct affine length
factors and the cubic rows of the same coefficient multipliers.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set ContinuousFlexibility.Statements

private theorem n07a_norm_eight {E : Type*} [SeminormedAddCommGroup E]
    (a b c d e f g : E) :
    ‖((a + b) + (c + d)) + ((c + e) + (f + g))‖ ≤
      ((‖a‖ + ‖b‖) + (‖c‖ + ‖d‖)) + ((‖c‖ + ‖e‖) + (‖f‖ + ‖g‖)) :=
  (norm_add_le _ _).trans (add_le_add
    ((norm_add_le _ _).trans (add_le_add (norm_add_le _ _) (norm_add_le _ _)))
    ((norm_add_le _ _).trans (add_le_add (norm_add_le _ _) (norm_add_le _ _))))

variable {S : PhysicalSpacesData} {K : CanonicalData S} {m : ℕ}

theorem n07a_principalMode_bound (hm : K.left m < K.right m)
    (χ : Fin 3 → N07aCanonicalOpenCoefficient S K m)
    (u ur uθ urr urθ uθθ : CanonicalL2 S K m)
    (hu : n07aAngularReflection m u = u) (j l : ℕ)
    (hb : n07aAngularBand m hm j u = u)
    (hr : N07aWeakCanonicalMixedDerivative S K m u ur 1 0)
    (hθ : N07aWeakCanonicalMixedDerivative S K m u uθ 0 1)
    (hrr : N07aWeakCanonicalMixedDerivative S K m ur urr 1 0)
    (hrθ : N07aWeakCanonicalMixedDerivative S K m ur urθ 0 1)
    (hθθ : N07aWeakCanonicalMixedDerivative S K m uθ uθθ 0 1)
    {κ M : ℝ} (hM : 0 ≤ M)
    (hval : ∀ i sine x, x ∈ Ioo (0 : ℝ) 1 →
      |κ * n07aTrigMatrixEntry sine
        (fun θ => (χ i).value (n07aIntervalUnitMap (K.left m) (K.right m) x, θ)) l j| ≤
        (K.right m - K.left m) ^ 6 * M * cylinderWeight x ^ 3)
    (hnormal : ∀ i sine x, x ∈ Ioo (0 : ℝ) 1 →
      |κ * n07aTrigMatrixEntry sine
        (fun θ => ((χ i).jet 1 0).value (n07aIntervalUnitMap (K.left m) (K.right m) x, θ)) l j| ≤
        4 * (K.right m - K.left m) ^ 5 * M * cylinderWeight x ^ 2)
    (hangular : ∀ i sine x, x ∈ Ioo (0 : ℝ) 1 →
      |κ * n07aTrigMatrixEntry sine
        (fun θ => ((χ i).jet 0 1).value (n07aIntervalUnitMap (K.left m) (K.right m) x, θ)) l j| ≤
        (K.right m - K.left m) ^ 6 * M * cylinderWeight x ^ 3) :
    ‖κ • n07aCanonicalUnitMode hm (n07aOpenDivergence (χ 0) (χ 1) (χ 2) ur uθ urr urθ uθθ) l‖ ≤
      14 * (1 + (K.right m - K.left m)) ^ 6 * M *
        Real.sqrt (n07aScaledModeEnergy (K.right m - K.left m) (2 * (j : ℝ))
          (n07aCanonicalUnitMode hm u j) (n07aCanonicalUnitMode hm ur j)
          (n07aCanonicalUnitMode hm urr j)) := by
  let ℓ := K.right m - K.left m
  let ω := 2 * (j : ℝ)
  let E := Real.sqrt (n07aScaledModeEnergy ℓ ω
    (n07aCanonicalUnitMode hm u j) (n07aCanonicalUnitMode hm ur j) (n07aCanonicalUnitMode hm urr j))
  have hℓ : 0 < ℓ := sub_pos.mpr hm
  have hω : 0 ≤ ω := by positivity
  have hE : 0 ≤ E := Real.sqrt_nonneg _
  have hur := n07a_weakCanonical_radial_reflection hm hu hr
  have hurr := n07a_weakCanonical_radial_reflection hm hur hrr
  have hbr := n07a_firstNormal_singleBand hm hu hr j hb
  have hbrr := n07a_firstNormal_singleBand hm hur hrr j hbr
  have hvalCos (i : Fin 3) := hval i false
  have hvalSin (i : Fin 3) := hval i true
  have hnormCos (i : Fin 3) := hnormal i false
  have hnormSin (i : Fin 3) := hnormal i true
  have hangCos (i : Fin 3) := hangular i false
  have hangSin (i : Fin 3) := hangular i true
  simp only [n07aTrigMatrixEntry, Bool.false_eq_true, ite_false, ite_true] at hvalCos hvalSin hnormCos hnormSin hangCos hangSin
  have ha := n07aCanonicalProduct_cosine_norm_le hm (χ 0) urr hurr j l 3 hbrr
    (mul_nonneg (pow_nonneg hℓ.le 6) hM) (hvalCos 0)
  have har := n07aCanonicalProduct_cosine_norm_le hm ((χ 0).jet 1 0) ur hur j l 2 hbr
    (by positivity : 0 ≤ 4 * ℓ ^ 5 * M) (hnormCos 0)
  have hcross := n07aCanonicalProduct_sine_norm_le hm (χ 1) ur urθ hur j l 3 hbr hrθ
    (mul_nonneg (pow_nonneg hℓ.le 6) hM) (hvalSin 1)
  have hbrθ := n07aCanonicalProduct_sine_norm_le hm ((χ 1).jet 1 0) u uθ hu j l 2 hb hθ
    (by positivity : 0 ≤ 4 * ℓ ^ 5 * M) (hnormSin 1)
  have hbθr := n07aCanonicalProduct_cosine_norm_le hm ((χ 1).jet 0 1) ur hur j l 3 hbr
    (mul_nonneg (pow_nonneg hℓ.le 6) hM) (hangCos 1)
  have hc := n07aCanonicalProduct_cosine_norm_le hm (χ 2) u hu j l 3 hb
    (mul_nonneg (pow_nonneg hℓ.le 6) hM) (hvalCos 2)
  have hcθ := n07aCanonicalProduct_sine_norm_le hm ((χ 2).jet 0 1) u uθ hu j l 3 hb hθ
    (mul_nonneg (pow_nonneg hℓ.le 6) hM) (hangSin 2)
  obtain ⟨he₀, he₁, he₂, he₃, he₄, he₅, he₆⟩ := n07a_scaledMode_norm_bounds hℓ hω
    (n07aCanonicalUnitMode hm u j) (n07aCanonicalUnitMode hm ur j) (n07aCanonicalUnitMode hm urr j)
  have ha' : ‖κ • n07aCanonicalUnitMode hm ((χ 0).mul urr) l‖ ≤ ℓ ^ 4 * M * E := by
    nlinarith only [ha, mul_le_mul_of_nonneg_left he₀ hM]
  have har' : ‖κ • n07aCanonicalUnitMode hm (((χ 0).jet 1 0).mul ur) l‖ ≤ 4 * ℓ ^ 4 * M * E := by
    nlinarith only [har, mul_le_mul_of_nonneg_left he₁ (show 0 ≤ 4 * M by positivity)]
  have hcross' : ‖κ • n07aCanonicalUnitMode hm ((χ 1).mul urθ) l‖ ≤ ℓ ^ 5 * M * E := by
    nlinarith only [hcross, mul_le_mul_of_nonneg_left he₂ hM]
  have hbrθ' : ‖κ • n07aCanonicalUnitMode hm (((χ 1).jet 1 0).mul uθ) l‖ ≤ 4 * ℓ ^ 5 * M * E := by
    nlinarith only [hbrθ, mul_le_mul_of_nonneg_left he₃ (show 0 ≤ 4 * M by positivity)]
  have hbθr' : ‖κ • n07aCanonicalUnitMode hm (((χ 1).jet 0 1).mul ur) l‖ ≤ ℓ ^ 5 * M * E := by
    nlinarith only [hbθr, mul_le_mul_of_nonneg_left he₅ hM]
  have hc' : ‖κ • n07aCanonicalUnitMode hm ((χ 2).mul uθθ) l‖ ≤ ℓ ^ 6 * M * E := by
    have hd := n07a_secondAngular_singleBand_eq hm hu j hb (by
      simpa only [Nat.zero_add] using hθ.comp hθθ)
    rw [hd, map_smul, n07aCanonicalUnitMode_smul, smul_comm κ (-(ω ^ 2)),
      norm_smul, Real.norm_eq_abs, abs_neg, abs_of_nonneg (sq_nonneg ω)]
    have hh := mul_le_mul_of_nonneg_left hc (sq_nonneg ω)
    nlinarith only [hh, mul_le_mul_of_nonneg_left he₄ hM]
  have hcθ' : ‖κ • n07aCanonicalUnitMode hm (((χ 2).jet 0 1).mul uθ) l‖ ≤ ℓ ^ 6 * M * E := by
    nlinarith only [hcθ, mul_le_mul_of_nonneg_left he₆ hM]
  have hall : ‖κ • n07aCanonicalUnitMode hm
      (n07aOpenDivergence (χ 0) (χ 1) (χ 2) ur uθ urr urθ uθθ) l‖ ≤
      (5 * ℓ ^ 4 + 7 * ℓ ^ 5 + 2 * ℓ ^ 6) * M * E := by
    simp only [n07aOpenDivergence, n07aCanonicalUnitMode_add, smul_add]
    have h := n07a_norm_eight
      (κ • n07aCanonicalUnitMode hm ((χ 0).mul urr) l)
      (κ • n07aCanonicalUnitMode hm (((χ 0).jet 1 0).mul ur) l)
      (κ • n07aCanonicalUnitMode hm ((χ 1).mul urθ) l)
      (κ • n07aCanonicalUnitMode hm (((χ 1).jet 1 0).mul uθ) l)
      (κ • n07aCanonicalUnitMode hm (((χ 1).jet 0 1).mul ur) l)
      (κ • n07aCanonicalUnitMode hm ((χ 2).mul uθθ) l)
      (κ • n07aCanonicalUnitMode hm (((χ 2).jet 0 1).mul uθ) l)
    nlinarith only [h, ha', har', hcross', hbrθ', hbθr', hc', hcθ']
  exact hall.trans (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right (n07a_scaledMode_principal_budget hℓ.le) hM) hE)

end ContinuousFlexibility.Analysis
