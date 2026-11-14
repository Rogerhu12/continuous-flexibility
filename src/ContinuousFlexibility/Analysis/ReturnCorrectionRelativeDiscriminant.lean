import ContinuousFlexibility.Analysis.ReturnCoefficientParity

/-!
# The relative discriminant retained by the actual return patch

The two actual characteristic-speed errors control the reconstructed
half-gap. At active points the squared gap retains one quarter of the
original discriminant. At inactive points the actual patch is exactly
the original coefficient object. No regularity or coefficient estimate
for a proposed corrected field is an input to this algebraic transfer.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open Set
open ContinuousFlexibility.Analysis

set_option backward.isDefEq.respectTransparency false

/-- Keep the quantitative half-gap conclusion of the scalar correction
lemma, with the reflected actual minus speed as the plus family. -/
theorem n04Coordinates_correctedHalfGap_lower
    (A : SymmetricCoefficients) (v : PolarPoint → ℝ) (r θ : ℝ)
    (hreflection : minusCharacteristicSpeed A (r, -θ) =
      -plusCharacteristicSpeed A (r, θ))
    (hq : 0 < Real.sqrt (A.b (r, θ) ^ 2 - A.a (r, θ) * A.c (r, θ)) / A.a (r, θ))
    (hminus : |v (r, θ) - minusCharacteristicSpeed A (r, θ)| ≤
      (Real.sqrt (A.b (r, θ) ^ 2 - A.a (r, θ) * A.c (r, θ)) / A.a (r, θ)) / 2)
    (hreflected : |v (r, -θ) - minusCharacteristicSpeed A (r, -θ)| ≤
      (Real.sqrt (A.b (r, θ) ^ 2 - A.a (r, θ) * A.c (r, θ)) / A.a (r, θ)) / 2) :
    (Real.sqrt (A.b (r, θ) ^ 2 - A.a (r, θ) * A.c (r, θ)) / A.a (r, θ)) / 2 ≤
      (-v (r, -θ) - v (r, θ)) / 2 := by
  have h := (returnCorrection_speed_positive hq hminus
    (show |-(v (r, -θ) - minusCharacteristicSpeed A (r, -θ))| ≤ _ by
      simpa only [abs_neg] using hreflected)).1
  rw [hreflection] at h
  simp only [minusCharacteristicSpeed, plusCharacteristicSpeed] at h
  linarith only [h]

private theorem n04Coordinates_scaled_gap_square_lower
    {a d v : ℝ} (ha : 0 < a) (hd : 0 ≤ d)
    (hv : (Real.sqrt d / a) / 2 ≤ v) :
    d / 4 ≤ (a * v) ^ 2 := by
  have hscaled : Real.sqrt d / 2 ≤ a * v := by
    calc
      _ = a * ((Real.sqrt d / a) / 2) := by
        field_simp [ha.ne']
      _ ≤ a * v := mul_le_mul_of_nonneg_left hv ha.le
  have hsquare := pow_le_pow_left₀
    (div_nonneg (Real.sqrt_nonneg d) (by norm_num : (0 : ℝ) ≤ 2)) hscaled 2
  nlinarith only [hsquare, Real.sq_sqrt hd]

/-- The actual global patch retains at least one quarter of the
original discriminant. The error hypotheses are needed only where its
cutoff derivative is nonzero. -/
theorem n04Coordinates_returnCorrectedDiscriminant_quarter
    {D : ReferenceData} {S : PhysicalSpacesData} {C : NonlinearGeometryData S}
    (hdisj : ∀ m n, m ≠ n → Disjoint (Ioo (C.left m) (C.right m))
      (Ioo (C.left n) (C.right n)))
    (χ : ℕ → ℝ → ℝ) (z : AnnularState S × ℝ) (m : ℕ) (p : PolarPoint)
    (hp : p.1 ∈ Ioo (C.left m) (C.right m))
    (ha : 0 < (originalCoefficients D S C z).a p)
    (hd : 0 < (originalCoefficients D S C z).b p ^ 2 -
      (originalCoefficients D S C z).a p * (originalCoefficients D S C z).c p)
    (hreflection : minusCharacteristicSpeed (originalCoefficients D S C z) (p.1, -p.2) =
      -plusCharacteristicSpeed (originalCoefficients D S C z) p)
    (herror : deriv (χ m) p.1 ≠ 0 →
      |returnCorrectedMinusSpeed D S C χ z m p -
        minusCharacteristicSpeed (originalCoefficients D S C z) p| ≤
          (Real.sqrt ((originalCoefficients D S C z).b p ^ 2 -
            (originalCoefficients D S C z).a p * (originalCoefficients D S C z).c p) /
              (originalCoefficients D S C z).a p) / 2 ∧
      |returnCorrectedMinusSpeed D S C χ z m (p.1, -p.2) -
        minusCharacteristicSpeed (originalCoefficients D S C z) (p.1, -p.2)| ≤
          (Real.sqrt ((originalCoefficients D S C z).b p ^ 2 -
            (originalCoefficients D S C z).a p * (originalCoefficients D S C z).c p) /
              (originalCoefficients D S C z).a p) / 2) :
    ((originalCoefficients D S C z).b p ^ 2 -
      (originalCoefficients D S C z).a p * (originalCoefficients D S C z).c p) / 4 ≤
        (returnCorrectedCoefficients D S C χ z).b p ^ 2 -
          (returnCorrectedCoefficients D S C χ z).a p *
            (returnCorrectedCoefficients D S C χ z).c p := by
  by_cases hχ : deriv (χ m) p.1 = 0
  · obtain ⟨hb, hc⟩ := returnCorrectedCoefficients_eq_original_at_of_deriv_zero
      (D := D) hdisj χ z m p hp hχ
    rw [returnCorrectedCoefficients_a, hb, hc]
    linarith only [hd]
  · obtain ⟨he, her⟩ := herror hχ
    have hgap := n04Coordinates_correctedHalfGap_lower
      (originalCoefficients D S C z) (returnCorrectedMinusSpeed D S C χ z m)
      p.1 p.2 hreflection (div_pos (Real.sqrt_pos.mpr hd) ha) he her
    have hbound := n04Coordinates_scaled_gap_square_lower ha hd.le hgap
    obtain ⟨hb, hc⟩ := returnCorrectedCoefficients_eq_component_at
      (D := D) hdisj χ z m p hp hχ
    have hdet : (returnCorrectedComponentCoefficients D S C χ z m).b p ^ 2 -
        (originalCoefficients D S C z).a p *
          (returnCorrectedComponentCoefficients D S C χ z m).c p =
        ((originalCoefficients D S C z).a p *
          ((-returnCorrectedMinusSpeed D S C χ z m (p.1, -p.2) -
            returnCorrectedMinusSpeed D S C χ z m p) / 2)) ^ 2 := by
      exact returnCorrection_discriminant _ _ _
    rw [returnCorrectedCoefficients_a, hb, hc, hdet]
    exact hbound

end ContinuousFlexibility.Statements
