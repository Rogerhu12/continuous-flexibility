import ContinuousFlexibility.Analysis.N01cCutoffJetBounds
import ContinuousFlexibility.Analysis.N01cStateHeightJets
import ContinuousFlexibility.Analysis.N01cStateSeminorms

/-!
# Fixed-loss bounds for the actual state height direction

The scalar cutoff contributes only compactly supported positive-order
jets. Combining these with the decoded physical height gives a bound
for every positive-order mixed jet of stateU with exactly two additional
input grading orders and the original H^(3/4) weight.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open Set

theorem state_height_grading_le (S : PhysicalSpacesData) (n : ℕ)
    (x : AnnularState S) :
    (S.height (3 / 4 : ℝ)).grading n x.1.1 ≤ stateGrading S n x := by
  rw [stateGrading_apply]
  have hc := norm_nonneg x.1.2
  have hν := norm_nonneg x.2.1
  have hκ := apply_nonneg ((S.circle (3 / 4 : ℝ)).grading n) x.2.2.1
  have hh := apply_nonneg ((S.circle (3 / 4 : ℝ)).grading n) x.2.2.2
  linarith only [hc, hν, hκ, hh]

theorem abs_stateHeightScalar_le_stateGrading (S : PhysicalSpacesData) (n : ℕ)
    (x : AnnularState S) :
    |x.1.2| ≤ stateGrading S n x := by
  rw [stateGrading_apply, ← Real.norm_eq_abs]
  have hf := apply_nonneg ((S.height (3 / 4 : ℝ)).grading n) x.1.1
  have hν := norm_nonneg x.2.1
  have hκ := apply_nonneg ((S.circle (3 / 4 : ℝ)).grading n) x.2.2.1
  have hh := apply_nonneg ((S.circle (3 / 4 : ℝ)).grading n) x.2.2.2
  linarith only [hf, hν, hκ, hh]

/-- The raw product bound for a single genuine state-height jet. The
constant and E0 power are spatially uniform and the input loss is two. -/
theorem stateU_positiveMixedJets_le_E0_stateGrading
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S) (s : ℕ) :
    ∃ C A : ℝ, 0 ≤ C ∧ 0 ≤ A ∧ ∀ x : AnnularState S, ∀ a b : ℕ,
      0 < a + b → a + b ≤ s → ∀ p ∈ annularOpen D,
        |mixedDerivative a b (stateU S x) p| ≤
          C * T.E0 p.1 ^ A * T.H p.1 ^ (3 / 4 : ℝ) *
            stateGrading S (s + 2) x := by
  obtain ⟨C₀, A, hC₀, hA, hheight⟩ :=
    sobolevModel_physicalMixedJets_le_E0_grading hT (hS.1 (3 / 4 : ℝ)) s
  obtain ⟨Cχ, hCχ, hcutoff⟩ :=
    cutoff_positiveJets_le_materialHeight hT hS.2.2.1 (3 / 4 : ℝ) s
  obtain ⟨K, hK, hEraise⟩ := materialE0_rpow_le_of_exponent_le hT (A := 0) hA
  refine ⟨C₀ + Cχ * K, A, add_nonneg hC₀ (mul_nonneg hCχ hK), hA,
    fun x a b hab horder p hp => ?_⟩
  have hH : 0 ≤ T.H p.1 ^ (3 / 4 : ℝ) :=
    Real.rpow_nonneg (hT.2.1 _ hp.1).2.1.le _
  have hE : 0 ≤ T.E0 p.1 ^ A :=
    Real.rpow_nonneg (hT.2.1 _ hp.1).2.2.1.le _
  have hG : 0 ≤ stateGrading S (s + 2) x := apply_nonneg _ _
  have hscale : 1 ≤ K * T.E0 p.1 ^ A := by
    simpa only [Real.rpow_zero] using hEraise p.1 hp.1
  have hcut :
      |if b = 0 then iteratedDeriv a S.chiLeft p.1 else 0| ≤
        Cχ * T.H p.1 ^ (3 / 4 : ℝ) := by
    split_ifs with hb
    · exact hcutoff a (by omega) (by omega) p.1 hp.1
    · rw [abs_zero]
      exact mul_nonneg hCχ hH
  have hcutraise : Cχ * T.H p.1 ^ (3 / 4 : ℝ) ≤
      (Cχ * K) * T.E0 p.1 ^ A * T.H p.1 ^ (3 / 4 : ℝ) := by
    calc
      _ = (Cχ * T.H p.1 ^ (3 / 4 : ℝ)) * 1 := (mul_one _).symm
      _ ≤ (Cχ * T.H p.1 ^ (3 / 4 : ℝ)) * (K * T.E0 p.1 ^ A) :=
        mul_le_mul_of_nonneg_left hscale (mul_nonneg hCχ hH)
      _ = _ := by ring
  have hdecoded :
      |mixedDerivative a b ((S.height (3 / 4 : ℝ)).decode x.1.1) p| ≤
        C₀ * T.E0 p.1 ^ A * T.H p.1 ^ (3 / 4 : ℝ) *
          stateGrading S (s + 2) x :=
    (hheight x.1.1 a b horder p hp).trans
      (mul_le_mul_of_nonneg_left (state_height_grading_le S (s + 2) x)
        (mul_nonneg (mul_nonneg hC₀ hE) hH))
  have hscalar :
      |x.1.2 * (if b = 0 then iteratedDeriv a S.chiLeft p.1 else 0)| ≤
        (Cχ * K) * T.E0 p.1 ^ A * T.H p.1 ^ (3 / 4 : ℝ) *
          stateGrading S (s + 2) x := by
    rw [abs_mul]
    calc
      _ ≤ stateGrading S (s + 2) x *
          ((Cχ * K) * T.E0 p.1 ^ A * T.H p.1 ^ (3 / 4 : ℝ)) :=
        mul_le_mul (abs_stateHeightScalar_le_stateGrading S (s + 2) x)
          (hcut.trans hcutraise) (abs_nonneg _) hG
      _ = _ := mul_comm _ _
  rw [mixedDerivative_stateU hT hS a b p x]
  calc
    _ ≤ |mixedDerivative a b ((S.height (3 / 4 : ℝ)).decode x.1.1) p| +
        |x.1.2 * (if b = 0 then iteratedDeriv a S.chiLeft p.1 else 0)| :=
      abs_add_le _ _
    _ ≤ C₀ * T.E0 p.1 ^ A * T.H p.1 ^ (3 / 4 : ℝ) * stateGrading S (s + 2) x +
        (Cχ * K) * T.E0 p.1 ^ A * T.H p.1 ^ (3 / 4 : ℝ) * stateGrading S (s + 2) x :=
      add_le_add hdecoded hscalar
    _ = _ := by ring

end ContinuousFlexibility.Statements
