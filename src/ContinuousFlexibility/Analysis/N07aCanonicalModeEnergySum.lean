module

public import ContinuousFlexibility.Analysis.N07aCanonicalActualModeEnergy
public import ContinuousFlexibility.Analysis.N07aCanonicalModeBessel

/-!
# Summing the actual positive mode energies

The source is an arbitrary canonical L² class. Its finite cosine Bessel
bound suffices, and the final sum controls the same weak second normal
derivative as the original reference equation.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set MeasureTheory ContinuousFlexibility.Statements CanonicalGeometry

theorem n07aCylinderSquare_nonneg (p : ℕ) (u : N07aIntervalL2) :
    0 ≤ n07aCylinderSquare p u := by
  rw [n07aCylinderSquare_eq]
  apply integral_nonneg_of_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
  exact mul_nonneg (pow_nonneg (cylinderWeight_nonneg (Ioo_subset_Icc_self hx)) p) (sq_nonneg _)

theorem n07aCylinderEnergy_nonneg (j : ℝ) (u d dd : N07aIntervalL2) :
    0 ≤ n07aCylinderEnergy j u d dd := by
  unfold n07aCylinderEnergy
  have hj : 0 ≤ 1 + j ^ 2 := by positivity
  exact add_nonneg (add_nonneg (add_nonneg (add_nonneg
    (n07aCylinderSquare_nonneg 2 d)
    (mul_nonneg hj (n07aCylinderSquare_nonneg 3 u)))
    (n07aCylinderSquare_nonneg 4 dd))
    (mul_nonneg (sq_nonneg _) (n07aCylinderSquare_nonneg 6 u)))
    (mul_nonneg hj (n07aCylinderSquare_nonneg 5 d))

def n07aReferenceModeBudget (A P Q ℓ E : ℝ) : ℝ :=
  (16384 * (4 * (1 + A * E ^ A + P * E ^ P) ^ 5) ^ 10) *
    (2 * (1 + (ℓ ^ 2 * (Q * E ^ Q)) ^ 2 + ℓ ^ 4)) * (ℓ⁻¹ * Real.pi⁻¹)

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {L : ReturnCorrectionData S} {K : CanonicalData S}

def n07aCanonicalModeEnergy {m : ℕ} (hm : K.left m < K.right m)
    (u ur urr : CanonicalL2 S K m) (n : ℕ) : ℝ :=
  n07aCylinderEnergy (2 * (n : ℝ)) (n07aCanonicalUnitMode hm u n)
    ((K.right m - K.left m) • n07aCanonicalUnitMode hm ur n)
    ((K.right m - K.left m) ^ 2 • n07aCanonicalUnitMode hm urr n)

theorem n07a_reference_actualMode_sum
    (hJ : ReferenceJets D T S C L K) (hP : ReferencePrincipal T S C K)
    (hE : ∀ m, 0 < T.E0 (T.sample (K.cell m)))
    (hlen : ∀ m, K.left m < K.right m) :
    ∃ A P Q : ℝ, 0 < A ∧ 0 < P ∧ 0 < Q ∧
      ∀ m, K.positive m = true → ∀ u ur urr G : CanonicalL2 S K m,
      N07aWeakCanonicalMixedDerivative S K m u ur 1 0 →
      N07aWeakCanonicalMixedDerivative S K m ur urr 1 0 →
      N07aCanonicalDistributionEquation S K m (K.coefficients (C.referenceState, 0) m) u G →
      Summable (n07aCanonicalModeEnergy (hlen m) u ur urr) ∧
        (∑' n, n07aCanonicalModeEnergy (hlen m) u ur urr n) ≤
          n07aReferenceModeBudget A P Q (K.right m - K.left m)
            (T.E0 (T.sample (K.cell m))) * (‖u‖ ^ 2 + ‖G‖ ^ 2) := by
  obtain ⟨A, P, Q, hA, hPpos, hQ, hb⟩ := n07a_reference_actualMode_energy hJ hP hE hlen
  refine ⟨A, P, Q, hA, hPpos, hQ, ?_⟩
  intro m hm u ur urr G hr hrr heq
  let ℓ := K.right m - K.left m
  let E := T.E0 (T.sample (K.cell m))
  let K₀ := 16384 * (4 * (1 + A * E ^ A + P * E ^ P) ^ 5) ^ 10
  let R := ℓ ^ 2 * (Q * E ^ Q)
  let B₀ := K₀ * (2 * (1 + R ^ 2 + ℓ ^ 4))
  have hK₀ : 0 ≤ K₀ := by dsimp only [K₀]; positivity
  have hB₀ : 0 ≤ B₀ := mul_nonneg hK₀ (by positivity)
  have hfinite (I : Finset ℕ) :
      (∑ n ∈ I, n07aCanonicalModeEnergy (hlen m) u ur urr n) ≤
        n07aReferenceModeBudget A P Q ℓ E * (‖u‖ ^ 2 + ‖G‖ ^ 2) := by
    calc
      _ ≤ ∑ n ∈ I, B₀ * (‖n07aCanonicalUnitMode (hlen m) u n‖ ^ 2 +
          ‖n07aCanonicalUnitMode (hlen m) G n‖ ^ 2) := by
        apply Finset.sum_le_sum
        intro n _
        exact (hb m hm u ur urr G hr hrr heq n).trans
          ((mul_le_mul_of_nonneg_left
            (n07a_mode_source_square_le R ℓ ‖n07aCanonicalUnitMode (hlen m) u n‖
              ‖n07aCanonicalUnitMode (hlen m) G n‖) hK₀).trans_eq (by
                exact (mul_assoc _ _ _).symm))
      _ = B₀ * ((∑ n ∈ I, ‖n07aCanonicalUnitMode (hlen m) u n‖ ^ 2) +
          ∑ n ∈ I, ‖n07aCanonicalUnitMode (hlen m) G n‖ ^ 2) := by
        rw [← Finset.mul_sum, Finset.sum_add_distrib]
      _ ≤ B₀ * (ℓ⁻¹ * (Real.pi⁻¹ * ‖u‖ ^ 2) +
          ℓ⁻¹ * (Real.pi⁻¹ * ‖G‖ ^ 2)) :=
        mul_le_mul_of_nonneg_left (add_le_add
          (n07aCanonicalUnitMode_sum_sq_le (hlen m) u I)
          (n07aCanonicalUnitMode_sum_sq_le (hlen m) G I)) hB₀
      _ = _ := by
        change B₀ * (ℓ⁻¹ * (Real.pi⁻¹ * ‖u‖ ^ 2) +
          ℓ⁻¹ * (Real.pi⁻¹ * ‖G‖ ^ 2)) =
            (B₀ * (ℓ⁻¹ * Real.pi⁻¹)) * (‖u‖ ^ 2 + ‖G‖ ^ 2)
        rw [← mul_add, ← mul_add]
        simp only [mul_assoc]
  have hnonneg : 0 ≤ n07aCanonicalModeEnergy (hlen m) u ur urr :=
    fun n => n07aCylinderEnergy_nonneg _ _ _ _
  exact ⟨summable_of_sum_le hnonneg hfinite, Real.tsum_le_of_sum_le hnonneg hfinite⟩

end ContinuousFlexibility.Analysis
