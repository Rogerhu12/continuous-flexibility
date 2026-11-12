import ContinuousFlexibility.Analysis.N07aModeBudgetMaterial
import ContinuousFlexibility.Analysis.N07aScaledModeNorms

/-!
# Norm bounds from the actual mode energy

The summable energy controls each individual mode of the same weak
solution.  The affine radial normalization is then converted back to the
actual canonical angular-band norm, with its exact length factor.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set MeasureTheory ContinuousFlexibility.Statements CanonicalGeometry

theorem n07a_referenceModeBudget_nonneg (A P Q E : ℝ) {ℓ : ℝ} (hℓ : 0 < ℓ) :
    0 ≤ n07aReferenceModeBudget A P Q ℓ E := by
  unfold n07aReferenceModeBudget
  positivity

theorem n07a_sqrt_energy_le {e B x y : ℝ}
    (hB : 0 ≤ B) (hx : 0 ≤ x) (hy : 0 ≤ y)
    (he : e ≤ B * (x ^ 2 + y ^ 2)) :
    Real.sqrt e ≤ Real.sqrt B * (x + y) := by
  apply Real.sqrt_le_iff.mpr
  refine ⟨mul_nonneg (Real.sqrt_nonneg _) (add_nonneg hx hy), ?_⟩
  rw [mul_pow, Real.sq_sqrt hB]
  exact he.trans (mul_le_mul_of_nonneg_left (by nlinarith [mul_nonneg hx hy]) hB)

variable {S : PhysicalSpacesData} {K : CanonicalData S} {m : ℕ}

theorem n07aCanonicalModeEnergy_eq_scaled (hm : K.left m < K.right m)
    (u ur urr : CanonicalL2 S K m) (j : ℕ) :
    n07aCanonicalModeEnergy hm u ur urr j =
      n07aScaledModeEnergy (K.right m - K.left m) (2 * (j : ℝ))
        (n07aCanonicalUnitMode hm u j) (n07aCanonicalUnitMode hm ur j)
        (n07aCanonicalUnitMode hm urr j) := rfl

theorem n07aAngularBand_norm_unitMode (hm : K.left m < K.right m)
    (u : CanonicalL2 S K m) (hu : n07aAngularReflection m u = u) (j : ℕ) :
    ‖n07aAngularBand m hm j u‖ =
      Real.sqrt (Real.pi * (K.right m - K.left m)) * ‖n07aCanonicalUnitMode hm u j‖ := by
  have hℓ : 0 < K.right m - K.left m := sub_pos.mpr hm
  have hs := n07aAngularBand_norm_sq_mode hm u hu j
  have he : ‖n07aAngularBand m hm j u‖ ^ 2 =
      (Real.sqrt (Real.pi * (K.right m - K.left m)) * ‖n07aCanonicalUnitMode hm u j‖) ^ 2 := by
    rw [hs, mul_pow, Real.sq_sqrt (mul_nonneg Real.pi_pos.le hℓ.le),
      n07aCanonicalUnitMode_norm_sq]
    rw [mul_assoc, ← mul_assoc (K.right m - K.left m), mul_inv_cancel₀ hℓ.ne', one_mul]
  nlinarith [norm_nonneg (n07aAngularBand m hm j u),
    mul_nonneg (Real.sqrt_nonneg (Real.pi * (K.right m - K.left m)))
      (norm_nonneg (n07aCanonicalUnitMode hm u j))]

variable {D : ReferenceData} {T : MaterialData}
  {C : NonlinearGeometryData S} {L : ReturnCorrectionData S}

theorem n07a_reference_actualMode_root_bound
    (hJ : ReferenceJets D T S C L K) (hP : ReferencePrincipal T S C K)
    (hE : ∀ m, 0 < T.E0 (T.sample (K.cell m)))
    (hlen : ∀ m, K.left m < K.right m) :
    ∃ A P Q : ℝ, 0 < A ∧ 0 < P ∧ 0 < Q ∧
      ∀ m, K.positive m = true → ∀ u ur urr G : CanonicalL2 S K m,
      N07aWeakCanonicalMixedDerivative S K m u ur 1 0 →
      N07aWeakCanonicalMixedDerivative S K m ur urr 1 0 →
      N07aCanonicalDistributionEquation S K m (K.coefficients (C.referenceState, 0) m) u G →
      ∀ j : ℕ,
        Real.sqrt (n07aScaledModeEnergy (K.right m - K.left m) (2 * (j : ℝ))
          (n07aCanonicalUnitMode (hlen m) u j) (n07aCanonicalUnitMode (hlen m) ur j)
          (n07aCanonicalUnitMode (hlen m) urr j)) ≤
        Real.sqrt (n07aReferenceModeBudget A P Q (K.right m - K.left m)
          (T.E0 (T.sample (K.cell m)))) * (‖u‖ + ‖G‖) := by
  obtain ⟨A, P, Q, hA, hPpos, hQ, hb⟩ := n07a_reference_actualMode_sum hJ hP hE hlen
  refine ⟨A, P, Q, hA, hPpos, hQ, ?_⟩
  intro m hm u ur urr G hr hrr heq j
  have h := hb m hm u ur urr G hr hrr heq
  have hj := h.1.le_tsum j (fun k _ => n07aCylinderEnergy_nonneg _ _ _ _)
  exact n07a_sqrt_energy_le
    (n07a_referenceModeBudget_nonneg A P Q _ (sub_pos.mpr (hlen m)))
    (norm_nonneg u) (norm_nonneg G) (hj.trans h.2)

end ContinuousFlexibility.Analysis
