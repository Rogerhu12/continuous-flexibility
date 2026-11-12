import ContinuousFlexibility.Analysis.N07aCanonicalUnitEnergy
import ContinuousFlexibility.Analysis.N07aIntervalWeakUnique

/-!
# Positive mode energy for the already existing second derivative

Uniqueness in the interval L² quotient identifies the derivative produced
by the energy proof with the affine normalization of the original second
normal derivative. Thus the estimate controls that same canonical field.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set MeasureTheory ContinuousFlexibility.Statements CanonicalGeometry

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {L : ReturnCorrectionData S} {K : CanonicalData S}

theorem n07a_reference_actualMode_energy
    (hJ : ReferenceJets D T S C L K) (hP : ReferencePrincipal T S C K)
    (hE : ∀ m, 0 < T.E0 (T.sample (K.cell m)))
    (hlen : ∀ m, K.left m < K.right m) :
    ∃ A P Q : ℝ, 0 < A ∧ 0 < P ∧ 0 < Q ∧
      ∀ m, K.positive m = true → ∀ u ur urr G : CanonicalL2 S K m,
      N07aWeakCanonicalMixedDerivative S K m u ur 1 0 →
      N07aWeakCanonicalMixedDerivative S K m ur urr 1 0 →
      N07aCanonicalDistributionEquation S K m (K.coefficients (C.referenceState, 0) m) u G →
      ∀ n : ℕ,
        n07aCylinderEnergy (2 * (n : ℝ)) (n07aCanonicalUnitMode (hlen m) u n)
          ((K.right m - K.left m) • n07aCanonicalUnitMode (hlen m) ur n)
          ((K.right m - K.left m) ^ 2 • n07aCanonicalUnitMode (hlen m) urr n) ≤
          16384 * (4 * (1 + A * T.E0 (T.sample (K.cell m)) ^ A +
            P * T.E0 (T.sample (K.cell m)) ^ P) ^ 5) ^ 10 *
            (((K.right m - K.left m) ^ 2 * (Q * T.E0 (T.sample (K.cell m)) ^ Q) *
              ‖n07aCanonicalUnitMode (hlen m) u n‖ +
              (K.right m - K.left m) ^ 2 * ‖n07aCanonicalUnitMode (hlen m) G n‖) ^ 2 +
                ‖n07aCanonicalUnitMode (hlen m) u n‖ ^ 2) := by
  obtain ⟨A, P, Q, hA, hPpos, hQ, hb⟩ := n07a_reference_canonical_unitMode_energy hJ hP hE hlen
  refine ⟨A, P, Q, hA, hPpos, hQ, ?_⟩
  intro m hm u ur urr G hr hrr heq n
  obtain ⟨dd, hd, hbound⟩ := hb m hm u ur G hr heq n
  have he : dd = (K.right m - K.left m) ^ 2 • n07aCanonicalUnitMode (hlen m) urr n :=
    n07a_intervalWeakDerivative_unique hd (n07aCanonicalUnitMode_secondNormal_class (hlen m) hrr n)
  exact he ▸ hbound

/-- A numerical square bound keeps the same source and unknown norms in
the summation, with a coefficient independent of the angular frequency. -/
theorem n07a_mode_source_square_le (R ℓ x y : ℝ) :
    (R * x + ℓ ^ 2 * y) ^ 2 + x ^ 2 ≤
      2 * (1 + R ^ 2 + ℓ ^ 4) * (x ^ 2 + y ^ 2) := by
  nlinarith [sq_nonneg (R * x - ℓ ^ 2 * y),
    mul_nonneg (sq_nonneg R) (sq_nonneg y),
    mul_nonneg (sq_nonneg (ℓ ^ 2)) (sq_nonneg x), sq_nonneg x, sq_nonneg y]

end ContinuousFlexibility.Analysis
