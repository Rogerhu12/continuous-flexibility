module

public import ContinuousFlexibility.Analysis.N07aReferenceOpenCoefficients
public import ContinuousFlexibility.Analysis.N07aModeBudgetMaterial

/-!
# The actual source in the reference mode equation

The original potential and all three original scalar columns are kept in
the source.  Its norm is controlled by the genuine field, source and
column classes; no homogeneous reference equation is substituted for it.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter MeasureTheory ContinuousFlexibility.Statements CanonicalGeometry

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {L : ReturnCorrectionData S} {K : CanonicalData S}

theorem n07a_referencePotential_bound (hJ : ReferenceJets D T S C L K) :
    ∃ A : ℝ, 0 < A ∧ ∀ m (hm : K.left m < K.right m), ∀ p ∈ canonicalOpen S K m,
      |(N07aCanonicalOpenCoefficient.constMul
        (if K.positive m then -1 else (1 : ℝ))
        (n07aReferenceOpenCoefficient hJ m hm 4)).value p| ≤
          A * T.E0 (T.sample (K.cell m)) ^ A := by
  obtain ⟨A, hA, hb⟩ := hJ.2 0
  refine ⟨A, hA, fun m hm p hp => ?_⟩
  have h := hb m .potential (n07aCanonicalUnitInversePoint K m p)
    (n07aCanonicalUnitInversePoint_maps hm hp) 0 0 (by omega)
  rw [spaces_mixedDerivative_zero] at h
  change |K.potential (C.referenceState, 0) m
    (canonicalUnitPoint K m (n07aCanonicalUnitInversePoint K m p))| ≤ _ at h
  rw [n07aCanonicalUnitPoint_inverse hm] at h
  change |(if K.positive m then -1 else (1 : ℝ)) * K.potential (C.referenceState, 0) m p| ≤ _
  have hs : |if K.positive m then (-1 : ℝ) else 1| = 1 := by
    cases K.positive m <;> norm_num
  rwa [abs_mul, hs, one_mul]

theorem n07a_referencePotential_mul_norm (hJ : ReferenceJets D T S C L K) :
    ∃ A : ℝ, 0 < A ∧ ∀ m (hm : K.left m < K.right m) (u : CanonicalL2 S K m),
      ‖(N07aCanonicalOpenCoefficient.constMul
        (if K.positive m then -1 else (1 : ℝ))
        (n07aReferenceOpenCoefficient hJ m hm 4)).mul u‖ ≤
          A * T.E0 (T.sample (K.cell m)) ^ A * ‖u‖ := by
  obtain ⟨A, hA, hb⟩ := n07a_referencePotential_bound hJ
  refine ⟨A, hA, fun m hm u => ?_⟩
  let q := N07aCanonicalOpenCoefficient.constMul
    (if K.positive m then -1 else (1 : ℝ)) (n07aReferenceOpenCoefficient hJ m hm 4)
  apply Lp.norm_le_mul_norm_of_ae_le_mul
  filter_upwards [q.mul_ae u, n07a_canonicalOpen_ae (S := S) (K := K) (m := m)] with p hq hp
  change ‖q.mul u p‖ ≤ _
  rw [hq, Real.norm_eq_abs, Real.norm_eq_abs, abs_mul]
  exact mul_le_mul_of_nonneg_right (hb m hm p hp) (abs_nonneg _)

theorem n07aReferenceCanonicalRhs_norm
    (hJ : ReferenceJets D T S C L K) (m : ℕ) (hm : K.left m < K.right m)
    (U : CanonicalUnknown S K) (F : CanonicalSequence S K) {A : ℝ}
    (hq : ‖(N07aCanonicalOpenCoefficient.constMul
      (if K.positive m then -1 else (1 : ℝ))
      (n07aReferenceOpenCoefficient hJ m hm 4)).mul (U.1 m)‖ ≤ A * ‖U.1 m‖) :
    ‖n07aReferenceCanonicalRhs hJ m hm U F‖ ≤
      ‖F m‖ + A * ‖U.1 m‖ +
        |U.2.1| * ‖(n07aReferenceScalarOpenCoefficient hJ m hm 0).toLp‖ +
        |U.2.2.1| * ‖(n07aReferenceScalarOpenCoefficient hJ m hm 1).toLp‖ +
        |U.2.2.2| * ‖(n07aReferenceScalarOpenCoefficient hJ m hm 2).toLp‖ := by
  let qU : CanonicalL2 S K m :=
    (N07aCanonicalOpenCoefficient.constMul
      (if K.positive m then -1 else (1 : ℝ))
      (n07aReferenceOpenCoefficient hJ m hm 4)).mul (U.1 m)
  let c₀ : CanonicalL2 S K m :=
    U.2.1 • (n07aReferenceScalarOpenCoefficient hJ m hm 0).toLp
  let c₁ : CanonicalL2 S K m :=
    U.2.2.1 • (n07aReferenceScalarOpenCoefficient hJ m hm 1).toLp
  let c₂ : CanonicalL2 S K m :=
    U.2.2.2 • (n07aReferenceScalarOpenCoefficient hJ m hm 2).toLp
  have hq' : ‖qU‖ ≤ A * ‖U.1 m‖ := hq
  have h₀ := norm_sub_le (F m) qU
  have h₁ := norm_sub_le (F m - qU) c₀
  have h₂ := norm_sub_le (F m - qU - c₀) c₁
  have h₃ := norm_sub_le (F m - qU - c₀ - c₁) c₂
  have hbound : ‖F m - qU - c₀ - c₁ - c₂‖ ≤
      ‖F m‖ + A * ‖U.1 m‖ + ‖c₀‖ + ‖c₁‖ + ‖c₂‖ := by
    linarith only [h₀, h₁, h₂, h₃, hq']
  simpa only [qU, c₀, c₁, c₂, n07aReferenceCanonicalRhs,
    norm_smul, Real.norm_eq_abs] using hbound

end ContinuousFlexibility.Analysis
