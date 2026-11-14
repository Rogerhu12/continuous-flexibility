module

public import ContinuousFlexibility.Analysis.N07aCanonicalUnitModes
public import ContinuousFlexibility.Analysis.N07aPositiveWeakMode

/-!
# Positive energy of the actual canonical modes

The source in the scalar energy estimate is constructed from the original
canonical right-hand side. Its potential term is an actual bounded L²
multiplier. All constants come from the primitive reference geometry.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter MeasureTheory ContinuousFlexibility.Statements CanonicalGeometry
open scoped ContDiff Topology

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {L : ReturnCorrectionData S} {K : CanonicalData S}

theorem n07a_reference_unitPotential_bound (hJ : ReferenceJets D T S C L K) :
    ∃ Q : ℝ, 0 < Q ∧ ∀ m x, x ∈ Ioo (0 : ℝ) 1 →
      |n07aReferenceUnitV D T S C L K m x| ≤
        (K.right m - K.left m) ^ 2 * (Q * T.E0 (T.sample (K.cell m)) ^ Q) := by
  obtain ⟨Q, hQ, hb⟩ := hJ.2 0
  refine ⟨Q, hQ, ?_⟩
  intro m x hx
  have h := hb m .potential (x, 0) ⟨hx, mem_univ _⟩ 0 0 (by omega)
  rw [spaces_mixedDerivative_zero] at h
  rw [n07aReferenceUnitV, abs_mul, abs_of_nonneg (sq_nonneg _)]
  exact mul_le_mul_of_nonneg_left h (sq_nonneg _)

/-- The true weak field and its true first radial derivative satisfy the
positive mode energy bound, with no assumed smooth solution or boundary trace. -/
theorem n07a_reference_canonical_unitMode_energy
    (hJ : ReferenceJets D T S C L K) (hP : ReferencePrincipal T S C K)
    (hE : ∀ m, 0 < T.E0 (T.sample (K.cell m)))
    (hlen : ∀ m, K.left m < K.right m) :
    ∃ A P Q : ℝ, 0 < A ∧ 0 < P ∧ 0 < Q ∧
      ∀ m, K.positive m = true → ∀ u d G : CanonicalL2 S K m,
      N07aWeakCanonicalMixedDerivative S K m u d 1 0 →
      N07aCanonicalDistributionEquation S K m (K.coefficients (C.referenceState, 0) m) u G →
      ∀ n : ℕ, ∃ dd : N07aIntervalL2,
        HasIntervalWeakDerivative 0 1
          (((K.right m - K.left m) • n07aCanonicalUnitMode (hlen m) d n : N07aIntervalL2) : ℝ → ℝ)
            dd ∧
        n07aCylinderEnergy (2 * (n : ℝ)) (n07aCanonicalUnitMode (hlen m) u n)
          ((K.right m - K.left m) • n07aCanonicalUnitMode (hlen m) d n) dd ≤
          16384 * (4 * (1 + A * T.E0 (T.sample (K.cell m)) ^ A +
            P * T.E0 (T.sample (K.cell m)) ^ P) ^ 5) ^ 10 *
            (((K.right m - K.left m) ^ 2 * (Q * T.E0 (T.sample (K.cell m)) ^ Q) *
              ‖n07aCanonicalUnitMode (hlen m) u n‖ +
              (K.right m - K.left m) ^ 2 * ‖n07aCanonicalUnitMode (hlen m) G n‖) ^ 2 +
                ‖n07aCanonicalUnitMode (hlen m) u n‖ ^ 2) := by
  obtain ⟨A, P, hA, hPpos, henergy⟩ := n07a_reference_positive_weak_mode hJ hP hE hlen
  obtain ⟨Q, hQ, hQbound⟩ := n07a_reference_unitPotential_bound hJ
  refine ⟨A, P, Q, hA, hPpos, hQ, ?_⟩
  intro m hm u d G hd heq n
  let ℓ := K.right m - K.left m
  let R := ℓ ^ 2 * (Q * T.E0 (T.sample (K.cell m)) ^ Q)
  let un := n07aCanonicalUnitMode (hlen m) u n
  let dn := ℓ • n07aCanonicalUnitMode (hlen m) d n
  let Gn := n07aCanonicalUnitMode (hlen m) G n
  let μ := volume.restrict (Ioo (0 : ℝ) 1)
  have hR : 0 ≤ R := mul_nonneg (sq_nonneg _) (mul_nonneg hQ.le (Real.rpow_nonneg (hE m).le _))
  have hVm : AEStronglyMeasurable (n07aReferenceUnitV D T S C L K m) μ :=
    (n07aReferenceUnit_scaled_contDiff hJ m).2.1.continuousOn.aestronglyMeasurable measurableSet_Ioo
  have hVb : ∀ᵐ x ∂μ, |n07aReferenceUnitV D T S C L K m x| ≤ R :=
    (ae_restrict_mem measurableSet_Ioo).mono (hQbound m)
  let MV := l2BoundedMultiplier μ hVm hVb
  let Fn : N07aIntervalL2 := MV un - ℓ ^ 2 • Gn
  have hFn : (Fn : ℝ → ℝ) =ᵐ[μ] fun x =>
      n07aReferenceUnitV D T S C L K m x * un x - ℓ ^ 2 * Gn x := by
    filter_upwards [Lp.coeFn_sub (MV un) (ℓ ^ 2 • Gn),
      l2BoundedMultiplier_ae μ hVm hVb un, Lp.coeFn_smul (ℓ ^ 2) Gn]
        with x hsub hmul hsmul
    rw [hsub, Pi.sub_apply, hmul, hsmul, Pi.smul_apply, smul_eq_mul]
  have hnorm : ‖Fn‖ ≤ R * ‖un‖ + ℓ ^ 2 * ‖Gn‖ := by
    calc
      ‖Fn‖ ≤ ‖MV un‖ + ‖ℓ ^ 2 • Gn‖ := norm_sub_le _ _
      _ ≤ R * ‖un‖ + ℓ ^ 2 * ‖Gn‖ := by
        rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
        exact add_le_add (((MV.le_opNorm un).trans
          (mul_le_mul_of_nonneg_right (norm_l2BoundedMultiplier_le μ hVm hR hVb)
            (norm_nonneg un)))) le_rfl
  have hmode : ∀ φ : ℝ → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ →
      tsupport φ ⊆ Ioo (0 : ℝ) 1 →
      (∫ x, un x * deriv (fun y => n07aReferenceUnitAtom D T S C L K m .principalA y *
        deriv φ y) x) = ∫ x, ((2 * (n : ℝ)) ^ 2 * n07aReferenceUnitC D T S C L K m x * un x +
          n07aReferenceUnitV D T S C L K m x * un x - Fn x) * φ x := by
    intro φ hφ hc hs
    have h := n07a_reference_canonical_unitMode_equation hJ hP (hlen m) heq n φ hφ hc hs
    apply h.trans
    apply n07a_interval_compact_pairing_congr _ hs
    filter_upwards [hFn] with x hx
    rw [hx]
    ring
  have hdn : HasIntervalWeakDerivative 0 1 un dn := by
    apply n07a_intervalWeakDerivative_congr (EventuallyEq.refl _ _)
      (Lp.coeFn_smul ℓ (n07aCanonicalUnitMode (hlen m) d n)).symm
    exact n07aCanonicalUnitMode_firstNormal (hlen m) hd n
  obtain ⟨dd, hdd, hb⟩ := henergy m hm (2 * (n : ℝ)) un dn Fn hdn hmode
  refine ⟨dd, hdd, hb.trans ?_⟩
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  exact add_le_add ((sq_le_sq₀ (norm_nonneg Fn)
    (add_nonneg (mul_nonneg hR (norm_nonneg un)) (mul_nonneg (sq_nonneg ℓ) (norm_nonneg Gn)))).2 hnorm)
    le_rfl

end ContinuousFlexibility.Analysis
