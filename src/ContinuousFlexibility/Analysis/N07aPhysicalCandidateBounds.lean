import ContinuousFlexibility.Analysis.N07aPhysicalEquationTransfer
import ContinuousFlexibility.Analysis.N07aLinearPhysicalNorm
import ContinuousFlexibility.Analysis.N07aScalarSolution

/-!
# The actual physical candidate and its original one-high output grading

All material jets are integrable before the height decoder is used. The
height pair preserves the actual left scalar, and compatibility removes
the auxiliary scalar from the same equation.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter MeasureTheory ContinuousFlexibility.Statements
open scoped ContDiff

set_option backward.isDefEq.respectTransparency true

attribute [local instance]
  n07aNonlinearAnnularGroup n07aNonlinearAnnularModule
  n07aNonlinearAnnularAddGroup n07aNonlinearAnnularSMul n07aNonlinearAnnularSub
  n07aNonlinearAnnularParameterGroup n07aNonlinearAnnularParameterModule
  n07aNonlinearAnnularParameterAddGroup n07aNonlinearAnnularParameterSMul
  n07aNonlinearAnnularParameterSub
  n07aNonlinearDirectionsGroup n07aNonlinearDirectionsModule
  n07aNonlinearDirectionsAddGroup n07aNonlinearDirectionsSMul n07aNonlinearDirectionsSub
  n07aNonlinearSectorParameterGroup n07aNonlinearSectorParameterModule
  n07aNonlinearSectorParameterAddGroup n07aNonlinearSectorParameterSMul
  n07aNonlinearSectorParameterSub

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {R : ReturnEquationData S}
  {L : ReturnCorrectionData S} {K : CanonicalData S}
  {base geometryLoss : ℕ} {ε : ℝ}

theorem n07a_exists_actualHeightCandidateFamily
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T)
    (hS : IsPhysicalSpaces D T S)
    (h01 : N01Properties D T S C base geometryLoss ε)
    (h02 : N02Properties D T S C R base ε)
    (h03 : N03Properties D T S C R L base ε)
    (h04 : N04Properties D T S C L K base geometryLoss ε)
    (href : CanonicalGeometry.ReferenceJets D T S C L K)
    (Ω : Set (CanonicalGeometry.Parameter S))
    (hΩ : Ω ⊆ sectorNeighborhood S base ε ε)
    (U : CanonicalGeometry.Parameter S → S.Source → CanonicalUnknown S K)
    (v : CanonicalGeometry.Parameter S → S.Source → PolarPoint → ℝ)
    (hv : ∀ z ∈ Ω, ∀ f,
      ContDiffOn ℝ ∞ (v z f) (annularOpen D) ∧
      Function.Periodic (v z f) (0, Real.pi) ∧
      (∀ r θ, v z f (r, -θ) = v z f (r, θ)) ∧
      referenceRow D (v z f) = 0 ∧
      ∀ p ∈ annularOpen D,
        divergenceOperator (L.coefficients (liftSectorParameter S C z)) (v z f) p +
          (U z f).2.2.1 * nuColumnField D S C (liftSectorParameter S C z) p +
          (U z f).2.2.2 * (S.height (3 / 4 : ℝ)).decode S.psi p =
            (S.height (3 / 4 : ℝ)).decode f.val p)
    (N : CanonicalGeometry.Parameter S → S.Source)
    (hN : ∀ z ∈ Ω, ∀ p, (S.height (3 / 4 : ℝ)).decode (N z).val p =
      nuColumnField D S C (liftSectorParameter S C z) p)
    (low loss lowα : ℕ) (Aα : ℝ) (hAα : 0 ≤ Aα)
    (hα : ∀ z ∈ Ω, ∀ f, |(U z f).2.1| + |(U z f).2.2.1| ≤
      Aα * S.sourceGrading lowα f)
    (hr : N07aSampleLinearJetBounds T K (CanonicalGeometry.parameterGrading S)
      S.sourceGrading Ω (physicalPieceOpen S K)
      (fun c m => T.H (T.sample (K.cell m)) ^ (3 / 4 : ℝ) *
        (T.M (T.sample (K.cell m)) ^ c)⁻¹) low loss
      (fun z f _ => n07aPhysicalRemainder D S (U z f).2.1 (v z f))) :
    ∃ η : CanonicalGeometry.Parameter S → S.Source → HeightPair S,
      (∀ z ∈ Ω, ∀ f, N07aScalarSolution D S C L (liftSectorParameter S C z) f
        (η z f, (U z f).2.2.1)) ∧
      ∃ d low' : ℕ, ∀ s : ℕ, ∃ A : ℝ, 0 < A ∧ ∀ z ∈ Ω, ∀ f,
        n07aOutputGrading S s (η z f, (U z f).2.2.1) ≤ A *
          (S.sourceGrading (s + d) f +
            (1 + CanonicalGeometry.parameterGrading S (s + d) z) * S.sourceGrading low' f) := by
  classical
  let r := fun z f => n07aPhysicalRemainder D S (U z f).2.1 (v z f)
  have hp : Monotone (CanonicalGeometry.parameterGrading S) := n07aParameterGrading_monotone S
  have hq : Monotone S.sourceGrading := n07aSourceGrading_monotone S
  have hrs (z : CanonicalGeometry.Parameter S) (hz : z ∈ Ω) (f : S.Source) :
      ContDiffOn ℝ ∞ (r z f) (annularOpen D) := n07aPhysicalRemainder_smooth hS (hv z hz f).1
  have hjet := n07a_sampleLinearJets_weighted_memLp_bound hD hT h04 href
    (by norm_num : (0 : ℝ) ≤ 3 / 4) (by norm_num : (3 / 4 : ℝ) ≤ 1) hp hq hr hrs
  have hmem (z : CanonicalGeometry.Parameter S) (hz : z ∈ Ω) (f : S.Source) :
      HeightMember D T (3 / 4 : ℝ) (r z f) := by
    refine n07aPhysicalRemainder_heightMember hS (hv z hz f).1 (hv z hz f).2.1
      (hv z hz f).2.2.1 (fun i j k => ?_)
    exact (hjet i j k).choose_spec.2 z hz f |>.1
  let η : CanonicalGeometry.Parameter S → S.Source → HeightPair S :=
    fun z f => if hz : z ∈ Ω then n07aPhysicalHeightPair hS (U z f).2.1 (v z f) (hmem z hz f)
      else 0
  have hη (z : CanonicalGeometry.Parameter S) (hz : z ∈ Ω) (f : S.Source) :
      η z f = n07aPhysicalHeightPair hS (U z f).2.1 (v z f) (hmem z hz f) := by
    simp only [η, dif_pos hz]
  have heq (z : CanonicalGeometry.Parameter S) (hz : z ∈ Ω) (f : S.Source) :
      EqOn (heightPairField S (η z f)) (v z f) (annularOpen D) := by
    rw [hη z hz f]
    exact n07aPhysicalHeightPair_field hS _ _ (hmem z hz f)
  have heqPDE (z : CanonicalGeometry.Parameter S) (hz : z ∈ Ω) (f : S.Source) :
      ∀ p ∈ annularOpen D,
        divergenceOperator (L.coefficients (liftSectorParameter S C z)) (heightPairField S (η z f)) p +
          (U z f).2.2.1 * nuColumnField D S C (liftSectorParameter S C z) p +
          (U z f).2.2.2 * (S.height (3 / 4 : ℝ)).decode S.psi p =
            (S.height (3 / 4 : ℝ)).decode f.val p := by
    intro p hpD
    rw [n07a_divergenceOperator_field_eqOn (isOpen_Ioo.prod isOpen_univ)
      (heq z hz f) (L.coefficients (liftSectorParameter S C z)) hpD]
    exact (hv z hz f).2.2.2.2 p hpD
  refine ⟨η, fun z hz f => ?_, loss + 2, max low lowα, fun s => ?_⟩
  · have hAux := n07a_actualAuxiliaryScalar_zero hS hT h01 h02 h03 (hΩ hz)
      (N z) (hN z hz) (η z f) (U z f).2.2.1 (U z f).2.2.2 f (heqPDE z hz f)
    refine ⟨?_, fun p hpD => ?_⟩
    · rw [hη z hz f, n07aPhysicalHeightPair_row (K := K) hS hD.choose_spec.1.2.1.le
        (U z f).2.1 (v z f) (hv z hz f).2.1 (hmem z hz f)]
      exact (hv z hz f).2.2.2.1
    · simpa only [hAux, zero_mul, add_zero] using heqPDE z hz f p hpD
  · have bound := n07a_sampleLinearJets_physicalNorm_bound hD hT h04 href
      (by norm_num : (0 : ℝ) ≤ 3 / 4) (by norm_num : (3 / 4 : ℝ) ≤ 1) hp hq hr hrs s
    let A : ℝ := bound.choose
    have hA : 0 < A := bound.choose_spec.1
    have hAb := bound.choose_spec.2
    refine ⟨A + Aα, add_pos_of_pos_of_nonneg hA hAα, fun z hz f => ?_⟩
    let Q := S.sourceGrading (s + (loss + 2)) f +
      (1 + CanonicalGeometry.parameterGrading S (s + (loss + 2)) z) *
        S.sourceGrading (max low lowα) f
    have hnorm : physicalNorm T (3 / 4 : ℝ) s (r z f) ≤ A * Q :=
      (hAb z hz f).trans (mul_le_mul_of_nonneg_left
        (add_le_add le_rfl (mul_le_mul_of_nonneg_left (hq (le_max_left _ _) f)
          (add_nonneg zero_le_one (apply_nonneg _ _)))) hA.le)
    have hqQ : S.sourceGrading lowα f ≤ Q := by
      apply (hq (le_max_right _ _) f).trans
      dsimp only [Q]
      have hp0 := apply_nonneg (CanonicalGeometry.parameterGrading S (s + (loss + 2))) z
      have hq0 := apply_nonneg (S.sourceGrading (max low lowα)) f
      nlinarith only [apply_nonneg (S.sourceGrading (s + (loss + 2))) f, mul_nonneg hp0 hq0]
    have hsc := (hα z hz f).trans (mul_le_mul_of_nonneg_left hqQ hAα)
    have hout : n07aOutputGrading S s (η z f, (U z f).2.2.1) =
        physicalNorm T (3 / 4 : ℝ) s (r z f) +
          (|(U z f).2.1| + |(U z f).2.2.1|) := by
      rw [hη z hz f]
      dsimp only [r]
      simp only [n07aOutputGrading, pairGrading_apply, realGrading, coe_normSeminorm,
        Real.norm_eq_abs, n07aPhysicalHeightPair_grading]
      ring
    exact hout.le.trans ((add_le_add hnorm hsc).trans_eq (by ring))

end ContinuousFlexibility.Analysis
