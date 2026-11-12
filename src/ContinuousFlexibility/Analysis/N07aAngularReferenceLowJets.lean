import ContinuousFlexibility.Analysis.N07aAngularReferenceJetEnvelopes
import ContinuousFlexibility.Analysis.N07aAngularSampleHeightDecay
import ContinuousFlexibility.Analysis.N07aCanonicalGreenPairing
import ContinuousFlexibility.Analysis.N07aCompositionBudget
import ContinuousFlexibility.Scalar.WeightedCutoffDerivative

/-!
# Genuine low physical jets of an arbitrary transported height pair

The remainder retains a strict positive height gain. Every positive
derivative of the prescribed cutoff is handled by its already constructed
weighted height vector. The bounds below are therefore conclusions for
the actual candidate, not regularity assumptions on a reference solution.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter ContinuousFlexibility.Statements
open scoped Topology ContDiff

theorem n07a_referencePartials_eq_mixed
    {U : Set PolarPoint} (hU : IsOpen U) {v : PolarPoint → ℝ}
    (hv : ContDiffOn ℝ ∞ v U) {p : PolarPoint} (hp : p ∈ U) :
    radialPartial v p = mixedDerivative 1 0 v p ∧
      radialPartial (radialPartial v) p = mixedDerivative 2 0 v p ∧
      angularPartial (angularPartial v) p = mixedDerivative 0 2 v p := by
  have hr (q : PolarPoint) (hq : q ∈ U) : radialPartial v q = mixedDerivative 1 0 v q := by
    simpa only [spaces_mixedDerivative_zero, zero_add] using
      n07a_radialPartial_mixedDerivative_on hU hv 0 0 hq
  have ht (q : PolarPoint) (hq : q ∈ U) : angularPartial v q = mixedDerivative 0 1 v q := by
    simpa only [spaces_mixedDerivative_zero, zero_add] using
      n07a_angularPartial_zero_mixedDerivative_on hU hv 0 hq
  have her : radialPartial v =ᶠ[𝓝 p] mixedDerivative 1 0 v := by
    filter_upwards [hU.mem_nhds hp] with q hq
    exact hr q hq
  have het : angularPartial v =ᶠ[𝓝 p] mixedDerivative 0 1 v := by
    filter_upwards [hU.mem_nhds hp] with q hq
    exact ht q hq
  refine ⟨hr p hp, ?_, ?_⟩
  · exact (congrArg (fun A : PolarPoint →L[ℝ] ℝ => A (1, 0))
      (her.fderiv_eq (𝕜 := ℝ))).trans
        (n07a_radialPartial_mixedDerivative_on hU hv 1 0 hp)
  · exact (congrArg (fun A : PolarPoint →L[ℝ] ℝ => A (0, 1))
      (het.fderiv_eq (𝕜 := ℝ))).trans
        (n07a_angularPartial_zero_mixedDerivative_on hU hv 1 hp)

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {L : ReturnCorrectionData S} {K : CanonicalData S}
  {base loss : ℕ} {ε : ℝ}

theorem n07a_cutoff_positive_mixed_decay
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (γ aL : ℝ) (a b : ℕ) (hpos : 0 < a + b) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ p ∈ annularOpen D,
      |mixedDerivative a b (fun q : PolarPoint => aL * S.chiLeft q.1) p| ≤
        B * T.H p.1 ^ γ := by
  cases b with
  | succ b =>
    refine ⟨0, le_rfl, fun p _ => ?_⟩
    simp only [spaces_mixedDerivative_const_mul, mixedDerivative, iteratedDeriv_const,
      Nat.succ_ne_zero, ite_false, ite_self, mul_zero, zero_mul, abs_zero, le_refl]
  | zero =>
    cases a with
    | zero => omega
    | succ a =>
      let u := scalarCutoffDerivativeHeight hT hS γ
      obtain ⟨B, hB, hBb⟩ := n07a_mixedDerivative_decode_decay hT (hS.1 γ) a 0 0
      let A : ℝ := |aL| * B * (S.height γ).grading (a + 3) u
      have hA : 0 ≤ A := mul_nonneg (mul_nonneg (abs_nonneg _) hB) (apply_nonneg _ _)
      refine ⟨A, hA, fun p hp => ?_⟩
      have h := hBb u p hp
      rw [decode_scalarCutoffDerivativeHeight] at h
      simp only [mixedDerivative, iteratedDeriv_zero, Nat.add_zero, pow_zero,
        inv_one, mul_one] at h
      rw [spaces_mixedDerivative_const_mul, abs_mul]
      simp only [mixedDerivative, iteratedDeriv_zero, iteratedDeriv_succ']
      exact (mul_le_mul_of_nonneg_left h (abs_nonneg aL)).trans_eq (by dsimp only [A]; ring)

theorem n07a_referenceRemainder_mixed_decay
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T)
    (hS : IsPhysicalSpaces D T S)
    (h01 : N01Properties D T S C base loss ε)
    (h04 : N04Properties D T S C L K base loss ε)
    (href : CanonicalGeometry.ReferenceJets D T S C L K)
    (hcur : CanonicalGeometry.CurrentJets D T S C L K base ε)
    (hRatio : N07aActualMaterialRatios T S C K base ε)
    (z : CanonicalGeometry.Parameter S) (hz : z ∈ sectorNeighborhood S base ε ε)
    (u : (S.height (3 / 4 : ℝ)).Space)
    {γ : ℝ} (hγ : 0 ≤ γ) (hγhi : γ < (3 / 4 : ℝ)) (a b : ℕ) :
    ∃ B : ℝ, 0 < B ∧ ∀ m p, p ∈ referencePhysicalPieceOpen S K m →
      |mixedDerivative a b (n07aReferenceRemainderField C K
        (liftSectorParameter S C z) ((S.height (3 / 4 : ℝ)).decode u) m) p| ≤
        B * T.H p.1 ^ γ := by
  have henv : N07aAngularFixedJetEnvelope T K (referencePhysicalPieceOpen S K)
      (fun m => T.H (T.sample (K.cell m)) ^ (3 / 4 : ℝ))
      (n07aReferenceRemainderField C K (liftSectorParameter S C z)
        ((S.height (3 / 4 : ℝ)).decode u)) := by
    simpa only [pow_zero, inv_one, mul_one] using
      n07a_referenceRemainder_fixedJetEnvelope hD hT hS h01 h04 href hcur hRatio z hz u 0
  obtain ⟨B, hB, hBb⟩ := henv.physical_height_decay hD hT href
    (fun m => (h04.1.referenceBounds m).1) (fun m => (h04.1.referenceBounds m).2.2)
    hγ (by linarith) hγhi (a + b)
  refine ⟨B, hB, fun m p hp => ?_⟩
  have hs := n07aReferenceRemainderField_contDiffOn hS h01 h04
    (liftSectorParameter_mem_stateNeighborhood (C := C) hz le_rfl)
    (h01.2.2.1.liftSectorParameter_sector z) ((hS.1 (3 / 4 : ℝ)).2.2.2.1 u).1 m
  exact (n07a_mixedDerivative_norm_le_iteratedFDeriv (isOpen_Ioo.prod isOpen_univ)
    hs a b hp).trans (hBb m p hp)

theorem n07a_referenceTransport_piece_smooth
    (hS : IsPhysicalSpaces D T S)
    (h01 : N01Properties D T S C base loss ε)
    (h04 : N04Properties D T S C L K base loss ε)
    (z : CanonicalGeometry.Parameter S) (hz : z ∈ sectorNeighborhood S base ε ε)
    (u : HeightPair S) {v : PolarPoint → ℝ}
    (hv : ∀ m, EqOn v
      (n07aReferencePieceHeight C K (liftSectorParameter S C z)
        (K.inverseChart (liftSectorParameter S C z)) u.2 (heightPairField S u) m)
      (referencePhysicalPieceOpen S K m)) (m : ℕ) :
    ContDiffOn ℝ ∞ v (referencePhysicalPieceOpen S K m) := by
  have hη : ContDiffOn ℝ ∞ (heightPairField S u) (annularOpen D) :=
    ((hS.1 (3 / 4 : ℝ)).2.2.2.1 u.1).1.add
      (contDiff_const.mul (hS.2.2.1.1.comp contDiff_fst)).contDiffOn
  exact (n07aReferencePieceHeight_contDiffOn hS h01 h04
    (liftSectorParameter_mem_stateNeighborhood (C := C) hz le_rfl)
    (h01.2.2.1.liftSectorParameter_sector z) (fun _ _ _ => rfl) u.2 hη m).congr (hv m)

theorem n07a_referenceTransport_positive_mixed_decay
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T)
    (hS : IsPhysicalSpaces D T S)
    (h01 : N01Properties D T S C base loss ε)
    (h04 : N04Properties D T S C L K base loss ε)
    (href : CanonicalGeometry.ReferenceJets D T S C L K)
    (hcur : CanonicalGeometry.CurrentJets D T S C L K base ε)
    (hRatio : N07aActualMaterialRatios T S C K base ε)
    (z : CanonicalGeometry.Parameter S) (hz : z ∈ sectorNeighborhood S base ε ε)
    (u : HeightPair S) {v : PolarPoint → ℝ}
    (hv : ∀ m, EqOn v
      (n07aReferencePieceHeight C K (liftSectorParameter S C z)
        (K.inverseChart (liftSectorParameter S C z)) u.2 (heightPairField S u) m)
      (referencePhysicalPieceOpen S K m))
    {γ : ℝ} (hγ : 0 ≤ γ) (hγhi : γ < (3 / 4 : ℝ)) (a b : ℕ) (hpos : 0 < a + b) :
    ∃ B : ℝ, 0 < B ∧ ∀ m p, p ∈ referencePhysicalPieceOpen S K m →
      |mixedDerivative a b v p| ≤ B * T.H p.1 ^ γ := by
  obtain ⟨A, hA, hAb⟩ := n07a_referenceRemainder_mixed_decay hD hT hS h01 h04
    href hcur hRatio z hz u.1 hγ hγhi a b
  obtain ⟨B, hB, hBb⟩ := n07a_cutoff_positive_mixed_decay hT hS γ u.2 a b hpos
  refine ⟨A + B, add_pos_of_pos_of_nonneg hA hB, fun m p hp => ?_⟩
  let R := n07aReferenceRemainderField C K (liftSectorParameter S C z)
    ((S.height (3 / 4 : ℝ)).decode u.1) m
  have hEq : EqOn v (fun q => R q + u.2 * S.chiLeft q.1) (referencePhysicalPieceOpen S K m) := by
    intro q hq
    exact (hv m hq).trans (congrFun (n07aReferencePieceHeight_eq_remainder
      C K (liftSectorParameter S C z) u m) q)
  have hRs := n07aReferenceRemainderField_contDiffOn hS h01 h04
    (liftSectorParameter_mem_stateNeighborhood (C := C) hz le_rfl)
    (h01.2.2.1.liftSectorParameter_sector z) ((hS.1 (3 / 4 : ℝ)).2.2.2.1 u.1).1 m
  have hχs : ContDiffOn ℝ ∞ (fun q : PolarPoint => u.2 * S.chiLeft q.1)
      (referencePhysicalPieceOpen S K m) :=
    (contDiff_const.mul (hS.2.2.1.1.comp contDiff_fst)).contDiffOn
  rw [n07a_mixedDerivative_eqOn (isOpen_Ioo.prod isOpen_univ) hEq a b hp,
    n07a_mixedDerivative_add_on (isOpen_Ioo.prod isOpen_univ) hRs hχs a b hp]
  exact (abs_add_le _ _).trans ((add_le_add (hAb m p hp)
    (hBb p ⟨(h04.1.referenceBounds m).2.2 hp.1, mem_univ _⟩)).trans_eq (by ring))

end ContinuousFlexibility.Analysis
