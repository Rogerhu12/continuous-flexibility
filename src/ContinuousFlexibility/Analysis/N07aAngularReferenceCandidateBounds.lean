import ContinuousFlexibility.Analysis.N07aAngularReferenceLowJets
import ContinuousFlexibility.Analysis.N07aAngularReferenceIntegrable
import ContinuousFlexibility.Analysis.N07aAngularEndpointFlux

/-!
# The arbitrary current height pair supplies the reference graph bounds

All physical bounds used by the reference Green theorem are instantiated
from the original HeightPair and the primitive geometric jets. The first
derivative is bounded across interfaces by the already constructed C¹
representative, while the second derivatives are used on the open pieces.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter ContinuousFlexibility.Statements
open scoped Topology ContDiff

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {L : ReturnCorrectionData S} {K : CanonicalData S}
  {base loss : ℕ} {ε : ℝ}

theorem n07a_referenceCandidate_physical_bounds
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T)
    (hS : IsPhysicalSpaces D T S)
    (h01 : N01Properties D T S C base loss ε)
    (h04 : N04Properties D T S C L K base loss ε)
    (href : CanonicalGeometry.ReferenceJets D T S C L K)
    (hcur : CanonicalGeometry.CurrentJets D T S C L K base ε)
    (hRatio : N07aActualMaterialRatios T S C K base ε)
    (z : CanonicalGeometry.Parameter S) (hz : z ∈ sectorNeighborhood S base ε ε)
    (u : HeightPair S) {v : PolarPoint → ℝ}
    (hvc : ContDiffOn ℝ 1 v (annularOpen D))
    (hv : ∀ m, EqOn v
      (n07aReferencePieceHeight C K (liftSectorParameter S C z)
        (K.inverseChart (liftSectorParameter S C z)) u.2 (heightPairField S u) m)
      (referencePhysicalPieceOpen S K m))
    {γ : ℝ} (hγ : 0 < γ) (hγhi : γ < (3 / 4 : ℝ)) :
    ∃ A₀ A₁ B : ℝ, 0 ≤ A₀ ∧ 0 ≤ A₁ ∧ 0 ≤ B ∧
      (∀ p ∈ annularOpen D,
        |v p - u.2 * S.chiLeft p.1| ≤ A₁ * T.H p.1 ^ γ) ∧
      (∀ p ∈ annularOpen D,
        |n07aReferenceInteriorDifferential D K v p| ≤ A₀ * T.H p.1 ^ γ) ∧
      ∀ m p, p ∈ referencePhysicalPieceOpen S K m →
        |radialPartial v p| ≤ B ∧ |radialPartial (radialPartial v) p| ≤ B ∧
          |angularPartial (angularPartial v) p| ≤ B := by
  obtain ⟨A₁, hA₁, hrem⟩ := n07a_referenceRemainder_mixed_decay hD hT hS h01 h04
    href hcur hRatio z hz u.1 hγ.le hγhi 0 0
  have hH : ContinuousOn (fun p : PolarPoint => T.H p.1 ^ γ) (annularOpen D) :=
    (((hT.1 T.H (by simp)).continuousOn).comp continuous_fst.continuousOn
      (fun _ hp => hp.1)).rpow_const (fun _ _ => Or.inr hγ.le)
  have hremGlobal : ∀ p ∈ annularOpen D,
      |v p - u.2 * S.chiLeft p.1| ≤ A₁ * T.H p.1 ^ γ := by
    apply n07a_physicalPiece_bound h04
      (hvc.continuousOn.sub
        (continuous_const.mul (hS.2.2.1.1.continuous.comp continuous_fst)).continuousOn).abs
      (continuousOn_const.mul hH)
    intro m p hp
    simp only [Pi.sub_apply, Pi.mul_apply, Function.comp_apply]
    rw [hv m hp, n07aReferencePieceHeight_eq_remainder]
    simp only [add_sub_cancel_right]
    simpa only [spaces_mixedDerivative_zero] using hrem m p hp
  obtain ⟨C₁, hC₁, h₁⟩ := n07a_referenceTransport_positive_mixed_decay hD hT hS h01 h04
    href hcur hRatio z hz u hv hγ.le hγhi 1 0 (by decide)
  obtain ⟨C₂, hC₂, h₂⟩ := n07a_referenceTransport_positive_mixed_decay hD hT hS h01 h04
    href hcur hRatio z hz u hv hγ.le hγhi 2 0 (by decide)
  obtain ⟨C₃, hC₃, h₃⟩ := n07a_referenceTransport_positive_mixed_decay hD hT hS h01 h04
    href hcur hRatio z hz u hv hγ.le hγhi 0 2 (by decide)
  let C₀ : ℝ := C₁ + C₂ + C₃
  have hC₀ : 0 ≤ C₀ := add_nonneg (add_nonneg hC₁.le hC₂.le) hC₃.le
  have hweighted (m : ℕ) (p : PolarPoint) (hp : p ∈ referencePhysicalPieceOpen S K m) :
      |radialPartial v p| ≤ C₀ * T.H p.1 ^ γ ∧
        |radialPartial (radialPartial v) p| ≤ C₀ * T.H p.1 ^ γ ∧
        |angularPartial (angularPartial v) p| ≤ C₀ * T.H p.1 ^ γ := by
    have he := n07a_referencePartials_eq_mixed (isOpen_Ioo.prod isOpen_univ)
      (n07a_referenceTransport_piece_smooth hS h01 h04 z hz u hv m) hp
    have hpD := (h04.1.referenceBounds m).2.2 hp.1
    have hpH : 0 ≤ T.H p.1 ^ γ := (Real.rpow_pos_of_pos (hT.2.1 _ hpD).2.1 γ).le
    rw [he.1, he.2.1, he.2.2]
    refine ⟨(h₁ m p hp).trans ?_, (h₂ m p hp).trans ?_, (h₃ m p hp).trans ?_⟩ <;>
      exact mul_le_mul_of_nonneg_right (by dsimp only [C₀]; linarith) hpH
  obtain ⟨A, hA, hAb⟩ := n07a_referenceCoefficient_bound hD.choose_spec.1
  have hsource : ∀ p ∈ annularOpen D,
      |n07aReferenceInteriorDifferential D K v p| ≤ (A * C₀) * T.H p.1 ^ γ := by
    intro p hp
    have hH0 : 0 ≤ T.H p.1 ^ γ := (Real.rpow_pos_of_pos (hT.2.1 _ hp.1).2.1 γ).le
    by_cases hi : p ∈ n07aReferencePieceInterior K
    · obtain ⟨m, hm⟩ := mem_iUnion.mp hi
      obtain ⟨hr, hrr, htt⟩ := hweighted m p hm
      rw [n07aReferenceInteriorDifferential_on_piece v hm]
      exact (n07a_referenceDifferential_abs_le hr hrr htt).trans
        ((mul_le_mul_of_nonneg_right (hAb p.1 hp.1) (mul_nonneg hC₀ hH0)).trans_eq
          (by ring))
    · rw [n07aReferenceInteriorDifferential, indicator_of_notMem hi, abs_zero]
      exact mul_nonneg (mul_nonneg hA hC₀) hH0
  obtain ⟨H, hHpos, hHb⟩ := n07a_material_decay_uniform_bound hT hγ 0
  have hHu (r : ℝ) (hr : r ∈ radialCore D) : T.H r ^ γ ≤ H := by
    simpa only [Real.rpow_zero, mul_one] using hHb r hr
  refine ⟨A * C₀, A₁, C₀ * H, mul_nonneg hA hC₀, hA₁.le,
    mul_nonneg hC₀ hHpos.le, hremGlobal, hsource, ?_⟩
  intro m p hp
  have hb := mul_le_mul_of_nonneg_left (hHu p.1 ((h04.1.referenceBounds m).2.2 hp.1)) hC₀
  exact ⟨(hweighted m p hp).1.trans hb,
    (hweighted m p hp).2.1.trans hb, (hweighted m p hp).2.2.trans hb⟩

end ContinuousFlexibility.Analysis
