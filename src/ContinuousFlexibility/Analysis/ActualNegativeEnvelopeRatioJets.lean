module

public import ContinuousFlexibility.Analysis.MaterialEnvelopeRatioJets
public import ContinuousFlexibility.Analysis.ActualNegativeMaterialRatioJets

/-!
# Actual negative envelope ratios with the original atlas and samples

The scalar envelope may be explicitly enlarged, but its sample function
is required to be the same. The original actual atlas and its true optical
cut remain fixed throughout; only its already proved metadata is used.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set
open ContinuousFlexibility.Statements

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {R : ReturnEquationData S}
  {L : ReturnCorrectionData S} {base loss : ℕ} {ε : ℝ}
  (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
  (hN : NonlinearPropertiesThrough03 D T S C R L base loss ε)
  (hfield : N04bFieldRegularity D S C L base ε)
  (e : ℕ ≃ N04PieceIndex D)

/-- The denominator is the same actual stored sample, even when the
scalar envelope is supplied by an explicitly enlarged material datum. -/
theorem n04bActualTypedAtlas_negative_envelopeRatio_physical_jets
    (U : MaterialData) (hU : IsMaterialData D U) (hsample : U.sample = T.sample)
    (γ : ℝ) (n : ℕ) :
    let K := n04bActualTypedAtlas hT hS hN hfield e
    ∃ B A : ℝ, 0 ≤ B ∧ 0 ≤ A ∧ ∀ k m side, e k = .inl (m, side) → ∀ r,
      r ∈ Icc (C.left m) (C.right m) →
      |iteratedDeriv n (materialE0NormalizedPower U γ (U.sample (K.cell k))) r| ≤
        B * U.E0 (U.sample (K.cell k)) ^ A := by
  dsimp only
  let K := n04bActualTypedAtlas hT hS hN hfield e
  obtain ⟨A₀, hA₀, hdist⟩ :=
    n04bActualTypedAtlas_negative_sample_endpointX hT hS hN hfield e
  obtain ⟨B, A, hB, hA, hbound⟩ :=
    materialE0_normalized_physical_jets_of_bounded_X_shift hU hN.1.1.1.1 γ n hA₀
  refine ⟨B, A, hB, hA, ?_⟩
  intro k m side hk r hr
  have hgeometry := hN.1.1.2.2.2.1.1 m
  have hrcore : r ∈ Ioo D.a D.b :=
    ⟨hgeometry.1.trans_le hr.1, hr.2.trans_lt hgeometry.2.2⟩
  apply hbound r (U.sample (K.cell k)) hrcore
    (materialSample_mem_interval hN.1.1.1.1 hU (K.cell k))
  rw [hsample]
  simpa only [abs_sub_comm] using hdist k m side hk r hr

/-- Unit rescaling retains the original half and only pays a positive
power of its length, uniformly bounded by the physical annular width. -/
theorem n04bActualTypedAtlas_negative_envelopeRatio_unit_jets
    (U : MaterialData) (hU : IsMaterialData D U) (hsample : U.sample = T.sample)
    (γ : ℝ) (a : ℕ) :
    let K := n04bActualTypedAtlas hT hS hN hfield e
    ∃ B A : ℝ, 0 ≤ B ∧ 0 ≤ A ∧ ∀ k m side, e k = .inl (m, side) →
      ∀ p ∈ CanonicalGeometry.unitStrip, ∀ b : ℕ,
        |mixedDerivative a b (fun q => materialE0NormalizedPower U γ
          (U.sample (K.cell k)) (CanonicalGeometry.physicalUnitPoint K k q).1) p| ≤
            B * U.E0 (U.sample (K.cell k)) ^ A := by
  dsimp only
  let K := n04bActualTypedAtlas hT hS hN hfield e
  obtain ⟨B, A, hB, hA, hphysical⟩ :=
    n04bActualTypedAtlas_negative_envelopeRatio_physical_jets
      hT hS hN hfield e U hU hsample γ a
  refine ⟨|D.b - D.a| ^ a * B, A,
    mul_nonneg (pow_nonneg (abs_nonneg _) _) hB, hA, ?_⟩
  intro k m side hk p hp b
  let f := materialE0NormalizedPower U γ (U.sample (K.cell k))
  let d := K.physicalLeft k
  let c := K.physicalRight k - K.physicalLeft k
  change |mixedDerivative a b (fun q => f (d + c * q.1)) p| ≤ _
  rw [n08_mixedDerivative_radial (fun r => f (d + c * r))]
  have hEs : 0 < U.E0 (U.sample (K.cell k)) :=
    (hU.2.1 _ (materialSample_mem_interval hN.1.1.1.1 hU (K.cell k))).2.2.1
  by_cases hb : b = 0
  · rw [if_pos hb, n07a_iteratedDeriv_comp_affine, abs_mul, abs_pow]
    obtain ⟨hc, hwidth, hpoint⟩ :=
      n04bActualTypedAtlas_negative_physicalUnitPoint hT hS hN hfield e k m side hk
    have hwhole := (hpoint p hp).1
    have hpow : |c| ^ a ≤ |D.b - D.a| ^ a := by
      apply pow_le_pow_left₀ (abs_nonneg _)
      rw [abs_of_pos hc]
      exact hwidth.trans (le_abs_self _)
    have hvalue := hphysical k m side hk (d + c * p.1) ⟨hwhole.1.le, hwhole.2.le⟩
    calc
      _ ≤ |c| ^ a * (B * U.E0 (U.sample (K.cell k)) ^ A) :=
        mul_le_mul_of_nonneg_left hvalue (pow_nonneg (abs_nonneg _) _)
      _ ≤ |D.b - D.a| ^ a * (B * U.E0 (U.sample (K.cell k)) ^ A) :=
        mul_le_mul_of_nonneg_right hpow (mul_nonneg hB (Real.rpow_nonneg hEs.le _))
      _ = _ := by ring
  · rw [if_neg hb, abs_zero]
    exact mul_nonneg (mul_nonneg (pow_nonneg (abs_nonneg _) _) hB)
      (Real.rpow_nonneg hEs.le _)

end ContinuousFlexibility.Analysis
