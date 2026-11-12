import ContinuousFlexibility.Analysis.RetainedReferenceOpticalEnvelope
import ContinuousFlexibility.Analysis.MaterialEnvelopeNormalization

/-!
# The actual retained optical bound in a normalized material weight

This is a construction-stage statement. It explicitly returns the
normalized material data on the same retained reference. It neither
changes existing physical spaces nor transports an existing Through03
certificate to new material data. The normalization permits the genuine
inverse coefficient estimate to be written with one constant and one
matching exponent, as required by the primitive geometry certificate.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open Set
open ContinuousFlexibility.Statements ContinuousFlexibility.Analysis

/-- The proved material normalization and the actual retained optical
estimate give the uniform simple-root lower bound. Host membership is
kept as physical inclusion in the same reference's real cells. -/
theorem retainedReference_normalized_optical_lower
    {S : SelectedTailData} {K : SeedCentralCutoff} {q length : ℝ}
    (P : SeedRetainedPair S K q length) (hS : IsSelectedTail S)
    (hstart : 100 ≤ S.chain.index)
    (hband : radialFrequencyBand S.chain S.Cstar S.chain.index 2) (hq : 0 < q)
    {Γ : ConnectedReferenceGeometry} (hΓ : Γ.Realizes)
    (hw : Γ.reference.w = P.pair.profile)
    (hcoordinates : R11aRetainedCoordinates P Γ)
    {T : MaterialData} (hT : IsMaterialData Γ.reference T) :
    IsMaterialData Γ.reference (enlargedMaterialData T) ∧
      (∀ r ∈ Ioo Γ.reference.a Γ.reference.b, 1 ≤ (enlargedMaterialData T).E0 r) ∧
      ∃ B : ℝ, 0 < B ∧ ∀ l h : ℝ, ∀ j : ℕ,
        NegativeRadialComponent Γ.reference l h → Ioo l h ⊆ Γ.reference.cells j →
        ∀ r ∈ Ioo l h,
          B⁻¹ * (enlargedMaterialData T).E0 ((enlargedMaterialData T).sample j) ^ (-B) *
              min (r - l) (h - r) ≤
            -deriv Γ.reference.w r / (r * Γ.reference.w r) := by
  have hT' : IsMaterialData Γ.reference (enlargedMaterialData T) :=
    isMaterialData_enlargedMaterialData hΓ.2.1 hT
  have hnorm : ∀ r ∈ Ioo Γ.reference.a Γ.reference.b,
      1 ≤ (enlargedMaterialData T).E0 r := fun _ hr => one_le_enlargedMaterialData_E0 hT hr
  obtain ⟨C, A, hC, hA, hbound⟩ := retainedReference_uniform_optical_envelope
    P hS hstart hband hq hΓ hw hcoordinates hT'
  obtain ⟨B, hB, hpack⟩ := coefficientEnvelope_pack C A
  refine ⟨hT', hnorm, B, hB, ?_⟩
  intro l h j hcomponent hhost r hr
  obtain ⟨κ, hκ, hκbound, hlower⟩ := hbound l h j hcomponent hhost
  let W := (enlargedMaterialData T).E0 ((enlargedMaterialData T).sample j)
  have hW : 1 ≤ W := hnorm _ (materialSample_mem_interval hΓ.2.1 hT' j)
  have hWpos : 0 < W := zero_lt_one.trans_le hW
  have hinv : κ⁻¹ ≤ B * W ^ B := hκbound.trans (hpack W hW)
  have hsmall : B⁻¹ * W ^ (-B) ≤ κ := by
    have h := (inv_le_comm₀ hκ (mul_pos hB (Real.rpow_pos_of_pos hWpos B))).mp hinv
    simpa only [Real.rpow_neg hWpos.le, mul_inv_rev, mul_comm] using h
  exact (mul_le_mul_of_nonneg_right hsmall
    (le_min (sub_nonneg.mpr hr.1.le) (sub_nonneg.mpr hr.2.le))).trans (hlower r hr)

end ContinuousFlexibility.Radial
