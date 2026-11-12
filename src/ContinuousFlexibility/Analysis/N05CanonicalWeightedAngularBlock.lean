import ContinuousFlexibility.Analysis.N05CanonicalAngularBlockDecay
import ContinuousFlexibility.Analysis.N05CanonicalSampleBlockWeights

/-!
# The actual loss-four kernel for all canonical angular blocks

The original graph row is scaled by the actual source sample weight.
The same global inverse and its fixed weak jet then satisfy the two-endpoint
estimate. Fine logarithmic comparison gives the unchanged material powers
`t - 4` and `-t`, uniformly over the retained angular coordinates.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {R : ReturnEquationData S}
  {L : ReturnCorrectionData S} {K : CanonicalData S} {base loss : ℕ} {ε : ℝ}
  (hD : IsRadialReference D) (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
  (h : NonlinearPropertiesThrough04 D T S C R L K base loss ε)
  (hcoordinates : N05ControlledReferenceCoordinates D S C K)
  {β ρ γ δ M0 M1 : ℝ} (hminus : 0 < β - ρ) (hplus : 0 < β + ρ)
  (hγ : |γ - β| ≤ δ) {G : RadialSource → RadialUnknown}
  (hGminus : ReferenceInverseProperties D (β - ρ) M0 M1 G)
  (hGplus : ReferenceInverseProperties D (β + ρ) M0 M1 G)

include hD hT hS h hcoordinates hminus hplus hγ hGminus hGplus

theorem n05_canonicalAngularInverseBlock_weighted_bound (t : ℝ) :
    ∃ c : ℝ, ∀ s : ℕ, ∃ C0 : ℝ, 0 < C0 ∧
      ∀ k m (v : n05CanonicalClosedSubmodule S K s) (j : Fin (s + 1)),
      ‖(n05CanonicalSampleWeight T S K γ (t - 4) k)⁻¹ •
        n05CanonicalAngularJetSequence S K
          (n05CanonicalGlobalInverse D S C K G
            (Pi.single m (n05CanonicalSampleWeight T S K γ t m • v.val m 0))).1 j.val k‖ ≤
        C0 * n05ActualWeightKernel D T K.cell t c (ρ - δ) k m * ‖v.val m‖ := by
  obtain ⟨a, _, hblocks⟩ :=
    n05_canonicalAngularInverseBlock_inner_bound hD hT hS h hcoordinates hminus hplus hGminus hGplus
  obtain ⟨B, c, hB, hkernel⟩ :=
    n05_canonicalSampleWeight_kernel_bound hD.1 hT S K γ t a (ρ - δ)
  refine ⟨c, fun s => ?_⟩
  obtain ⟨Cb, hCb, hblock⟩ := hblocks s
  refine ⟨Cb * B, mul_pos hCb hB, fun k m v j => ?_⟩
  let wi := n05CanonicalSampleWeight T S K γ t m
  let wo := n05CanonicalSampleWeight T S K γ (t - 4) k
  let d := radialS (D.cellIndex (K.cell k)) - radialS (D.cellIndex (K.cell m))
  let q := radialQ (D.cellIndex (K.cell k)) + radialQ (D.cellIndex (K.cell m))
  let u := n05CanonicalAngularJetSequence S K
    (n05CanonicalGlobalInverse D S C K G (Pi.single m (wi • v.val m 0))).1 j.val k
  have hwi : 0 < wi := n05CanonicalSampleWeight_pos hT hD.1.choose_spec.2.1 S K γ t m
  have hwo : 0 < wo := n05CanonicalSampleWeight_pos hT hD.1.choose_spec.2.1 S K γ (t - 4) k
  have hzero : (wi • v).val m 0 = wi • v.val m 0 := rfl
  have hrow : (wi • v).val m = wi • v.val m := rfl
  have hb : Real.exp (γ * d) * ‖u‖ ≤
      Cb * Real.exp (a * q - (ρ - δ) * |d|) * (wi * ‖v.val m‖) := by
    simpa only [hzero, hrow, norm_smul, Real.norm_eq_abs, abs_of_pos hwi] using
      hblock γ δ hγ k m (wi • v) j
  have hc : Real.exp (-γ * d) * Real.exp (γ * d) = 1 := by
    rw [← Real.exp_add, show -γ * d + γ * d = 0 by ring, Real.exp_zero]
  have he : Real.exp (a * q - (ρ - δ) * |d| - γ * d) =
      Real.exp (-γ * d) * Real.exp (a * q - (ρ - δ) * |d|) := by
    rw [← Real.exp_add]
    congr 1
    ring
  change ‖wo⁻¹ • u‖ ≤ _
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hwo)]
  calc
    wo⁻¹ * ‖u‖ = wo⁻¹ * (Real.exp (-γ * d) * (Real.exp (γ * d) * ‖u‖)) := by
      rw [← mul_assoc (Real.exp (-γ * d)) (Real.exp (γ * d)) ‖u‖, hc, one_mul]
    _ ≤ wo⁻¹ * (Real.exp (-γ * d) *
        (Cb * Real.exp (a * q - (ρ - δ) * |d|) * (wi * ‖v.val m‖))) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hb (Real.exp_pos _).le)
        (inv_nonneg.mpr hwo.le)
    _ = Cb * (wo⁻¹ * wi * Real.exp (a * q - (ρ - δ) * |d| - γ * d)) * ‖v.val m‖ := by
      rw [he]
      ring
    _ ≤ Cb * (B * n05ActualWeightKernel D T K.cell t c (ρ - δ) k m) * ‖v.val m‖ :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (hkernel k m) hCb.le) (norm_nonneg _)
    _ = _ := by ring

end ContinuousFlexibility.Statements
