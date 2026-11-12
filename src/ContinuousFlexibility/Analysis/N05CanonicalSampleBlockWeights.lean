import ContinuousFlexibility.Analysis.N05CanonicalBlockDecay
import ContinuousFlexibility.Analysis.N05ActualWeightKernel

/-!
# Actual sample weights on the canonical inverse blocks

The fine logarithmic comparison for the actual endpoint weight contributes
only powers of the coefficient envelope. The material powers remain exactly
`t - 4` and `-t`; neither endpoint conversion spends an extra material order.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open Set

/-- Conjugating by the actual sample weights gives the genuine loss-four
kernel, with only its coefficient exponent enlarged by the endpoint error. -/
theorem n05_canonicalSampleWeight_kernel_bound
    {D : ReferenceData} {T : MaterialData} (hD : IsAccumulatingProfile D)
    (hT : IsMaterialData D T) (S : PhysicalSpacesData) (K : CanonicalData S)
    (γ t a η : ℝ) :
    ∃ B c : ℝ, 0 < B ∧ ∀ k m,
      (n05CanonicalSampleWeight T S K γ (t - 4) k)⁻¹ *
        n05CanonicalSampleWeight T S K γ t m *
        Real.exp (a * (radialQ (D.cellIndex (K.cell k)) +
            radialQ (D.cellIndex (K.cell m))) -
          η * |radialS (D.cellIndex (K.cell k)) - radialS (D.cellIndex (K.cell m))| -
          γ * (radialS (D.cellIndex (K.cell k)) - radialS (D.cellIndex (K.cell m)))) ≤
      B * n05ActualWeightKernel D T K.cell t c η k m := by
  obtain ⟨H, hH, hlog⟩ := n05_material_reference_logH_bound hD hT
  have hdata := hT
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hsample, _, _⟩ := hdata
  let Q (j : ℕ) := radialQ (D.cellIndex (K.cell j))
  let S0 (j : ℕ) := radialS (D.cellIndex (K.cell j))
  let H0 (j : ℕ) := T.H (T.sample (K.cell j))
  let M (j : ℕ) := T.M (T.sample (K.cell j))
  let A : ℝ := |γ| * H
  have hH0 (j : ℕ) : 0 < H0 j :=
    (hT.2.1 _ (materialSample_mem_radialCore hT hD.choose_spec.2.1 (K.cell j))).2.1
  have hM (j : ℕ) : 0 < M j := zero_lt_one.trans_le
    (hT.2.1 _ (materialSample_mem_radialCore hT hD.choose_spec.2.1 (K.cell j))).2.2.2
  have herr (j : ℕ) : |γ * (Real.log (H0 j) + S0 j)| ≤ A * (Q j + 1) := by
    rw [abs_mul]
    have he := mul_le_mul_of_nonneg_left (hlog (K.cell j) _ (hsample _)) (abs_nonneg γ)
    simpa only [A, Q, S0, H0, mul_assoc] using he
  have hweight (j : ℕ) : radialE (D.cellIndex (K.cell j)) ^ (a + A) =
      Real.exp ((a + A) * Q j) := by
    rw [radialE, ← Real.exp_mul]
    congr 1
    exact mul_comm _ _
  refine ⟨Real.exp (2 * A), a + A, Real.exp_pos _, fun k m => ?_⟩
  have hinv : (n05CanonicalSampleWeight T S K γ (t - 4) k)⁻¹ =
      M k ^ (t - 4) * H0 k ^ (-γ) := by
    change (M k ^ (-(t - 4)) * H0 k ^ γ)⁻¹ = _
    rw [mul_inv_rev, ← Real.rpow_neg (hH0 k).le γ,
      ← Real.rpow_neg (hM k).le (-(t - 4)), neg_neg]
    ring
  have hu : Real.log (H0 k) * (-γ) + Real.log (H0 m) * γ +
      (a * (Q k + Q m) - η * |S0 k - S0 m| - γ * (S0 k - S0 m)) ≤
      2 * A + (a + A) * Q k + (a + A) * Q m - η * |S0 k - S0 m| := by
    have hk := (abs_le.mp (herr k)).1
    have hm := (abs_le.mp (herr m)).2
    nlinarith only [hk, hm]
  let P : ℝ := M k ^ (t - 4) * M m ^ (-t)
  have hP : 0 ≤ P := mul_nonneg
    (Real.rpow_nonneg (hM k).le _) (Real.rpow_nonneg (hM m).le _)
  calc
    _ = P * Real.exp (Real.log (H0 k) * (-γ) + Real.log (H0 m) * γ +
        (a * (Q k + Q m) - η * |S0 k - S0 m| - γ * (S0 k - S0 m))) := by
      rw [hinv]
      change (M k ^ (t - 4) * H0 k ^ (-γ)) * (M m ^ (-t) * H0 m ^ γ) * _ = _
      rw [Real.rpow_def_of_pos (hH0 k), Real.rpow_def_of_pos (hH0 m),
        Real.exp_add, Real.exp_add]
      dsimp only [P]
      ring
    _ ≤ P * Real.exp (2 * A + (a + A) * Q k + (a + A) * Q m -
        η * |S0 k - S0 m|) := mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hu) hP
    _ = Real.exp (2 * A) * n05ActualWeightKernel D T K.cell t (a + A) η k m := by
      rw [show 2 * A + (a + A) * Q k + (a + A) * Q m - η * |S0 k - S0 m| =
        2 * A + (a + A) * Q k + (a + A) * Q m + (-η * |S0 k - S0 m|) by ring,
        Real.exp_add, Real.exp_add, Real.exp_add]
      rw [← hweight k, ← hweight m]
      dsimp only [P, M, Q, S0, n05ActualWeightKernel]
      ring

/-- The actual raw inverse, conjugated by the exact canonical sample
weights, satisfies the loss-four kernel estimate. No linearity of chosen
representatives or of the raw block is used in this estimate. -/
theorem n05_canonicalInverseBlock_weighted_bound
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {R : ReturnEquationData S}
    {L : ReturnCorrectionData S} {K : CanonicalData S} {base loss : ℕ} {ε : ℝ}
    (hD : IsRadialReference D) (hT : IsMaterialData D T)
    (hS : IsPhysicalSpaces D T S)
    (h : NonlinearPropertiesThrough04 D T S C R L K base loss ε)
    (hcoordinates : N05ControlledReferenceCoordinates D S C K)
    {β ρ γ δ M0 M1 : ℝ} (hminus : 0 < β - ρ) (hplus : 0 < β + ρ)
    (hγ : |γ - β| ≤ δ) {G : RadialSource → RadialUnknown}
    (hGminus : ReferenceInverseProperties D (β - ρ) M0 M1 G)
    (hGplus : ReferenceInverseProperties D (β + ρ) M0 M1 G) (t : ℝ) :
    ∃ C0 c : ℝ, 0 < C0 ∧ ∀ k m (u : CanonicalL2 S K m),
      ‖(n05CanonicalSampleWeight T S K γ (t - 4) k)⁻¹ •
        n05CanonicalInverseBlock D S C K G k m
          (n05CanonicalSampleWeight T S K γ t m • u)‖ ≤
        C0 * n05ActualWeightKernel D T K.cell t c (ρ - δ) k m * ‖u‖ := by
  obtain ⟨Cb, a, hCb, _, hblock⟩ :=
    n05_canonicalInverseBlock_inner_bound hD hT hS h hcoordinates hminus hplus hGminus hGplus
  obtain ⟨B, c, hB, hkernel⟩ :=
    n05_canonicalSampleWeight_kernel_bound hD.1 hT S K γ t a (ρ - δ)
  refine ⟨Cb * B, c, mul_pos hCb hB, fun k m u => ?_⟩
  let wi := n05CanonicalSampleWeight T S K γ t m
  let wo := n05CanonicalSampleWeight T S K γ (t - 4) k
  let d := radialS (D.cellIndex (K.cell k)) - radialS (D.cellIndex (K.cell m))
  let q := radialQ (D.cellIndex (K.cell k)) + radialQ (D.cellIndex (K.cell m))
  let v := n05CanonicalInverseBlock D S C K G k m (wi • u)
  have hwi : 0 < wi := n05CanonicalSampleWeight_pos hT hD.1.choose_spec.2.1 S K γ t m
  have hwo : 0 < wo := n05CanonicalSampleWeight_pos hT hD.1.choose_spec.2.1 S K γ (t - 4) k
  have hb : Real.exp (γ * d) * ‖v‖ ≤
      Cb * Real.exp (a * q - (ρ - δ) * |d|) * (wi * ‖u‖) := by
    simpa only [norm_smul, Real.norm_eq_abs, abs_of_pos hwi] using
      hblock γ δ hγ k m (wi • u)
  have hc : Real.exp (-γ * d) * Real.exp (γ * d) = 1 := by
    rw [← Real.exp_add, show -γ * d + γ * d = 0 by ring, Real.exp_zero]
  have he : Real.exp (a * q - (ρ - δ) * |d| - γ * d) =
      Real.exp (-γ * d) * Real.exp (a * q - (ρ - δ) * |d|) := by
    rw [← Real.exp_add]
    congr 1
    ring
  change ‖wo⁻¹ • v‖ ≤ _
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hwo)]
  calc
    wo⁻¹ * ‖v‖ = wo⁻¹ * (Real.exp (-γ * d) * (Real.exp (γ * d) * ‖v‖)) := by
      rw [← mul_assoc (Real.exp (-γ * d)) (Real.exp (γ * d)) ‖v‖, hc, one_mul]
    _ ≤ wo⁻¹ * (Real.exp (-γ * d) *
        (Cb * Real.exp (a * q - (ρ - δ) * |d|) * (wi * ‖u‖))) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left hb (Real.exp_pos _).le) (inv_nonneg.mpr hwo.le)
    _ = Cb * (wo⁻¹ * wi * Real.exp (a * q - (ρ - δ) * |d| - γ * d)) * ‖u‖ := by
      rw [he]
      ring
    _ ≤ Cb * (B * n05ActualWeightKernel D T K.cell t c (ρ - δ) k m) * ‖u‖ :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (hkernel k m) hCb.le) (norm_nonneg _)
    _ = _ := by ring

end ContinuousFlexibility.Statements
