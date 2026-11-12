import ContinuousFlexibility.Analysis.N05CanonicalNormalBlock
import ContinuousFlexibility.Analysis.N05InnerExponentBlocks

/-!
# Two physical endpoints for the same canonical normal blocks

Square roots and the two-weight inequality are applied to the fixed
canonical angular jet of the fixed radial derivative. Their coefficient exponent is chosen before the
retained angular order. Only the finite-order norm constant depends on it.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open ContinuousFlexibility.Analysis

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {R : ReturnEquationData S}
  {L : ReturnCorrectionData S} {K : CanonicalData S} {base loss : ℕ} {ε : ℝ}
  (hD : IsRadialReference D) (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
  (h : NonlinearPropertiesThrough04 D T S C R L K base loss ε)
  (hcoordinates : N05ControlledReferenceCoordinates D S C K)

include hD hT hS h hcoordinates

theorem n05_canonicalNormalInverseBlock_endpoint_norm_bound
    {σ M0 M1 MN : ℝ} (hσ : 0 < σ) {G : RadialSource → RadialUnknown}
    (hG : ReferenceInverseProperties D σ M0 M1 G)
    (hN : FirstNormalInverseEstimate D σ M0 MN G) :
    ∃ A : ℝ, 0 < A ∧ ∀ s : ℕ, ∃ C0 : ℝ, 0 < C0 ∧
      ∀ k m (v : n05CanonicalClosedSubmodule S K (s + 1)) (j : Fin (s + 1)),
      Real.exp (-A * radialQ (D.cellIndex (K.cell k)) + σ * radialS (D.cellIndex (K.cell k))) *
        ‖n05CanonicalAngularJetSequence S K (n05CanonicalRadialJetSequence S K
          (n05CanonicalGlobalInverse D S C K G (Pi.single m (v.val m 0))).1) j.val k‖ ≤
      C0 * Real.exp (A * radialQ (D.cellIndex (K.cell m)) +
        σ * radialS (D.cellIndex (K.cell m))) * ‖v.val m‖ := by
  obtain ⟨a, ha, hs⟩ :=
    n05_canonicalNormalInverseBlock_endpoint_square_bound hD hT hS h hcoordinates hσ hG hN
  refine ⟨a / 2, half_pos ha, fun s => ?_⟩
  obtain ⟨B, hB, hbound⟩ := hs s
  refine ⟨Real.sqrt B, Real.sqrt_pos.mpr hB, fun k m v j => ?_⟩
  let Qk := radialQ (D.cellIndex (K.cell k))
  let Qm := radialQ (D.cellIndex (K.cell m))
  let Sk := radialS (D.cellIndex (K.cell k))
  let Sm := radialS (D.cellIndex (K.cell m))
  let y := ‖n05CanonicalAngularJetSequence S K (n05CanonicalRadialJetSequence S K
    (n05CanonicalGlobalInverse D S C K G (Pi.single m (v.val m 0))).1) j.val k‖
  have hy : 0 ≤ y := norm_nonneg _
  have hE (q : ℝ) : Real.exp (a / 2 * q) ^ 2 = Real.exp (a * q) := by
    rw [pow_two, ← Real.exp_add]
    congr 1
    ring
  have hσexp (r : ℝ) : Real.exp (σ * r) ^ 2 = Real.exp (2 * σ * r) := by
    rw [pow_two, ← Real.exp_add]
    congr 1
    ring
  have hweight (n : ℕ) : radialE n ^ a = Real.exp (a * radialQ n) := by
    rw [radialE, ← Real.exp_mul, mul_comm (radialQ n) a]
  have hn : Real.exp (σ * Sk) * y ≤ Real.sqrt B * Real.exp (a / 2 * Qk) *
      Real.exp (a / 2 * Qm) * Real.exp (σ * Sm) * ‖v.val m‖ := by
    apply (sq_le_sq₀ (mul_nonneg (Real.exp_pos _).le hy) (by positivity)).mp
    simpa only [mul_pow, Real.sq_sqrt hB.le, hE, hσexp, hweight, Qk, Qm, Sk, Sm, y]
      using hbound k m v j
  have hcancel : Real.exp (-(a / 2) * Qk) * Real.exp (a / 2 * Qk) = 1 := by
    rw [← Real.exp_add, show -(a / 2) * Qk + a / 2 * Qk = 0 by ring, Real.exp_zero]
  change Real.exp (-(a / 2) * Qk + σ * Sk) * y ≤
    Real.sqrt B * Real.exp (a / 2 * Qm + σ * Sm) * ‖v.val m‖
  calc
    _ = Real.exp (-(a / 2) * Qk) * (Real.exp (σ * Sk) * y) := by
      rw [Real.exp_add, mul_assoc]
    _ ≤ Real.exp (-(a / 2) * Qk) * (Real.sqrt B * Real.exp (a / 2 * Qk) *
        Real.exp (a / 2 * Qm) * Real.exp (σ * Sm) * ‖v.val m‖) :=
      mul_le_mul_of_nonneg_left hn (Real.exp_pos _).le
    _ = Real.sqrt B * (Real.exp (-(a / 2) * Qk) * Real.exp (a / 2 * Qk)) *
        (Real.exp (a / 2 * Qm) * Real.exp (σ * Sm)) * ‖v.val m‖ := by ring
    _ = _ := by rw [hcancel, mul_one, ← Real.exp_add]

theorem n05_canonicalNormalInverseBlock_inner_bound
    {β ρ M0 M1 MN : ℝ} (hminus : 0 < β - ρ) (hplus : 0 < β + ρ)
    {G : RadialSource → RadialUnknown}
    (hGminus : ReferenceInverseProperties D (β - ρ) M0 M1 G)
    (hGplus : ReferenceInverseProperties D (β + ρ) M0 M1 G)
    (hNminus : FirstNormalInverseEstimate D (β - ρ) M0 MN G)
    (hNplus : FirstNormalInverseEstimate D (β + ρ) M0 MN G) :
    ∃ A : ℝ, 0 < A ∧ ∀ s : ℕ, ∃ C0 : ℝ, 0 < C0 ∧
      ∀ γ δ : ℝ, |γ - β| ≤ δ →
      ∀ k m (v : n05CanonicalClosedSubmodule S K (s + 1)) (j : Fin (s + 1)),
      Real.exp (γ * (radialS (D.cellIndex (K.cell k)) - radialS (D.cellIndex (K.cell m)))) *
        ‖n05CanonicalAngularJetSequence S K (n05CanonicalRadialJetSequence S K
          (n05CanonicalGlobalInverse D S C K G (Pi.single m (v.val m 0))).1) j.val k‖ ≤
      C0 * Real.exp (A * (radialQ (D.cellIndex (K.cell k)) + radialQ (D.cellIndex (K.cell m))) -
        (ρ - δ) * |radialS (D.cellIndex (K.cell k)) - radialS (D.cellIndex (K.cell m))|) *
          ‖v.val m‖ := by
  obtain ⟨Am, hAm, hm⟩ :=
    n05_canonicalNormalInverseBlock_endpoint_norm_bound hD hT hS h hcoordinates hminus hGminus hNminus
  obtain ⟨Ap, hAp, hp⟩ :=
    n05_canonicalNormalInverseBlock_endpoint_norm_bound hD hT hS h hcoordinates hplus hGplus hNplus
  let A := max Am Ap
  have hA : 0 < A := hAm.trans_le (le_max_left _ _)
  refine ⟨A, hA, fun s => ?_⟩
  obtain ⟨Cm, hCm, hmBound⟩ := hm s
  obtain ⟨Cp, hCp, hpBound⟩ := hp s
  have hC : 0 < max Cm Cp := hCm.trans_le (le_max_left _ _)
  refine ⟨max Cm Cp, hC, fun γ δ hγ k m v j => ?_⟩
  let y := ‖n05CanonicalAngularJetSequence S K (n05CanonicalRadialJetSequence S K
    (n05CanonicalGlobalInverse D S C K G (Pi.single m (v.val m 0))).1) j.val k‖
  have henlarge (a c σ : ℝ) (ha : a ≤ A) (hc : 0 ≤ c)
      (hb : Real.exp (-a * radialQ (D.cellIndex (K.cell k)) + σ * radialS (D.cellIndex (K.cell k))) * y ≤
        c * Real.exp (a * radialQ (D.cellIndex (K.cell m)) + σ * radialS (D.cellIndex (K.cell m))) *
          ‖v.val m‖) :
      Real.exp (-A * radialQ (D.cellIndex (K.cell k)) + σ * radialS (D.cellIndex (K.cell k))) * y ≤
        c * Real.exp (A * radialQ (D.cellIndex (K.cell m)) + σ * radialS (D.cellIndex (K.cell m))) *
          ‖v.val m‖ := by
    have hk := mul_le_mul_of_nonneg_right ha (Radial.radialQ_nonneg (D.cellIndex (K.cell k)))
    have hm' := mul_le_mul_of_nonneg_right ha (Radial.radialQ_nonneg (D.cellIndex (K.cell m)))
    calc
      _ ≤ Real.exp (-a * radialQ (D.cellIndex (K.cell k)) +
          σ * radialS (D.cellIndex (K.cell k))) * y :=
        mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (by linarith only [hk])) (norm_nonneg _)
      _ ≤ _ := hb
      _ ≤ _ := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left
        (Real.exp_le_exp.mpr (by linarith only [hm'])) hc) (norm_nonneg _)
  have hmid := n05_twoEndpoint_block_bound
    (radialS (D.cellIndex (K.cell k))) (radialS (D.cellIndex (K.cell m)))
    (radialQ (D.cellIndex (K.cell k))) (radialQ (D.cellIndex (K.cell m)))
    β ρ A A Cm Cp ‖v.val m‖ y (norm_nonneg _)
    (henlarge Am Cm (β - ρ) (le_max_left _ _) hCm.le (hmBound k m v j))
    (henlarge Ap Cp (β + ρ) (le_max_right _ _) hCp.le (hpBound k m v j))
  simpa only [mul_add] using n05_innerExponent_block_bound
    (radialS (D.cellIndex (K.cell k))) (radialS (D.cellIndex (K.cell m)))
    (radialQ (D.cellIndex (K.cell k))) (radialQ (D.cellIndex (K.cell m)))
    β γ ρ δ A A (max Cm Cp) ‖v.val m‖ y hC.le (norm_nonneg _) hγ hmid

end ContinuousFlexibility.Statements
