module

public import ContinuousFlexibility.Analysis.N05CanonicalInverseBlock
public import ContinuousFlexibility.Analysis.N05InnerExponentBlocks

/-!
# Two endpoint estimates for the same actual canonical block

Taking square roots of the actual endpoint estimate keeps its physical
exponent unchanged. Enlarging only the coefficient powers gives common
weights at both endpoints. Their numerical combination then controls
every inner conjugating exponent for the same fixed global inverse.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Statements

open ContinuousFlexibility.Analysis

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {R : ReturnEquationData S}
  {L : ReturnCorrectionData S} {K : CanonicalData S}
  {base loss : ℕ} {ε : ℝ}

/-- The endpoint norm estimate concerns the literal raw block. Its
coefficient exponent is half that of the established square estimate. -/
theorem n05_canonicalInverseBlock_endpoint_norm_bound
    (hD : IsRadialReference D) (hT : IsMaterialData D T)
    (hS : IsPhysicalSpaces D T S)
    (h : NonlinearPropertiesThrough04 D T S C R L K base loss ε)
    (hcoordinates : N05ControlledReferenceCoordinates D S C K)
    {σ M0 M1 : ℝ} (hσ : 0 < σ) {G : RadialSource → RadialUnknown}
    (hG : ReferenceInverseProperties D σ M0 M1 G) :
    ∃ C0 A : ℝ, 0 < C0 ∧ 0 < A ∧ ∀ k m (u : CanonicalL2 S K m),
      Real.exp (-A * radialQ (D.cellIndex (K.cell k)) +
          σ * radialS (D.cellIndex (K.cell k))) *
        ‖n05CanonicalInverseBlock D S C K G k m u‖ ≤
      C0 * Real.exp (A * radialQ (D.cellIndex (K.cell m)) +
        σ * radialS (D.cellIndex (K.cell m))) * ‖u‖ := by
  obtain ⟨B, a, hB, ha, hbound⟩ :=
    n05_canonicalInverseBlock_endpoint_square_bound hD hT hS h hcoordinates hσ hG
  refine ⟨Real.sqrt B, a / 2, Real.sqrt_pos.2 hB, half_pos ha, fun k m u => ?_⟩
  let Qk := radialQ (D.cellIndex (K.cell k))
  let Qm := radialQ (D.cellIndex (K.cell m))
  let Sk := radialS (D.cellIndex (K.cell k))
  let Sm := radialS (D.cellIndex (K.cell m))
  let y := ‖n05CanonicalInverseBlock D S C K G k m u‖
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
  have hn : Real.exp (σ * Sk) * y ≤
      Real.sqrt B * Real.exp (a / 2 * Qk) * Real.exp (a / 2 * Qm) *
        Real.exp (σ * Sm) * ‖u‖ := by
    apply (sq_le_sq₀ (mul_nonneg (Real.exp_pos _).le hy) (by positivity)).mp
    simpa only [mul_pow, Real.sq_sqrt hB.le, hE, hσexp, hweight, Qk, Qm, Sk, Sm, y]
      using hbound k m u
  have hcancel : Real.exp (-(a / 2) * Qk) * Real.exp (a / 2 * Qk) = 1 := by
    rw [← Real.exp_add, show -(a / 2) * Qk + a / 2 * Qk = 0 by ring, Real.exp_zero]
  change Real.exp (-(a / 2) * Qk + σ * Sk) * y ≤
    Real.sqrt B * Real.exp (a / 2 * Qm + σ * Sm) * ‖u‖
  calc
    _ = Real.exp (-(a / 2) * Qk) * (Real.exp (σ * Sk) * y) := by
      rw [Real.exp_add, mul_assoc]
    _ ≤ Real.exp (-(a / 2) * Qk) *
        (Real.sqrt B * Real.exp (a / 2 * Qk) * Real.exp (a / 2 * Qm) *
          Real.exp (σ * Sm) * ‖u‖) :=
      mul_le_mul_of_nonneg_left hn (Real.exp_pos _).le
    _ = Real.sqrt B * (Real.exp (-(a / 2) * Qk) * Real.exp (a / 2 * Qk)) *
        (Real.exp (a / 2 * Qm) * Real.exp (σ * Sm)) * ‖u‖ := by ring
    _ = _ := by rw [hcancel, mul_one, ← Real.exp_add]

/-- The two physical endpoints control every inner exponent, with constants
chosen before the inner exponent, width, piece indices and input. Whenever
`δ < ρ`, the displayed residual decay is strictly positive. -/
theorem n05_canonicalInverseBlock_inner_bound
    (hD : IsRadialReference D) (hT : IsMaterialData D T)
    (hS : IsPhysicalSpaces D T S)
    (h : NonlinearPropertiesThrough04 D T S C R L K base loss ε)
    (hcoordinates : N05ControlledReferenceCoordinates D S C K)
    {β ρ M0 M1 : ℝ} (hminus : 0 < β - ρ) (hplus : 0 < β + ρ)
    {G : RadialSource → RadialUnknown}
    (hGminus : ReferenceInverseProperties D (β - ρ) M0 M1 G)
    (hGplus : ReferenceInverseProperties D (β + ρ) M0 M1 G) :
    ∃ C0 A : ℝ, 0 < C0 ∧ 0 < A ∧ ∀ γ δ : ℝ, |γ - β| ≤ δ →
      ∀ k m (u : CanonicalL2 S K m),
        Real.exp (γ * (radialS (D.cellIndex (K.cell k)) -
            radialS (D.cellIndex (K.cell m)))) *
          ‖n05CanonicalInverseBlock D S C K G k m u‖ ≤
        C0 * Real.exp (A * (radialQ (D.cellIndex (K.cell k)) +
            radialQ (D.cellIndex (K.cell m))) -
          (ρ - δ) * |radialS (D.cellIndex (K.cell k)) -
            radialS (D.cellIndex (K.cell m))|) * ‖u‖ := by
  obtain ⟨Cm, Am, hCm, hAm, hm⟩ :=
    n05_canonicalInverseBlock_endpoint_norm_bound hD hT hS h hcoordinates hminus hGminus
  obtain ⟨Cp, Ap, hCp, hAp, hp⟩ :=
    n05_canonicalInverseBlock_endpoint_norm_bound hD hT hS h hcoordinates hplus hGplus
  let A : ℝ := max Am Ap
  have hA : 0 < A := hAm.trans_le (le_max_left _ _)
  have hC : 0 < max Cm Cp := hCm.trans_le (le_max_left _ _)
  have henlarge (a c σ : ℝ) (ha : a ≤ A) (hc : 0 ≤ c)
      (k m : ℕ) (u : CanonicalL2 S K m)
      (hb : Real.exp (-a * radialQ (D.cellIndex (K.cell k)) +
          σ * radialS (D.cellIndex (K.cell k))) *
        ‖n05CanonicalInverseBlock D S C K G k m u‖ ≤
        c * Real.exp (a * radialQ (D.cellIndex (K.cell m)) +
          σ * radialS (D.cellIndex (K.cell m))) * ‖u‖) :
      Real.exp (-A * radialQ (D.cellIndex (K.cell k)) +
          σ * radialS (D.cellIndex (K.cell k))) *
        ‖n05CanonicalInverseBlock D S C K G k m u‖ ≤
        c * Real.exp (A * radialQ (D.cellIndex (K.cell m)) +
          σ * radialS (D.cellIndex (K.cell m))) * ‖u‖ := by
    have hk := mul_le_mul_of_nonneg_right ha (Radial.radialQ_nonneg (D.cellIndex (K.cell k)))
    have hm' := mul_le_mul_of_nonneg_right ha (Radial.radialQ_nonneg (D.cellIndex (K.cell m)))
    calc
      _ ≤ Real.exp (-a * radialQ (D.cellIndex (K.cell k)) +
          σ * radialS (D.cellIndex (K.cell k))) *
          ‖n05CanonicalInverseBlock D S C K G k m u‖ :=
        mul_le_mul_of_nonneg_right
          (Real.exp_le_exp.mpr (by linarith only [hk])) (norm_nonneg _)
      _ ≤ _ := hb
      _ ≤ _ := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left
          (Real.exp_le_exp.mpr (by linarith only [hm'])) hc) (norm_nonneg _)
  refine ⟨max Cm Cp, A, hC, hA, fun γ δ hγ k m u => ?_⟩
  have hmid := n05_twoEndpoint_block_bound
    (radialS (D.cellIndex (K.cell k))) (radialS (D.cellIndex (K.cell m)))
    (radialQ (D.cellIndex (K.cell k))) (radialQ (D.cellIndex (K.cell m)))
    β ρ A A Cm Cp ‖u‖ ‖n05CanonicalInverseBlock D S C K G k m u‖ (norm_nonneg _)
    (henlarge Am Cm (β - ρ) (le_max_left _ _) hCm.le k m u (hm k m u))
    (henlarge Ap Cp (β + ρ) (le_max_right _ _) hCp.le k m u (hp k m u))
  simpa only [mul_add] using n05_innerExponent_block_bound
    (radialS (D.cellIndex (K.cell k))) (radialS (D.cellIndex (K.cell m)))
    (radialQ (D.cellIndex (K.cell k))) (radialQ (D.cellIndex (K.cell m)))
    β γ ρ δ A A (max Cm Cp) ‖u‖ ‖n05CanonicalInverseBlock D S C K G k m u‖
    hC.le (norm_nonneg _) hγ hmid

end ContinuousFlexibility.Statements
