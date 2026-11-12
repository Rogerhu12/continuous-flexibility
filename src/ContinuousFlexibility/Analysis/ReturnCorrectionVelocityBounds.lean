import ContinuousFlexibility.Analysis.ReturnCorrectionSmallness
import ContinuousFlexibility.Analysis.ReturnCorrectionResidualError

/-!
# Quantitative bounds for the actual corrected velocity

N01 bounds the actual radial coefficient above by nine times the
reference profile. This gives one uniform upper bound on the annulus.
The selected-collar discriminant lower bound therefore controls the
actual half-gap. The correction velocity is bounded directly from its
defining formula using the actual flow derivative and actual K-id.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace ContinuousFlexibility.Statements

open Set
open ContinuousFlexibility.Analysis
open scoped ContDiff

theorem radialCoefficient_upper_of_ratios
    {w W Q d : ℝ} (hw : 0 < w) (hW : 0 < W)
    (hWw : W / w ≤ 2) (hQW : Q / W ≤ 9 / 8) (hd : 1 / 2 ≤ d) :
    Q / (d * Real.sqrt d) ≤ 9 * w := by
  have hw' := (div_le_iff₀ hw).mp hWw
  have hQ' := (div_le_iff₀ hW).mp hQW
  have hQw : Q ≤ (9 / 4 : ℝ) * w := by linarith only [hw', hQ']
  have hs : (1 / 2 : ℝ) ≤ Real.sqrt d :=
    Real.le_sqrt_of_sq_le (by nlinarith only [hd])
  have hp : (1 / 4 : ℝ) ≤ d * Real.sqrt d := by
    have h := mul_le_mul hd hs (by norm_num : (0 : ℝ) ≤ 1 / 2)
      (by linarith only [hd] : 0 ≤ d)
    norm_num at h
    exact h
  apply (div_le_iff₀ ((by norm_num : (0 : ℝ) < 1 / 4).trans_le hp)).mpr
  have hmul := mul_le_mul_of_nonneg_left hp
    (mul_nonneg (by norm_num : (0 : ℝ) ≤ 9) hw.le)
  nlinarith only [hQw, hmul]

theorem N01Properties.originalRadialCoefficient_le_nine_profile
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {base loss : ℕ} {ε : ℝ}
    (hN : N01Properties D T S C base loss ε)
    {z : AnnularState S × ℝ} (hz : z ∈ stateNeighborhood S C base ε)
    (hsector : stateSector S z.1) {p : PolarPoint} (hp : p ∈ annularOpen D) :
    (originalCoefficients D S C z).a p ≤ 9 * D.w p.1 := by
  obtain ⟨_, hdata⟩ := hN.1.1
  have hw : 0 < D.w p.1 := hdata.1.2.2.2.2.1 p.1 hp.1
  have hW : 0 < stateProfile D S C z.1 p.1 := by
    change 0 < D.w p.1 * Real.exp _
    exact mul_pos hw (Real.exp_pos _)
  have hdata' := hN
  rcases hdata' with ⟨_, _, _, _, _, _, _, _, _, hcoeff, _⟩
  have hb := hcoeff z hz hsector p hp
  have h := radialCoefficient_upper_of_ratios hw hW hb.2.1 hb.2.2.2.1 hb.2.2.2.2.1
  change polarLinearA (stateProfile D S C z.1) (stateHeight D S C z) p ≤ _
  unfold polarLinearA linearRadial polarScale inverseDThreeHalves
  simpa only [one_div, ← div_eq_mul_inv] using h

theorem N01Properties.originalRadialCoefficient_uniform_upper
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {base loss : ℕ} {ε : ℝ}
    (hN : N01Properties D T S C base loss ε) :
    ∃ A : ℝ, 0 < A ∧ ∀ z ∈ stateNeighborhood S C base ε,
      stateSector S z.1 → ∀ p ∈ annularOpen D, (originalCoefficients D S C z).a p ≤ A := by
  obtain ⟨_, hdata⟩ := hN.1.1
  have hw : ContDiff ℝ ∞ D.w := hdata.1.2.2.1.1
  obtain ⟨K, hK⟩ := (isCompact_Icc (a := D.a) (b := D.b)).exists_bound_of_continuousOn
    hw.continuous.continuousOn
  let A := 9 * max K 1
  have hA : 0 < A := mul_pos (by norm_num) (zero_lt_one.trans_le (le_max_right _ _))
  refine ⟨A, hA, fun z hz hsector p hp => ?_⟩
  have hbound : |D.w p.1| ≤ K := by
    simpa only [Real.norm_eq_abs] using hK p.1 ⟨hp.1.1.le, hp.1.2.le⟩
  have hwK : D.w p.1 ≤ max K 1 :=
    (le_abs_self _).trans (hbound.trans (le_max_left _ _))
  exact (hN.originalRadialCoefficient_le_nine_profile hz hsector hp).trans
    (mul_le_mul_of_nonneg_left hwK (by norm_num))

theorem characteristic_halfGap_lower_of_discriminant
    {a b c A d : ℝ} (ha : 0 < a) (haA : a ≤ A) (hd : 0 ≤ d)
    (hdisc : d ^ 2 ≤ b ^ 2 - a * c) :
    d / A ≤ Real.sqrt (b ^ 2 - a * c) / a :=
  (div_le_div_of_nonneg_left hd ha haA).trans
    (div_le_div_of_nonneg_right (Real.le_sqrt_of_sq_le hdisc) ha.le)

theorem returnCorrectedMinusSpeed_error_bound
    (D : ReferenceData) (S : PhysicalSpacesData) (C : NonlinearGeometryData S)
    (χ : ℕ → ℝ → ℝ) (z : AnnularState S × ℝ) (m : ℕ) (p : PolarPoint)
    {F L : ℝ} (hF : ∀ θ, |deriv (C.minusFlow z m p.1) θ| ≤ F)
    (hL : ∀ θ, |returnCorrectionInitialMap S C z m θ - θ| ≤ L) :
    |returnCorrectedMinusSpeed D S C χ z m p -
      minusCharacteristicSpeed (originalCoefficients D S C z) p| ≤
      F * |deriv (χ m) p.1| * L := by
  let α := Function.invFun (C.minusFlow z m p.1) p.2
  let θ := Function.invFun
    (returnInterpolation (χ m p.1) (returnCorrectionInitialMap S C z m)) α
  have hF₀ : 0 ≤ F := (abs_nonneg _).trans (hF α)
  have hbound := mul_le_mul
    (mul_le_mul_of_nonneg_right (hF α) (abs_nonneg (deriv (χ m) p.1)))
    (hL θ) (abs_nonneg _) (mul_nonneg hF₀ (abs_nonneg _))
  simpa only [returnCorrectedMinusSpeed, add_sub_cancel_left, abs_mul, α, θ] using hbound

theorem N01Properties.returnCorrectedMinusSpeed_error_weighted
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {base loss : ℕ} {ε : ℝ}
    (hN : N01Properties D T S C base loss ε)
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T) :
    ∃ B K : ℝ, 0 < B ∧ 0 < K ∧
      ∀ base' : ℕ, base ≤ base' → 1 + hN.ordinaryFlowLoss 1 ≤ base' →
      ∀ η : ℝ, 0 ≤ η → η ≤ ε → η ≤ 1 / 2 → K * η ≤ 1 →
      ∀ z ∈ stateNeighborhood S C base' η, stateSector S z.1 →
      ∀ χ : ℕ → ℝ → ℝ, ∀ m p, p.1 ∈ Icc (C.left m) (C.right m) →
      |returnCorrectedMinusSpeed D S C χ z m p -
        minusCharacteristicSpeed (originalCoefficients D S C z) p| ≤
        4 * |deriv (χ m) p.1| *
          (6 * B * T.H (T.sample (C.cell m)) ^ (3 / 4 : ℝ) *
            T.E0 (T.sample (C.cell m)) ^ B * η +
            (2 * circleSobolevConstant * η) * T.H (T.sample m) ^ (3 / 4 : ℝ)) := by
  obtain ⟨B, hB, hb⟩ := hN.returnCorrectionInitialMap_and_residual_small hS hT
  obtain ⟨K, hK, hk⟩ := hN.minusFlow_near_reference_uniform hS hT
  refine ⟨B, K, hB, hK,
    fun base' hbase hhigh η hη hηε hη₁ hηK z hz hsector χ m p hp => ?_⟩
  have hderiv (θ : ℝ) : |deriv (C.minusFlow z m p.1) θ| ≤ 2 := by
    have hd := (hk base' hbase hhigh η hη hηε hη₁ z hz hsector m p.1 hp θ).2.trans hηK
    calc
      _ = |(deriv (C.minusFlow z m p.1) θ - 1) + 1| := by congr 1; ring
      _ ≤ |deriv (C.minusFlow z m p.1) θ - 1| + |(1 : ℝ)| := abs_add_le _ _
      _ ≤ 1 + 1 := add_le_add hd (by norm_num)
      _ = 2 := by norm_num
  have h := returnCorrectedMinusSpeed_error_bound D S C χ z m p hderiv
    (fun θ => (hb base' hbase hhigh η hηε hη₁ z hz hsector m θ).1)
  exact h.trans_eq (by ring)

end ContinuousFlexibility.Statements

