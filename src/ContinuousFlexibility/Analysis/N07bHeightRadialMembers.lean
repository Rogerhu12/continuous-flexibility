import ContinuousFlexibility.Analysis.N07bHeightRadialWeights
import ContinuousFlexibility.Analysis.SpacesSources
import ContinuousFlexibility.Analysis.N06AngularMeanBridge
import ContinuousFlexibility.Radial.ProfilePartitionBounds
import ContinuousFlexibility.Radial.R11bPhysicalPairing
import Mathlib.Topology.Algebra.InfiniteSum.Real

/-!
# Physical heights belong to strictly weaker natural radial classes

The proof uses the actual physical representatives.  The endpoint estimate
controls each weighted localized square by a common multiple of the square
of its partition function.  The partition-square inequality controls every
finite cell sum, without a multiplicity bound for the discrete cell index.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open Set Filter MeasureTheory
open ContinuousFlexibility.Radial
open scoped BigOperators ContDiff

/-- The normalized material-cylinder pointwise bound gives the actual
height decay at every physical point in the annulus. -/
theorem n07b_heightMember_abs_le_materialH {D : ReferenceData} {T : MaterialData}
    {β : ℝ} {f : PolarPoint → ℝ}
    (hT : IsMaterialData D T) (hf : HeightMember D T β f) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ p ∈ annularOpen D, |f p| ≤ K * T.H p.1 ^ β := by
  obtain ⟨K, hK, hbound⟩ :=
    heightMember_materialPullback_mixedDerivative_uniform_bound hT hf 0 0
  have hdata := hT
  obtain ⟨_, hpos, _, _, _, _, _, _, hright, _⟩ := hdata
  refine ⟨K, hK, fun p hp => ?_⟩
  have hH : 0 < T.H p.1 := (hpos p.1 hp.1).2.1
  have he : T.H p.1 ^ β * materialPullback T β f (T.rho p.1, p.2) = f p := by
    rw [materialPullback, hright p.1 hp.1, ← mul_assoc, ← Real.rpow_add hH,
      add_neg_cancel, Real.rpow_zero, one_mul]
  have hpull : |materialPullback T β f (T.rho p.1, p.2)| ≤ K := by
    simpa only [mixedDerivative, iteratedDeriv_zero] using
      hbound (T.rho p.1, p.2)
  rw [← he, abs_mul, abs_of_pos (Real.rpow_pos_of_pos hH β)]
  calc
    _ ≤ T.H p.1 ^ β * K :=
      mul_le_mul_of_nonneg_left hpull (Real.rpow_pos_of_pos hH β).le
    _ = K * T.H p.1 ^ β := mul_comm _ _

/-- Positive material heights have actual local physical L² representatives. -/
theorem n07b_heightMember_radialCellIntegrable {D : ReferenceData} {T : MaterialData}
    (hpart : RadialPartition D) (hT : IsMaterialData D T)
    {β : ℝ} (hβ : 0 < β) {f : PolarPoint → ℝ} (hf : HeightMember D T β f) :
    RadialCellIntegrable D f := by
  have hc := (heightMember_contDiff_and_flatJets hT hβ hf).1.continuous
  intro m
  have hm : Continuous (fun p : PolarPoint => D.localizer m p.1 * f p) :=
    ((hpart.1 m).continuous.comp continuous_fst).mul hc
  exact r11b_continuous_memLp hm

/-- A common pointwise bound on weighted cell interiors gives a summable
series of actual cell squares.  Only the partition-square bound is used. -/
theorem n07b_weighted_referenceCellSquare_summable {D : ReferenceData}
    (hpart : RadialPartition D) (hab : D.a ≤ D.b) {f : PolarPoint → ℝ}
    (hf : RadialCellIntegrable D f) (w : ℕ → ℝ)
    (hw : ∀ m, 0 ≤ w m) {B : ℝ} (hB : 0 ≤ B)
    (hbound : ∀ (m : ℕ) (p : PolarPoint), p.1 ∈ D.cells m → w m * f p ^ 2 ≤ B) :
    Summable (fun m => w m * referenceCellSquare D m f) := by
  letI : IsFiniteMeasure (radialPhysicalMeasure D) :=
    ⟨r11b_radialPhysicalMeasure_finite D⟩
  have hi (m : ℕ) : Integrable
      (fun p : PolarPoint => w m * (D.localizer m p.1 * f p) ^ 2)
      (radialPhysicalMeasure D) := (hf m).integrable_sq.const_mul _
  have hpoint (s : Finset ℕ) (p : PolarPoint) :
      (∑ m ∈ s, w m * (D.localizer m p.1 * f p) ^ 2) ≤ B := by
    calc
      _ ≤ ∑ m ∈ s, B * D.localizer m p.1 ^ 2 := by
        apply Finset.sum_le_sum
        intro m _
        by_cases hz : D.localizer m p.1 = 0
        · simp only [hz, zero_mul, zero_pow (by decide : 2 ≠ 0), mul_zero, le_refl]
        · have hr : p.1 ∈ D.cells m := hpart.2.2.1 m hz
          calc
            _ = (w m * f p ^ 2) * D.localizer m p.1 ^ 2 := by ring
            _ ≤ B * D.localizer m p.1 ^ 2 :=
              mul_le_mul_of_nonneg_right (hbound m p hr) (sq_nonneg _)
      _ = B * ∑ m ∈ s, D.localizer m p.1 ^ 2 := (Finset.mul_sum s _ _).symm
      _ ≤ B * 1 := mul_le_mul_of_nonneg_left
        (profile_localizer_sq_sum_le_one hpart s p.1) hB
      _ = B := mul_one _
  have hfinite (s : Finset ℕ) :
      (∑ m ∈ s, w m * referenceCellSquare D m f) ≤
        (2 * Real.pi)⁻¹ * ∫ p, B ∂radialPhysicalMeasure D := by
    calc
      _ = ∑ m ∈ s, (2 * Real.pi)⁻¹ *
          ∫ p, w m * (D.localizer m p.1 * f p) ^ 2 ∂radialPhysicalMeasure D := by
        apply Finset.sum_congr rfl
        intro m _
        rw [r11b_referenceCellSquare_eq_integral hab hf m, integral_const_mul]
        ring
      _ = (2 * Real.pi)⁻¹ * ∑ m ∈ s,
          ∫ p, w m * (D.localizer m p.1 * f p) ^ 2 ∂radialPhysicalMeasure D :=
        (Finset.mul_sum s _ _).symm
      _ = (2 * Real.pi)⁻¹ * ∫ p,
          ∑ m ∈ s, w m * (D.localizer m p.1 * f p) ^ 2 ∂radialPhysicalMeasure D := by
        rw [integral_finsetSum s (fun m _ => hi m)]
      _ ≤ (2 * Real.pi)⁻¹ * ∫ p, B ∂radialPhysicalMeasure D := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        exact integral_mono (integrable_finsetSum s (fun m _ => hi m))
          (integrable_const B) (hpoint s)
  exact summable_of_sum_le
    (fun m => mul_nonneg (hw m) (r11b_referenceCellSquare_nonneg hab m f)) hfinite

/-- Every fixed natural material weight is summable below the physical
height exponent, for the actual representative and the actual cells. -/
theorem n07b_heightMember_weighted_referenceCellSquare_summable
    {D : ReferenceData} {T : MaterialData}
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T)
    {β γ : ℝ} (hβ : 0 < β) (hγβ : γ < β)
    {f : PolarPoint → ℝ} (hf : HeightMember D T β f) (A : ℝ) :
    Summable (fun m =>
      Real.exp (A * radialQ (D.cellIndex m) + 2 * γ * radialS (D.cellIndex m)) *
        referenceCellSquare D m f) := by
  have hdata := hD
  obtain ⟨C0, hgeom, hpart, _⟩ := hdata
  obtain ⟨C, hC, hweight⟩ := n07b_material_cell_weight_bound hD hT hβ hγβ A
  obtain ⟨K, hK, hpoint⟩ := n07b_heightMember_abs_le_materialH hT hf
  apply n07b_weighted_referenceCellSquare_summable hpart hgeom.2.1.le
    (n07b_heightMember_radialCellIntegrable hpart hT hβ hf)
    (fun m => Real.exp (A * radialQ (D.cellIndex m) + 2 * γ * radialS (D.cellIndex m)))
    (fun m => (Real.exp_pos _).le) (B := C * K ^ 2) (mul_nonneg hC.le (sq_nonneg K))
  intro m p hp
  have hpCore : p.1 ∈ Ioo D.a D.b := hpart.2.2.2.1 m hp
  have hH : 0 < T.H p.1 := (hT.2.1 p.1 hpCore).2.1
  have hpow : (T.H p.1 ^ β) ^ (2 : ℕ) = T.H p.1 ^ (2 * β) := by
    simpa only [Nat.cast_ofNat, mul_comm] using (Real.rpow_mul_natCast hH.le β 2).symm
  have hsq : f p ^ 2 ≤ K ^ 2 * T.H p.1 ^ (2 * β) := by
    calc
      f p ^ 2 = |f p| ^ 2 := (sq_abs _).symm
      _ ≤ (K * T.H p.1 ^ β) ^ 2 :=
        pow_le_pow_left₀ (abs_nonneg _) (hpoint p ⟨hpCore, mem_univ _⟩) 2
      _ = _ := by rw [mul_pow, hpow]
  calc
    _ ≤ Real.exp (A * radialQ (D.cellIndex m) + 2 * γ * radialS (D.cellIndex m)) *
        (K ^ 2 * T.H p.1 ^ (2 * β)) :=
      mul_le_mul_of_nonneg_left hsq (Real.exp_pos _).le
    _ = K ^ 2 * (Real.exp
        (A * radialQ (D.cellIndex m) + 2 * γ * radialS (D.cellIndex m)) *
        T.H p.1 ^ (2 * β)) := by ring
    _ ≤ K ^ 2 * C := mul_le_mul_of_nonneg_left (hweight m p.1 hp) (sq_nonneg K)
    _ = C * K ^ 2 := mul_comm _ _

/-- The source compatibility condition is the actual physical integral.
No natural weighted membership is assumed. -/
theorem n07b_heightMember_sourceMember {D : ReferenceData} {T : MaterialData}
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T)
    {β γ : ℝ} (hβ : 0 < β) (hγβ : γ < β)
    {f : PolarPoint → ℝ} (hf : HeightMember D T β f)
    (M c : ℝ) (hQ : physicalSourceIntegral D f = 0) :
    SourceMember D γ M (f, c) := by
  have hdata := hD
  obtain ⟨C0, _, hpart, _⟩ := hdata
  have hc := (heightMember_contDiff_and_flatJets hT hβ hf).1.continuous
  have hmean : (fun r => radialAngularMean (fun θ => f (r, θ))) =
      fun r => angularMean (fun θ => f (r, θ)) := by
    funext r
    apply n06_radialAngularMean_eq_angularMean_of_continuous
    · intro θ
      have h := hf.2.2.1 (r, θ)
      simpa only [Prod.mk_add_mk, add_zero] using h
    · exact hc.comp (continuous_const.prodMk continuous_id)
  refine ⟨n07b_heightMember_radialCellIntegrable hpart hT hβ hf, ?_,
    hf.2.2.1, hf.2.1, ?_, ?_⟩
  · exact n07b_heightMember_weighted_referenceCellSquare_summable hD hT hβ hγβ hf (2 * M)
  · rw [hmean]
    exact (spaces_continuous_angularMean hc).intervalIntegrable _ _
  · rw [hmean]
    exact hQ

/-- Adding an arbitrary radial left constant is realized by the same
constant in every strictly weaker natural output weight. -/
theorem n07b_heightMember_outputRealization {D : ReferenceData} {T : MaterialData}
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T)
    {β γ : ℝ} (hβ : 0 < β) (hγβ : γ < β)
    {f : PolarPoint → ℝ} (hf : HeightMember D T β f) (M a μ : ℝ) :
    OutputRealization D γ M a ((fun p => f p + a * D.chiLeft p.1), μ) := by
  have hdata := hD
  obtain ⟨C0, _, hpart, _⟩ := hdata
  have hrem : outputRemainder D a ((fun p => f p + a * D.chiLeft p.1), μ) = f := by
    funext p
    change (f p + a * D.chiLeft p.1) - a * D.chiLeft p.1 = f p
    exact add_sub_cancel_right _ _
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hrem]
    exact n07b_heightMember_radialCellIntegrable hpart hT hβ hf
  · rw [hrem]
    exact n07b_heightMember_weighted_referenceCellSquare_summable hD hT hβ hγβ hf (-2 * M)
  · intro p
    change f (p + (0, Real.pi)) + a * D.chiLeft (p.1 + 0) =
      f p + a * D.chiLeft p.1
    rw [hf.2.2.1 p, add_zero]
  · intro r θ
    change f (r, -θ) + a * D.chiLeft r = f (r, θ) + a * D.chiLeft r
    rw [hf.2.1 r θ]

end ContinuousFlexibility.Statements
