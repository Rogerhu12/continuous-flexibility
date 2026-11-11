import ContinuousFlexibility.Radial.InnerMorseScaledPhysicalChart
import ContinuousFlexibility.Radial.InnerMorsePhysicalPoisson

/-!
# Scaled Morse columns with the actual physical interpolation

The column below is the column of the final actual chart, in the final
reference Hilbert space. Its estimate follows from the remainder of the
same selected model. Positive radius and height dilations add no
constant: the velocity, cap ratio and normalized model remainder are
unchanged. Both weight signs are covered by the same real exponent.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open Real Set MeasureTheory ContinuousFlexibility.Statements
open scoped ContDiff

/-- Applying one nonzero dilation to the argument and both walls
preserves the interpolation coordinate. -/
theorem innerInterpolatedWeight_dilation (rs : ℝ) (hrs : rs ≠ 0)
    (l r u v x : ℝ) :
    innerInterpolatedWeight (rs * l) (rs * r) u v (rs * x) =
      innerInterpolatedWeight l r u v x := by
  have hratio : (rs * x - rs * l) / (rs * r - rs * l) = (x - l) / (r - l) := by
    rw [← mul_sub, ← mul_sub]
    by_cases hrl : r - l = 0
    · simp only [hrl, mul_zero, div_zero]
    · field_simp [hrs, hrl] <;> ring
  simp only [innerInterpolatedWeight, innerWeightTransition, hratio]

/-- The final physical interpolation is constant on each full scaled
buffer, with the original cut value. -/
theorem innerMorseScaledChain_physical_weight_on_buffer
    {T : MorseChainData} {σ : ℕ → ℝ} {D₀ : ReferenceData} {cost : ℕ → ℝ}
    (hreal : MorseChainRealization T σ D₀ cost) (side : Bool) {m : ℕ}
    (hm : T.index ≤ m) {rs : ℝ} (hrs : 0 < rs) {j B₀ : ℝ}
    (hB : BufferHypotheses
      (innerMorseBufferData (morseChainA T m) (morseChainB T m) j B₀))
    (N : ℕ) (a γ : ℝ) (i : Fin 2) {x : ℝ}
    (hx : x ∈ uIcc
      (bufferCut (innerMorseBufferData (morseChainA T m) (morseChainB T m) j B₀) i)
      (bufferInnerWall (innerMorseBufferData (morseChainA T m) (morseChainB T m) j B₀) i)) :
    let B := innerMorseBufferData (morseChainA T m) (morseChainB T m) j B₀
    innerMorseInterpolatedWeight N a γ side m
      (rs * T.radius side m (bufferInnerWall B 0))
      (rs * T.radius side m (bufferInnerWall B 1))
      (rs * T.radius side m x) = innerMorseCutWeight N a γ side m i := by
  dsimp only
  unfold innerMorseInterpolatedWeight
  rw [innerInterpolatedWeight_dilation rs hrs.ne']
  simpa only [innerMorseInterpolatedWeight] using
    innerMorseChain_physical_weight_on_buffer hreal side hm hB N a γ i hx

section CommonChain

variable {T : MorseChainData} {σ : ℕ → ℝ} {D₀ : ReferenceData} {cost : ℕ → ℝ}
  (hreal : MorseChainRealization T σ D₀ cost) (hindex : 10 ≤ T.index)
  (D : ReferenceData) {n : ℕ} (G : InnerRadialChainGeometry D n)
  (bordered : Bool) (j : ℝ) (central piece : Fin (n + 1)) (column : RadialModeL2 D)
  (side : Bool) (m : ℕ) (hm : T.index ≤ m) (rs hs : ℝ)
  (hrs : 0 < rs) (hhs : 0 < hs)
  (hprofile : ∀ x ∈ Icc innerMorseBufferLeftCut
      (innerMorseBufferRightCut (morseChainA T m) (morseChainB T m)),
    D.w (rs * T.radius side m x) = hs * rs * D₀.w (T.radius side m x))
  (haway : piece ≠ central)
  (hleft : G.left piece = rs * innerMorseChainCut T side m 0)
  (hright : G.right piece = rs * innerMorseChainCut T side m 1)
  {C K : ℝ}
  (hB : BufferHypotheses (innerMorseBufferData (morseChainA T m) (morseChainB T m)
    j (8 * (T.d m : ℝ) ^ 9)))
  (M : InnerBufferLocalizedData
    (innerMorseBufferData (morseChainA T m) (morseChainB T m)
      j (8 * (T.d m : ℝ) ^ 9)) C K)

/-- The same selected remainder controls either signed weight on the
actual final physical column. No physical column estimate is an input. -/
theorem innerMorseScaledPhysicalModelChart_poisson_bound
    (N : ℕ) {a : ℝ} (ha : 0 ≤ a) (hN : 4096 ≤ N) (hNa : 64 * a ≤ (N : ℝ))
    (hmN : N ≤ m) (hj : 1 ≤ j) (hC : 0 < C)
    (hrem : ∀ i, innerMorseModelNormalizedRemainder M i ≤ 1 / j)
    (γ sign : ℝ) (hγ : |γ| ≤ 1) (hsign : |sign| ≤ 1)
    (W : ℝ → ℝ) (hW : Measurable W) (CW : ℝ) (hWC : ∀ r, |W r| ≤ CW)
    (hinterp : ∀ x ∈ Icc innerMorseBufferLeftCut
        (innerMorseBufferRightCut (morseChainA T m) (morseChainB T m)),
      W (rs * T.radius side m x) =
        (innerMorseInterpolatedWeight N a γ side m
          (rs * T.radius side m (bufferInnerWall
            (innerMorseBufferData (morseChainA T m) (morseChainB T m) j
              (8 * (T.d m : ℝ) ^ 9)) 0))
          (rs * T.radius side m (bufferInnerWall
            (innerMorseBufferData (morseChainA T m) (morseChainB T m) j
              (8 * (T.d m : ℝ) ^ 9)) 1)) (rs * T.radius side m x)) ^ sign)
    (i : Fin 2) :
    let A := innerMorseScaledPhysicalModelChart hreal hindex D G bordered j central piece
      column side m hm rs hs hrs hhs hprofile haway hleft hright hB M
    ‖((innerMorseCutWeight N a γ side m i) ^ sign * sqrt (A.kappa i))⁻¹ •
      innerBorderFieldMap (radialHilbertMeasure D)
        (innerWeightMultiplier (radialHilbertMeasure D) W hW CW hWC) (A.column i)‖ ≤
          innerMorsePoissonConstant / j := by
  let A := innerMorseScaledPhysicalModelChart hreal hindex D G bordered j central piece
    column side m hm rs hs hrs hhs hprofile haway hleft hright hB M
  change ‖((innerMorseCutWeight N a γ side m i) ^ sign * sqrt (A.kappa i))⁻¹ •
    innerBorderFieldMap (radialHilbertMeasure D)
      (innerWeightMultiplier (radialHilbertMeasure D) W hW CW hWC) (A.column i)‖ ≤
        innerMorsePoissonConstant / j
  let B := innerMorseBufferData (morseChainA T m) (morseChainB T m) j (8 * (T.d m : ℝ) ^ 9)
  let l := rs * T.radius side m (bufferInnerWall B 0)
  let r := rs * T.radius side m (bufferInnerWall B 1)
  let w := (innerMorseCutWeight N a γ side m i) ^ sign
  let Ucap := (30000 / j) * B.mass i
  have hjpos : 0 < j := zero_lt_one.trans_le hj
  have hmass : 0 < B.mass i := buffer_mass_pos hB i
  have hwpos : 0 < w := rpow_pos_of_pos (innerMorseCutWeight_pos N a γ side m i) sign
  have hk := (M.energies_pos hB hC i).1
  have hUcap : 0 ≤ Ucap := mul_nonneg (div_nonneg (by norm_num) hjpos.le) hmass.le
  have hbuffer : ∀ x ∈ uIcc (bufferCut B i) (bufferInnerWall B i),
      |deriv A.radius x / A.radius x| ≤ Ucap := by
    intro x hx
    exact (div_le_iff₀ hmass).mp
      (innerMorseScaledChain_buffer_cap_ratio hreal side hm hrs hindex hjpos
        (8 * (T.d m : ℝ) ^ 9) i hx)
  have hvelocity : Ucap / B.mass i ≤ 30000 / j := by
    dsimp only [Ucap]
    exact (mul_div_cancel_right₀ _ hmass.ne').le
  have hconstant : ∀ x ∈ uIcc (bufferCut B i) (bufferInnerWall B i),
      W (A.radius x) = w := by
    intro x hx
    change W (rs * T.radius side m x) = w
    rw [hinterp x (innerBuffer_closedSpan_subset hB i hx),
      innerMorseScaledChain_physical_weight_on_buffer hreal side hm hrs hB N a γ i hx]
  have hcell : ∀ x ∈ Ioo B.l B.h, |W (A.radius x)| ≤ radialE m * w := by
    intro x hx
    change |W (rs * T.radius side m x)| ≤ radialE m * w
    have hp : 0 < innerMorseInterpolatedWeight N a γ side m l r (rs * T.radius side m x) :=
      innerInterpolatedWeight_pos l r _ _ _
    rw [hinterp x (Ioo_subset_Icc_self hx), abs_of_pos (rpow_pos_of_pos hp sign)]
    exact (div_le_iff₀ hwpos).mp
      (innerMorseInterpolatedWeight_cut_ratios N ha hγ hsign hN hNa hmN side l r
        (rs * T.radius side m x) i).1
  have hcentral : B.bordered = true → w = 1 := by
    intro h
    simp only [B, innerMorseBufferData, Bool.false_eq_true] at h
  have hnorm := innerModelPhysicalPoissonColumn_frequency_bound D hB M
    A.height_pos A.radius_smooth A.scale_smooth A.chart_pos A.in_core A.weight_identity
    14 (by norm_num) A.log_deriv_bound W hW CW hWC i
      (ratio := radialE m) (w := w) (Ucap := Ucap) (k := (M.column i).inwardEnergy)
      (j := j) (Kcap := 30000)
      (exp_pos _).le hwpos hUcap hk hjpos (by norm_num) hcentral hconstant hbuffer hcell
      (by linarith only [hk]) hvelocity
      (by simpa only [innerMorseModelNormalizedRemainder] using hrem i)
  have hkappa : A.kappa i =
      innerPhysicalCutKappa (hs * morseChainAmplitude T σ m) (fun _ => 1)
        (fun k => (M.column k).inwardEnergy) i :=
    innerMorseScaledPhysicalModelChart_kappa hreal hindex D G bordered j central piece
      column side m hm rs hs hrs hhs hprofile haway hleft hright hB M i
  rw [hkappa]
  simpa only [InnerRadialModelChart.column, innerPhysicalCutKappa, innerMorsePoissonConstant]
    using hnorm

end CommonChain

end ContinuousFlexibility.Radial
