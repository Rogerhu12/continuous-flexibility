import ContinuousFlexibility.Radial.InnerMorseModelEnvelope
import ContinuousFlexibility.Radial.InnerMorseBufferLeading
import ContinuousFlexibility.Radial.InnerCentralPhysicalPoisson

/-!
# The same Morse Poisson columns in the actual physical weighted space

The radius, profile identity, cap velocity and physical interval come
from the original realization. Weights interpolate in physical r
between the images of the two actual inner walls. Monotonicity makes
them constant on each complete buffer, while the already proved
coefficient ratio controls the remainder. All positive even-frequency
bands use the same fixed leading constant on both tails.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open Real Set MeasureTheory ContinuousFlexibility.Statements
open scoped ContDiff Matrix.Norms.L2Operator

def innerMorsePhysicalPoissonColumn {T : MorseChainData} {σ : ℕ → ℝ}
    {D : ReferenceData} {cost : ℕ → ℝ} (hreal : MorseChainRealization T σ D cost)
    (side : Bool) (hindex : 10 ≤ T.index) {m : ℕ} (hm : T.index ≤ m)
    {j C K : ℝ}
    (hB : BufferHypotheses
      (innerMorseBufferData (morseChainA T m) (morseChainB T m) j (8 * (T.d m : ℝ) ^ 9)))
    (M : InnerBufferLocalizedData
      (innerMorseBufferData (morseChainA T m) (morseChainB T m) j
        (8 * (T.d m : ℝ) ^ 9)) C K) (i : Fin 2) :
    InnerBorderL2 (radialHilbertMeasure D) :=
  innerModelPhysicalPoissonColumn D hB M (innerMorseChain_height_pos hreal side hm)
    (hreal.radius_smooth side m hm) contDiff_const
    (innerMorseChain_buffer_chart_positive hreal side hm)
    (innerMorseChain_buffer_in_core hreal side hm)
    (innerMorseChain_buffer_profile hreal side hm) 14 (by norm_num)
    (fun _ hx => innerMorseChain_buffer_velocity hreal side hindex hm hx) i

theorem innerMorseModelPhysicalKappa_eq {T : MorseChainData} {m : ℕ} {j C K : ℝ}
    (M : InnerBufferLocalizedData
      (innerMorseBufferData (morseChainA T m) (morseChainB T m) j
        (8 * (T.d m : ℝ) ^ 9)) C K) (height : ℝ) (i : Fin 2) :
    innerPhysicalCutKappa height (fun _ => 1) (fun k => (M.column k).inwardEnergy) i =
      innerLiouvilleBoundaryKappa height (fun _ => 1)
        (bufferCut (innerMorseBufferData (morseChainA T m) (morseChainB T m) j
          (8 * (T.d m : ℝ) ^ 9))) (fun k => (M.column k).inwardEnergy) i := by
  simp only [innerPhysicalCutKappa, innerLiouvilleBoundaryKappa, innerLiouvilleBoundaryDrift,
    deriv_const, mul_zero, zero_div, add_zero]

def innerMorsePoissonConstant : ℝ := sqrt 12 * 30000 * sqrt 2 + 1

theorem innerMorsePoissonConstant_pos : 0 < innerMorsePoissonConstant := by
  unfold innerMorsePoissonConstant
  positivity

/-- The physical interpolation has its exact endpoint value on each
actual model buffer; no inverse-coordinate weight is introduced. -/
theorem innerMorseChain_physical_weight_on_buffer {T : MorseChainData} {σ : ℕ → ℝ}
    {D : ReferenceData} {cost : ℕ → ℝ} (hreal : MorseChainRealization T σ D cost)
    (side : Bool) {m : ℕ} (hm : T.index ≤ m) {j B₀ : ℝ}
    (hB : BufferHypotheses (innerMorseBufferData (morseChainA T m) (morseChainB T m) j B₀))
    (N : ℕ) (a γ : ℝ) (i : Fin 2) {x : ℝ}
    (hx : x ∈ uIcc
      (bufferCut (innerMorseBufferData (morseChainA T m) (morseChainB T m) j B₀) i)
      (bufferInnerWall (innerMorseBufferData (morseChainA T m) (morseChainB T m) j B₀) i)) :
    let B := innerMorseBufferData (morseChainA T m) (morseChainB T m) j B₀
    innerMorseInterpolatedWeight N a γ side m
      (T.radius side m (bufferInnerWall B 0)) (T.radius side m (bufferInnerWall B 1))
      (T.radius side m x) = innerMorseCutWeight N a γ side m i := by
  let B := innerMorseBufferData (morseChainA T m) (morseChainB T m) j B₀
  have hw := innerBuffer_walls_inside hB
  have hw0 : bufferInnerWall B 0 ∈ Icc B.l B.h :=
    ⟨hw.1.le, (hw.2.1.trans hw.2.2).le⟩
  have hw1 : bufferInnerWall B 1 ∈ Icc B.l B.h :=
    ⟨(hw.1.trans hw.2.1).le, hw.2.2.le⟩
  have hxB : x ∈ Icc B.l B.h := innerBuffer_closedSpan_subset hB i hx
  have hsub := innerMorseChain_buffer_subset hreal side hm
  have hmono := hreal.radius_strictMonoOn side m hm
  have hlr : T.radius side m (bufferInnerWall B 0) <
      T.radius side m (bufferInnerWall B 1) := hmono (hsub hw0) (hsub hw1) hw.2.1
  have hleft := innerMorseCutWeight_pos N a γ side m 0
  have hright := innerMorseCutWeight_pos N a γ side m 1
  dsimp only
  rcases (show i = 0 ∨ i = 1 by omega) with rfl | rfl
  · have hx0 : x ∈ Icc B.l (bufferInnerWall B 0) := by
      simpa only [bufferCut, ite_true, uIcc_of_le hw.1.le] using hx
    have hRx : T.radius side m x ≤ T.radius side m (bufferInnerWall B 0) :=
      hmono.monotoneOn (hsub hxB) (hsub hw0) hx0.2
    simpa only [innerMorseInterpolatedWeight, Bool.false_eq_true, ite_false] using
      innerInterpolatedWeight_eqOn_buffer hlr hleft hright false hRx
  · have h10 : (1 : Fin 2) ≠ 0 := by decide
    have hx1 : x ∈ Icc (bufferInnerWall B 1) B.h := by
      simpa only [bufferCut, h10, ite_false, uIcc_of_ge hw.2.2.le] using hx
    have hRx : T.radius side m (bufferInnerWall B 1) ≤ T.radius side m x :=
      hmono.monotoneOn (hsub hw1) (hsub hxB) hx1.1
    simpa only [innerMorseInterpolatedWeight, ite_true] using
      innerInterpolatedWeight_eqOn_buffer hlr hleft hright true hRx

def InnerMorsePhysicalPoissonBound {T : MorseChainData} {σ : ℕ → ℝ}
    {D : ReferenceData} {cost : ℕ → ℝ} (hreal : MorseChainRealization T σ D cost)
    (N : ℕ) (a : ℝ) {m : ℕ} {j C K : ℝ}
    (M : InnerBufferLocalizedData
      (innerMorseBufferData (morseChainA T m) (morseChainB T m) j
        (8 * (T.d m : ℝ) ^ 9)) C K) : Prop :=
  ∀ (side : Bool) (hindex : 10 ≤ T.index) (hm : T.index ≤ m)
    (hB : BufferHypotheses
      (innerMorseBufferData (morseChainA T m) (morseChainB T m) j (8 * (T.d m : ℝ) ^ 9)))
    (γ sign : ℝ), |γ| ≤ 1 → |sign| ≤ 1 →
    ∀ (W : ℝ → ℝ) (hW : Measurable W) (CW : ℝ) (hWC : ∀ r, |W r| ≤ CW),
      (∀ x ∈ Icc innerMorseBufferLeftCut
          (innerMorseBufferRightCut (morseChainA T m) (morseChainB T m)),
        W (T.radius side m x) =
          (innerMorseInterpolatedWeight N a γ side m
            (T.radius side m (bufferInnerWall
              (innerMorseBufferData (morseChainA T m) (morseChainB T m) j
                (8 * (T.d m : ℝ) ^ 9)) 0))
            (T.radius side m (bufferInnerWall
              (innerMorseBufferData (morseChainA T m) (morseChainB T m) j
                (8 * (T.d m : ℝ) ^ 9)) 1)) (T.radius side m x)) ^ sign) → ∀ i : Fin 2,
        ‖((innerMorseCutWeight N a γ side m i) ^ sign *
            sqrt (innerPhysicalCutKappa (morseChainAmplitude T σ m) (fun _ => 1)
              (fun k => (M.column k).inwardEnergy) i))⁻¹ •
          innerBorderFieldMap (radialHilbertMeasure D)
            (innerWeightMultiplier (radialHilbertMeasure D) W hW CW hWC)
            (innerMorsePhysicalPoissonColumn hreal side hindex hm hB M i)‖ ≤
              innerMorsePoissonConstant / j

private theorem physical_bound_of_remainder {T : MorseChainData} {σ : ℕ → ℝ}
    {D : ReferenceData} {cost : ℕ → ℝ} (hreal : MorseChainRealization T σ D cost)
    (N : ℕ) {a : ℝ} (ha : 0 ≤ a) (hN : 4096 ≤ N) (hNa : 64 * a ≤ (N : ℝ))
    {m : ℕ} (hmN : N ≤ m) {j C K : ℝ} (hj : 1 ≤ j) (hC : 0 < C)
    (M : InnerBufferLocalizedData
      (innerMorseBufferData (morseChainA T m) (morseChainB T m) j
        (8 * (T.d m : ℝ) ^ 9)) C K)
    (hrem : ∀ i, innerMorseModelNormalizedRemainder M i ≤ 1 / j) :
    InnerMorsePhysicalPoissonBound hreal N a M := by
  intro side hindex hm hB γ sign hγ hsign W hW CW hWC hinterp i
  let B := innerMorseBufferData (morseChainA T m) (morseChainB T m) j (8 * (T.d m : ℝ) ^ 9)
  let l := T.radius side m (bufferInnerWall B 0)
  let r := T.radius side m (bufferInnerWall B 1)
  let w := (innerMorseCutWeight N a γ side m i) ^ sign
  let Ucap := (30000 / j) * B.mass i
  have hjpos : 0 < j := zero_lt_one.trans_le hj
  have hmass : 0 < B.mass i := buffer_mass_pos hB i
  have hwpos : 0 < w := rpow_pos_of_pos (innerMorseCutWeight_pos N a γ side m i) sign
  have hk := (M.energies_pos hB hC i).1
  have hUcap : 0 ≤ Ucap := mul_nonneg (div_nonneg (by norm_num) hjpos.le) hmass.le
  have hbuffer : ∀ x ∈ uIcc (bufferCut B i) (bufferInnerWall B i),
      |deriv (T.radius side m) x / T.radius side m x| ≤ Ucap := by
    intro x hx
    exact (div_le_iff₀ hmass).mp
      (innerMorseChain_buffer_cap_ratio hreal side hindex hm hjpos (8 * (T.d m : ℝ) ^ 9) i hx)
  have hvelocity : Ucap / B.mass i ≤ 30000 / j := by
    dsimp only [Ucap]
    exact (mul_div_cancel_right₀ _ hmass.ne').le
  have hconstant : ∀ x ∈ uIcc (bufferCut B i) (bufferInnerWall B i),
      W (T.radius side m x) = w := by
    intro x hx
    rw [hinterp x (innerBuffer_closedSpan_subset hB i hx),
      innerMorseChain_physical_weight_on_buffer hreal side hm hB N a γ i hx]
  have hcell : ∀ x ∈ Ioo B.l B.h, |W (T.radius side m x)| ≤ radialE m * w := by
    intro x hx
    have hp : 0 < innerMorseInterpolatedWeight N a γ side m l r (T.radius side m x) :=
      innerInterpolatedWeight_pos l r _ _ _
    rw [hinterp x (Ioo_subset_Icc_self hx), abs_of_pos (rpow_pos_of_pos hp sign)]
    exact (div_le_iff₀ hwpos).mp
      (innerMorseInterpolatedWeight_cut_ratios N ha hγ hsign hN hNa hmN side l r
        (T.radius side m x) i).1
  have hcentral : B.bordered = true → w = 1 := by
    intro h
    simp only [B, innerMorseBufferData, Bool.false_eq_true] at h
  have hnorm := innerModelPhysicalPoissonColumn_frequency_bound D hB M
    (innerMorseChain_height_pos hreal side hm) (hreal.radius_smooth side m hm) contDiff_const
    (innerMorseChain_buffer_chart_positive hreal side hm)
    (innerMorseChain_buffer_in_core hreal side hm) (innerMorseChain_buffer_profile hreal side hm)
    14 (by norm_num) (fun _ hx => innerMorseChain_buffer_velocity hreal side hindex hm hx)
    W hW CW hWC i (ratio := radialE m) (w := w) (Ucap := Ucap)
      (k := (M.column i).inwardEnergy) (j := j) (Kcap := 30000)
      (exp_pos _).le hwpos hUcap hk hjpos (by norm_num) hcentral hconstant hbuffer hcell
      (by linarith only [hk]) hvelocity
      (by simpa only [innerMorseModelNormalizedRemainder] using hrem i)
  simpa only [innerMorsePhysicalPoissonColumn, innerMorsePoissonConstant, innerPhysicalCutKappa]
    using hnorm

/-- The actual physical column estimate and both full conormal error
estimates are now consequences of the ordered choices, for the same M.
The weight is the physical-r interpolation of the global construction. -/
theorem exists_innerMorsePhysicalChoices (hR09 : R09Statement) {a : ℝ} (ha : 0 ≤ a) :
    ∃ C K : ℝ, 0 < C ∧ 0 < K ∧
      ∀ A : ℝ, innerMorseModelAmplitude C K ≤ A →
      ∃ Cstar : ℝ, 0 < Cstar ∧ innerMorseBufferThreshold ≤ Cstar ∧
        ∀ η : ℝ, 0 < η → ∀ initial : ℕ, ∃ N : ℕ,
          initial ≤ N ∧ 4096 ≤ N ∧ 64 * a ≤ (N : ℝ) ∧
          ∀ (T : MorseChainData) (σ : ℕ → ℝ) (D : ReferenceData) (cost : ℕ → ℝ),
            ∀ hreal : MorseChainRealization T σ D cost, T.index = N →
            ∀ m n j : ℕ, N ≤ m → m < n → 2 ≤ j → radialFrequencyBand T Cstar n j →
              BufferHypotheses
                (innerMorseBufferData (morseChainA T m) (morseChainB T m) j
                  (8 * (T.d m : ℝ) ^ 9)) ∧
              ∃ M : InnerBufferLocalizedData
                (innerMorseBufferData (morseChainA T m) (morseChainB T m) j
                  (8 * (T.d m : ℝ) ^ 9)) C K,
                InnerMorsePhysicalPoissonBound hreal N a M ∧
                ∀ γ : ℝ, |γ| ≤ 1 → ∀ side : Bool, ∀ height : ℝ, 0 < height → ∀ sign : Bool,
                  ‖innerTwoCutWeightedError
                    (innerPhysicalCutKappa height (fun _ => 1) (fun i => (M.column i).inwardEnergy))
                    (innerMorseCutWeight N a γ side m)
                    (M.physicalFluxError height (fun _ => 1)) sign‖ < η := by
  obtain ⟨C, K, hC, hK, hchoice⟩ := exists_innerMorseModelChoices hR09 ha
  refine ⟨C, K, hC, hK, ?_⟩
  intro A hA
  obtain ⟨Cstar, hCstar, hgeometry, hmodels⟩ := hchoice A hA
  refine ⟨Cstar, hCstar, hgeometry, ?_⟩
  intro η hη initial
  obtain ⟨N, hN, hlarge, hweight, htail⟩ := hmodels η hη initial
  refine ⟨N, hN, hlarge, hweight, ?_⟩
  intro T σ D cost hreal hindex m n j hm hmn hj hband
  obtain ⟨hB, M, hrem, herror⟩ := htail T σ D cost hreal hindex m n j hm hmn hj hband
  have hj1 : (1 : ℝ) ≤ j := by exact_mod_cast (show 1 ≤ j by omega)
  have hj0 : (0 : ℝ) ≤ j := Nat.cast_nonneg j
  have hr : ∀ i, innerMorseModelNormalizedRemainder M i ≤ 1 / (j : ℝ) :=
    fun i => (hrem i).le.trans (div_le_div_of_nonneg_right (min_le_left 1 η) hj0)
  exact ⟨hB, M, physical_bound_of_remainder hreal N ha hlarge hweight hm hj1 hC M hr, herror⟩

end ContinuousFlexibility.Radial
