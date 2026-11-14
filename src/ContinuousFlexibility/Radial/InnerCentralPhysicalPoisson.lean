module

public import ContinuousFlexibility.Radial.InnerCentralModelEnvelope
public import ContinuousFlexibility.Radial.InnerLiouvilleConormal

/-!
# The actual central physical Poisson columns at scale j⁻¹

The columns are the existing unit-boundary Liouville lifts of the same
localized model, in the true radial L² space with its single Hilbert
scalar. The middle weight equals one, so either global weight sign is
covered by the same result. The leading estimate and the small
remainder are both derived from the actual central construction.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Radial

open Real Set MeasureTheory ContinuousFlexibility.Statements
open scoped ContDiff Matrix.Norms.L2Operator

theorem innerBuffer_closedSpan_subset {B : BufferData} (hB : BufferHypotheses B)
    (i : Fin 2) : uIcc (bufferCut B i) (bufferInnerWall B i) ⊆ Icc B.l B.h := by
  have hcut : bufferCut B i ∈ Icc B.l B.h := by
    unfold bufferCut
    split_ifs
    · exact left_mem_Icc.mpr hB.1.le
    · exact right_mem_Icc.mpr hB.1.le
  have hw := innerBuffer_walls_inside hB
  have hwall : bufferInnerWall B i ∈ Icc B.l B.h := by
    rcases (show i = 0 ∨ i = 1 by omega) with rfl | rfl
    · exact ⟨hw.1.le, (hw.2.1.trans hw.2.2).le⟩
    · exact ⟨(hw.1.trans hw.2.1).le, hw.2.2.le⟩
  exact uIcc_subset_Icc hcut hwall

theorem innerCentralBuffer_velocity_nonneg {X₀ : ℝ} (hX : 8 ≤ X₀) :
    0 ≤ centralRadiusWeightConstant * (1 + X₀) :=
  mul_nonneg centralRadiusWeightConstant_pos.le (by linarith only [hX])

/-- The whole central interval has the same usable cap velocity. Its
ratio to the actual mass has a constant independent of the far cut. -/
theorem innerCentralBuffer_velocity_over_mass {n : ℕ} (hn : 1 ≤ n)
    {X₀ : ℝ} (hX : 8 ≤ X₀) :
    (centralRadiusWeightConstant * (1 + X₀)) / innerCentralCapMass (2 * n) X₀ ≤
      (8 * centralRadiusWeightConstant) / (2 * n) := by
  have hj := innerCentralBuffer_frequency hn
  have hjpos : (0 : ℝ) < 2 * n := (by norm_num : (0 : ℝ) < 2).trans_le hj
  have hXpos : 0 < X₀ := by linarith only [hX]
  apply (div_le_iff₀ (innerCentralCapMass_pos hjpos hXpos)).mpr
  calc
    centralRadiusWeightConstant * (1 + X₀) ≤ centralRadiusWeightConstant * (2 * X₀) :=
      mul_le_mul_of_nonneg_left (by linarith only [hX]) centralRadiusWeightConstant_pos.le
    _ = ((8 * centralRadiusWeightConstant) / (2 * n)) *
        innerCentralCapMass (2 * n) X₀ := by
      unfold innerCentralCapMass
      field_simp [hjpos.ne']
      <;> ring

theorem innerCentralBuffer_chart_pos (n : ℕ) (X₀ : ℝ) :
    ∀ x ∈ Icc (innerCentralBufferData n X₀).l (innerCentralBufferData n X₀).h,
      0 < centralRadius x ∧ 0 < deriv centralRadius x ∧ 0 < centralDensityRoot x :=
  fun x _ => ⟨centralRadius_pos x, deriv_centralRadius_pos x, centralDensityRoot_pos x⟩

theorem innerCentralBuffer_chart_velocity (n : ℕ) (X₀ : ℝ) :
    ∀ x ∈ Icc (innerCentralBufferData n X₀).l (innerCentralBufferData n X₀).h,
      |deriv centralRadius x / centralRadius x| ≤ centralRadiusWeightConstant * (1 + X₀) :=
  fun _ hx => innerCentralBuffer_velocity hx

def innerCentralPhysicalPoissonColumn (D : ReferenceData) {n : ℕ} {X₀ C K height : ℝ}
    (hX : 8 ≤ X₀) (hB : BufferHypotheses (innerCentralBufferData n X₀))
    (M : InnerBufferLocalizedData (innerCentralBufferData n X₀) C K)
    (hh : 0 < height)
    (hcore : Ioo (centralRadius (-X₀)) (centralRadius X₀) ⊆ radialCore D)
    (hw : ∀ x ∈ Icc (-X₀) X₀,
      D.w (centralRadius x) = height * centralDensityRoot x ^ 2 * deriv centralRadius x)
    (i : Fin 2) : InnerBorderL2 (radialHilbertMeasure D) :=
  innerModelPhysicalPoissonColumn D hB M hh contDiff_centralRadius contDiff_centralDensityRoot
    (innerCentralBuffer_chart_pos n X₀) hcore hw
    (centralRadiusWeightConstant * (1 + X₀)) (innerCentralBuffer_velocity_nonneg hX)
    (innerCentralBuffer_chart_velocity n X₀) i

/-- The normalization used in the norm estimate is exactly the cut
energy in the physical weak-flux identity, including its signed drift. -/
theorem innerCentralModelPhysicalKappa_eq {n : ℕ} {X₀ C K : ℝ}
    (M : InnerBufferLocalizedData (innerCentralBufferData n X₀) C K)
    (height : ℝ) (i : Fin 2) :
    innerPhysicalCutKappa height
      (fun k => centralDensityRoot (bufferCut (innerCentralBufferData n X₀) k))
      (innerCentralModelCutEnergy M) i =
        innerLiouvilleBoundaryKappa height centralDensityRoot (bufferCut (innerCentralBufferData n X₀))
          (fun k => (M.column k).inwardEnergy) i := by
  rw [innerLiouvilleBoundaryKappa, innerLiouvilleBoundaryDrift, deriv_centralDensityRoot]
  dsimp only [innerPhysicalCutKappa, innerCentralModelCutEnergy]
  field_simp [(centralDensityRoot_pos (bufferCut (innerCentralBufferData n X₀) i)).ne']
  <;> ring

def innerCentralPoissonConstant : ℝ :=
  sqrt 12 * (8 * centralRadiusWeightConstant) * sqrt 2 + 1

theorem innerCentralPoissonConstant_pos : 0 < innerCentralPoissonConstant := by
  unfold innerCentralPoissonConstant
  have hυ := centralRadiusWeightConstant_pos
  positivity

/-- This property concerns the actual lifted columns for every exact
central realization and every bounded measurable weight equal to one
on the middle interval. In particular it applies to both global signs. -/
def InnerCentralPhysicalPoissonBound {n : ℕ} {X₀ C K : ℝ}
    (M : InnerBufferLocalizedData (innerCentralBufferData n X₀) C K) : Prop :=
  ∀ (hX : 8 ≤ X₀) (hB : BufferHypotheses (innerCentralBufferData n X₀))
    (D : ReferenceData) (height : ℝ) (hh : 0 < height)
    (hcore : Ioo (centralRadius (-X₀)) (centralRadius X₀) ⊆ radialCore D)
    (hw : ∀ x ∈ Icc (-X₀) X₀,
      D.w (centralRadius x) = height * centralDensityRoot x ^ 2 * deriv centralRadius x)
    (W : ℝ → ℝ) (hW : Measurable W) (CW : ℝ) (hWC : ∀ r, |W r| ≤ CW),
    (∀ x ∈ Icc (-X₀) X₀, W (centralRadius x) = 1) → ∀ i : Fin 2,
      ‖(sqrt (innerPhysicalCutKappa height
          (fun k => centralDensityRoot (bufferCut (innerCentralBufferData n X₀) k))
          (innerCentralModelCutEnergy M) i))⁻¹ •
        innerBorderFieldMap (radialHilbertMeasure D)
          (innerWeightMultiplier (radialHilbertMeasure D) W hW CW hWC)
          (innerCentralPhysicalPoissonColumn D hX hB M hh hcore hw i)‖ ≤
            innerCentralPoissonConstant / (2 * n)

private theorem physical_bound_of_remainder {n : ℕ} (hn : 1 ≤ n) {X₀ C K : ℝ}
    (M : InnerBufferLocalizedData (innerCentralBufferData n X₀) C K) (hC : 0 < C)
    (hfar : 2 * C * centralRadiusA ≤ innerCentralCapMass (2 * n) X₀)
    (hrem : ∀ i, innerCentralModelNormalizedRemainder M i ≤ 1 / (2 * n)) :
    InnerCentralPhysicalPoissonBound M := by
  intro hX hB D height hh hcore hw W hW CW hWC hmiddle i
  have hj := innerCentralBuffer_frequency hn
  have hjpos : (0 : ℝ) < 2 * n := (by norm_num : (0 : ℝ) < 2).trans_le hj
  have hk := innerCentralModelCutEnergy_bounds M hC hfar i
  have hU := innerCentralBuffer_velocity_nonneg hX
  have hbuffer : ∀ x ∈ uIcc (bufferCut (innerCentralBufferData n X₀) i)
      (bufferInnerWall (innerCentralBufferData n X₀) i),
      |deriv centralRadius x / centralRadius x| ≤ centralRadiusWeightConstant * (1 + X₀) :=
    fun _ hx => innerCentralBuffer_velocity (innerBuffer_closedSpan_subset hB i hx)
  have hconstant : ∀ x ∈ uIcc (bufferCut (innerCentralBufferData n X₀) i)
      (bufferInnerWall (innerCentralBufferData n X₀) i), W (centralRadius x) = 1 :=
    fun x hx => hmiddle x (innerBuffer_closedSpan_subset hB i hx)
  have hcell : ∀ x ∈ Ioo (innerCentralBufferData n X₀).l (innerCentralBufferData n X₀).h,
      |W (centralRadius x)| ≤ (1 : ℝ) * 1 := by
    intro x hx
    rw [hmiddle x (Ioo_subset_Icc_self hx)]
    norm_num
  have hnorm := innerModelPhysicalPoissonColumn_frequency_bound D hB M hh
    contDiff_centralRadius contDiff_centralDensityRoot (innerCentralBuffer_chart_pos n X₀)
    hcore hw (centralRadiusWeightConstant * (1 + X₀)) hU
    (innerCentralBuffer_chart_velocity n X₀) W hW CW hWC i
      (ratio := 1) (w := 1) (Ucap := centralRadiusWeightConstant * (1 + X₀))
      (k := innerCentralModelCutEnergy M i) (j := 2 * n)
      (Kcap := 8 * centralRadiusWeightConstant)
      (by norm_num : (0 : ℝ) ≤ 1) (by norm_num : (0 : ℝ) < 1) hU hk.1 hjpos
      (mul_nonneg (by norm_num) centralRadiusWeightConstant_pos.le)
      (fun _ => rfl) hconstant hbuffer hcell hk.2
      (innerCentralBuffer_velocity_over_mass hn hX)
      (by simpa only [innerCentralModelNormalizedRemainder, mul_one] using hrem i)
  simpa only [innerCentralPhysicalPoissonColumn, innerPhysicalCutKappa,
    innerCentralPoissonConstant, one_mul] using hnorm

/-- The physical central column bounds and both normalized conormal
error bounds hold for the very same constructed M at every even mode.
No velocity-to-mass or normalized-remainder estimate is assumed. -/
theorem exists_innerCentralPhysicalChoices (hR09 : R09Statement) :
    ∃ C K : ℝ, 0 < C ∧ 0 < K ∧
      ∀ A : ℝ, innerCentralModelAmplitude C K ≤ A →
      ∀ η : ℝ, 0 < η → ∀ initial : ℝ, ∃ X₀ : ℝ,
        initial ≤ X₀ ∧ 8 ≤ X₀ ∧
        (∀ j : ℝ, 2 ≤ j → 2 * C * centralRadiusA ≤ innerCentralCapMass j X₀) ∧
        ∀ n : ℕ, 1 ≤ n →
          BufferHypotheses (innerCentralBufferData n X₀) ∧
          ∃ M : InnerBufferLocalizedData (innerCentralBufferData n X₀) C K,
            InnerCentralPhysicalPoissonBound M ∧
            ∀ height : ℝ, 0 < height → ∀ sign : Bool,
              ‖innerTwoCutWeightedError
                (innerPhysicalCutKappa height
                  (fun i => centralDensityRoot (bufferCut (innerCentralBufferData n X₀) i))
                  (innerCentralModelCutEnergy M)) (fun _ => 1)
                (M.physicalFluxError height
                  (fun i => centralDensityRoot (bufferCut (innerCentralBufferData n X₀) i))) sign‖ < η := by
  obtain ⟨C, K, hC, hK, hchoice⟩ := exists_innerCentralModelChoices hR09
  refine ⟨C, K, hC, hK, ?_⟩
  intro A hA η hη initial
  obtain ⟨X₀, hinit, hX, hfar, hmodels⟩ := hchoice A hA η hη initial
  refine ⟨X₀, hinit, hX, hfar, ?_⟩
  intro n hn
  obtain ⟨hB, M, _hk, hrem, herror⟩ := hmodels n hn
  have hj := innerCentralBuffer_frequency hn
  have hj0 : (0 : ℝ) ≤ 2 * n := (by norm_num : (0 : ℝ) ≤ 2).trans hj
  have hr : ∀ i, innerCentralModelNormalizedRemainder M i ≤ 1 / (2 * n) :=
    fun i => (hrem i).le.trans (div_le_div_of_nonneg_right (min_le_left 1 η) hj0)
  exact ⟨hB, M, physical_bound_of_remainder hn M hC (hfar (2 * n) hj) hr, herror⟩

end ContinuousFlexibility.Radial
