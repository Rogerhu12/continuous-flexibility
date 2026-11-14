import ContinuousFlexibility.Analysis.N04NegativeChartRootActualComposition
import ContinuousFlexibility.Analysis.N04NegativeChartRootCoordinateBounds
import ContinuousFlexibility.Analysis.N04NegativeChartOverlapRadius

/-! The low input and its same-flow positive band fix the actual root
coefficient interval and the physical overlap before every jet order. -/

noncomputable section

namespace ContinuousFlexibility.Analysis.N04RealizationStart

open Set ContinuousFlexibility.Statements CanonicalGeometry
open scoped ContDiff

set_option backward.isDefEq.respectTransparency true

attribute [local instance]
  n07aNonlinearAnnularGroup n07aNonlinearAnnularModule
  n07aNonlinearAnnularAddGroup n07aNonlinearAnnularSMul n07aNonlinearAnnularSub
  n07aNonlinearAnnularParameterGroup n07aNonlinearAnnularParameterModule
  n07aNonlinearAnnularParameterAddGroup n07aNonlinearAnnularParameterSMul
  n07aNonlinearAnnularParameterSub
  n07aNonlinearDirectionsGroup n07aNonlinearDirectionsModule
  n07aNonlinearDirectionsAddGroup n07aNonlinearDirectionsSMul n07aNonlinearDirectionsSub
  n07aNonlinearSectorParameterGroup n07aNonlinearSectorParameterModule
  n07aNonlinearSectorParameterAddGroup n07aNonlinearSectorParameterSMul
  n07aNonlinearSectorParameterSub
  interiorRaw_parameterTopology interiorRaw_parameterAddGroup interiorRaw_parameterSMul

/-- The value interval and overlap radius use one scale and one band.
No parameter or spatial derivative estimate is assumed by this package. -/
structure RootValueData (W : N04RealizationStart) (e : ℕ ≃ N04PieceIndex W.D)
    (b : ℕ) (ε C : ℝ) where
  σ : ℕ → Bool → ℝ
  scale : 1 ≤ C
  band : ∀ m side, 0 < σ m side ∧ σ m side ≤ 1
  values : ∃ l A P Q : ℝ, 0 < l ∧ 0 ≤ A ∧ 0 ≤ P ∧ 0 ≤ Q ∧
    ∀ m side z, z ∈ sectorNeighborhood W.S b ε ε →
    ∀ q : PolarPoint, q.1 ∈ Ioc (0 : ℝ) (σ m side) →
      l * W.T.E0 (W.negativeHalfSample e m side) ^ (-P) ≤
        W.negativeRootTravelCoefficient m side (W.negativeChartRootScale e C m side) z q ∧
      W.negativeRootTravelCoefficient m side (W.negativeChartRootScale e C m side) z q ≤
        A * W.T.E0 (W.negativeHalfSample e m side) ^ Q
  overlap_bounds : ∀ m side,
    0 < W.negativeChartRootScale e C m side * σ m side ∧
      W.negativeChartRootScale e C m side * σ m side ≤ W.negativeMaterialCollar m
  overlap_material : ∃ K A : ℝ, 0 < K ∧ 0 ≤ A ∧ ∀ m side,
    (W.negativeChartRootScale e C m side * σ m side)⁻¹ ≤
      K * W.T.E0 (W.negativeHalfSample e m side) ^ A

variable {W : N04RealizationStart} {e : ℕ ≃ N04PieceIndex W.D}

private theorem rootValue_interval_of_inverse (F : W.NegativeOpticalFactors e)
    {d c : (Fin 1 → ℝ) × PolarPoint → ℝ} {δ : ℝ}
    (hd : ContDiff ℝ ∞ d) (hc : ContDiff ℝ ∞ c)
    (hdp : ∀ y r, Function.Periodic (fun θ => d (y, (r, θ))) Real.pi)
    (hcp : ∀ y r, Function.Periodic (fun θ => c (y, (r, θ))) Real.pi)
    (A : NegativeChartRootFlowData d c δ) {z : Parameter W.S}
    (hz : liftSectorParameter W.S W.C z ∈ stateNeighborhood W.S W.C W.base (W.ε / 2))
    (hs : stateSector W.S (liftSectorParameter W.S W.C z).1)
    (m : ℕ) (side : Bool) (hδ : 0 < δ)
    (hcollar : δ * 2 ≤ W.negativeMaterialCollar m)
    (hrep : ∀ p : PolarPoint, p.1 ∈ Icc (0 : ℝ) (W.negativeOpticalWidth m side) →
      d (0, p) = F.fullHalfDrift (liftSectorParameter W.S W.C z) m side p ∧
      c (0, p) = F.fullHalfSpeed (liftSectorParameter W.S W.C z) m side p)
    {p : PolarPoint} (hp : p.1 ∈ Ioc (0 : ℝ) 2) {l u : ℝ}
    (hvalue : extendedRootOddCoefficient
      (W.negativeRootInverseCoordinate A (liftSectorParameter W.S W.C z) m side 0) p ∈
        Icc l u) :
    W.negativeRootTravelCoefficient m side δ z p ∈ Icc l u := by
  let G := W.negativeRootInverseCoordinate A (liftSectorParameter W.S W.C z) m side 0
  have heq : W.negativeRootTravelCoefficient m side δ z p =
      extendedRootOddCoefficient G p :=
    (F.fullHalfFields_root_coefficient hd hc hdp hcp A 0 (z := z) hz hs m side
      (by norm_num : (0 : ℝ) < 2) hδ hcollar hrep (p := p) hp).trans
        ((n04NegativeChart_rootOddCoefficient_sub_angle G hp.1.ne').trans
          (extendedRootOddCoefficient_of_nonneg G hp.1.le).symm)
  exact ⟨hvalue.1.trans_eq heq.symm, heq.trans_le hvalue.2⟩

namespace NegativeOpticalFactors

variable {F : W.NegativeOpticalFactors e} {base loss : ℕ}

/-- The same low-input choice fixes both the root flow scale and the
positive band. Every actual value is checked using a single zero plot
and its supplied inverse flow. All constants precede the state and point. -/
theorem FullHalfFieldPowerControl.root_valueData
    (Q : F.FullHalfFieldPowerControl base loss) {b : ℕ} {ε : ℝ}
    (hb : W.base ≤ b) (hblow : Q.root_low_input.choose ≤ b)
    (hεpos : 0 < ε) (hε : ε ≤ min (W.ε / 2) (1 / 2 : ℝ))
    (hεlow : ε ≤ Q.root_low_input.choose_spec.choose) :
    Nonempty (RootValueData W e b ε Q.rootCompositionScaleCoefficient) := by
  have hlow := Q.root_low_input
  let C := Q.rootCompositionScaleCoefficient
  let B₀ := hlow.choose_spec.choose_spec.choose_spec.choose
  let p₀ := hlow.choose_spec.choose_spec.choose_spec.choose_spec.choose
  have hl := hlow.choose_spec.choose_spec.choose_spec.choose_spec.choose_spec
  have hC : 1 ≤ C := hl.2.2.2.2.1
  have hB₀ : 0 < B₀ := hl.2.2.2.2.2.1
  have hp₀ : 0 < p₀ := hl.2.2.2.2.2.2.1
  have hband := F.fullHalfFields_root_positive_band
  let Bχ := hband.choose
  let pχ := hband.choose_spec.choose
  let Cχ := hband.choose_spec.choose_spec.choose
  have hbs := hband.choose_spec.choose_spec.choose_spec
  have hBχ : 0 < Bχ := hbs.1
  have hpχ : 0 < pχ := hbs.2.1
  have hCχ : 0 < Cχ := hbs.2.2.1
  let E := fun m side => W.T.E0 (W.negativeHalfSample e m side)
  let δ := W.negativeChartRootScale e C
  let σ := fun m side => W.negativeRootPositiveRadius e Bχ pχ Cχ
    (B₀ * E m side ^ p₀) (δ m side) m side
  have hσ (m : ℕ) (side : Bool) : 0 < σ m side ∧ σ m side ≤ 1 := by
    have hd : 0 < δ m side := (W.negativeChartRootScale_bounds e hC m side).1
    have he : 0 < E m side := zero_lt_one.trans_le (W.floor _)
    have hκ : 0 < (Bχ * ((δ m side)⁻¹) ^ 2 * E m side ^ pχ)⁻¹ := by positivity
    have hm : 0 ≤ Cχ * (B₀ * E m side ^ p₀) := by positivity
    have hrad := negativeChartPositiveRadius_bounds hκ hm
    exact ⟨hrad.1, hrad.2.1⟩
  have hscale := W.negativeChartRootScale_inverse_material e hC
  let D := hscale.choose
  let q := hscale.choose_spec.choose
  have hD : 0 < D := hscale.choose_spec.choose_spec.1
  have hq : 0 ≤ q := hscale.choose_spec.choose_spec.2.1
  have hδcost := hscale.choose_spec.choose_spec.2.2
  refine ⟨{
    σ := σ, scale := hC, band := hσ, values := ?_,
    overlap_bounds := ?_, overlap_material := ?_ }⟩
  · refine ⟨(2 * Bχ * D ^ 2)⁻¹, 1 + Cχ * B₀, q * 2 + pχ, p₀,
      by positivity, by positivity, by positivity, hp₀.le, ?_⟩
    intro m side z hz p hp
    have hεhalf : ε ≤ W.ε / 2 := hε.trans (min_le_left _ _)
    have hzlow := liftSectorParameter_mem_stateNeighborhood (C := W.C)
      (sectorNeighborhood_mono W.S hblow hεlow hεlow hz) le_rfl
    have hzhalf := liftSectorParameter_mem_stateNeighborhood (C := W.C)
      (sectorNeighborhood_mono W.S hb hεhalf hεhalf hz) le_rfl
    have hs := W.through03.1.1.2.2.1.liftSectorParameter_sector z
    have hδ := W.negativeChartRootScale_bounds e hC m side
    have hrepresentative := negativeRootRepresentative_nonempty F hb hεhalf z hz
      (0 : (Fin 1 → ℝ) →L[ℝ] Parameter W.S) m side (δ m side)
    let A := hrepresentative.some
    have hrep (r : PolarPoint) (hr : r.1 ∈ Icc (0 : ℝ) (W.negativeOpticalWidth m side)) :
        A.d (0, r) = F.fullHalfDrift (liftSectorParameter W.S W.C z) m side r ∧
        A.c (0, r) = F.fullHalfSpeed (liftSectorParameter W.S W.C z) m side r := by
      simpa only [ContinuousLinearMap.zero_apply, add_zero] using A.fields 0 A.zero_V r hr
    have hinput := hl.2.2.2.2.2.2.2 (liftSectorParameter W.S W.C z) hzlow hs
      m side (δ m side) hδ.1 hδ.2.1 hδ.2.2.2.1 hδ.2.2.2.2
      1 A.d A.c A.hd A.hc A.dp A.cp A.flow 0 hrep
    have he : 0 < E m side := zero_lt_one.trans_le (W.floor _)
    have hM : 0 ≤ B₀ * E m side ^ p₀ := by positivity
    have hbval := hbs.2.2.2 1 A.d A.c A.hd A.hc A.dp A.cp
      (δ m side) hδ.1 hδ.2.1 A.flow m side (B₀ * E m side ^ p₀) hM
    have hv := hbval.2.2.2 0 (liftSectorParameter W.S W.C z) hzhalf hs
      (fun θ => (hrep (0, θ) ⟨le_rfl, (W.negativeOpticalWidth_pos m side).le⟩).2)
      hinput.2 p.1 ⟨hp.1.le, hp.2⟩ p.2
    have hp₂ : p.1 ∈ Ioc (0 : ℝ) 2 :=
      ⟨hp.1, (hp.2.trans (hσ m side).2).trans (by norm_num)⟩
    have hχ := rootValue_interval_of_inverse F A.hd A.hc A.dp A.cp A.flow
      hzhalf hs m side hδ.1 hδ.2.2.1 hrep hp₂ hv
    exact negativeRoot_band_material_values (E := E m side) (W.floor _) hδ.1 hBχ hD hCχ.le hp₀.le
      (hδcost m side) (show B₀ * E m side ^ p₀ ≤ B₀ * E m side ^ p₀ from le_rfl)
      hχ.1 hχ.2
  · intro m side
    exact W.negativeChartOverlapRadius_bounds e (p := pχ) (p₀ := p₀) hC hBχ hCχ hB₀ m side
  · exact W.negativeChartOverlapRadius_inverse_material e hC hBχ hpχ.le hCχ hB₀ hp₀.le

end NegativeOpticalFactors
end ContinuousFlexibility.Analysis.N04RealizationStart

/-- info: 'ContinuousFlexibility.Analysis.N04RealizationStart.NegativeOpticalFactors.FullHalfFieldPowerControl.root_valueData'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ContinuousFlexibility.Analysis.N04RealizationStart.NegativeOpticalFactors.FullHalfFieldPowerControl.root_valueData
