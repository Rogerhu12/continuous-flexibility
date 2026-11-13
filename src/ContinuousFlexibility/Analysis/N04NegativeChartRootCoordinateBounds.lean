import ContinuousFlexibility.Analysis.N04NegativeChartRootCoefficient
import ContinuousFlexibility.Analysis.N04NegativeChartRootScale
import ContinuousFlexibility.Analysis.N04NegativeChartPositivePowerBounds
import ContinuousFlexibility.Analysis.N04NegativeChartRadialProjectionBounds
import ContinuousFlexibility.Analysis.N04NegativeChartPhysicalBounds
import ContinuousFlexibility.Analysis.N04NegativeHeightDomains
import ContinuousFlexibility.Analysis.N04NegativeChartInteriorRawBudget

/-! The actual divided travel and angle prefix determine both physical
chart components on the selected material root band. -/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set ContinuousFlexibility.Statements CanonicalGeometry
open scoped ContDiff BigOperators

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

namespace N04RealizationStart

attribute [local instance] interiorRaw_parameterTopology interiorRaw_parameterAddGroup interiorRaw_parameterSMul

def negativeRootPrefixField (W : N04RealizationStart) (m : ℕ) (side odd : Bool)
    (δ : ℝ) (z : Parameter W.S) (q : PolarPoint) : ℝ :=
  if odd then W.negativeRootTravelCoefficient m side δ z q
    else W.negativeRootAngleDefect m side δ z q

/-- Raw fractional prefixes of the actual two root coefficients. The
scale and parameter neighborhood are fixed before every derivative order. -/
structure RootCoordinatePrefixData (W : N04RealizationStart)
    (e : ℕ ≃ N04PieceIndex W.D) (base : ℕ) (ε C : ℝ) (σ : ℕ → Bool → ℝ) : Prop where
  base_le : W.base ≤ base
  ε_pos : 0 < ε
  ε_le : ε ≤ W.ε
  ε_small : ε ≤ 1 / 2
  scale : 1 ≤ C
  band : ∀ m side, 0 < σ m side ∧ σ m side ≤ 1
  values : ∃ l A P Q : ℝ, 0 < l ∧ 0 ≤ A ∧ 0 ≤ P ∧ 0 ≤ Q ∧
    ∀ m side z, z ∈ sectorNeighborhood W.S base ε ε →
    ∀ q : PolarPoint, q.1 ∈ Ioc (0 : ℝ) (σ m side) →
      l * W.T.E0 (W.negativeHalfSample e m side) ^ (-P) ≤
        W.negativeRootTravelCoefficient m side (W.negativeChartRootScale e C m side) z q ∧
      W.negativeRootTravelCoefficient m side (W.negativeChartRootScale e C m side) z q ≤
        A * W.T.E0 (W.negativeHalfSample e m side) ^ Q
  «prefix» : ∀ K : ℕ, 0 < K → ∃ shift : ℕ, ∀ s : ℕ, ∃ B : ℝ, 0 < B ∧
    ∀ m (side odd : Bool) (q : PolarPoint), q.1 ∈ Ioc (0 : ℝ) (σ m side) →
    ∀ k, k ≤ K → ∀ a b, a + b ≤ s →
    ∀ J : SmoothDirections (sectorNeighborhood W.S base ε ε)
      (fun z => mixedDerivative a b
        (W.negativeRootPrefixField m side odd (W.negativeChartRootScale e C m side) z) q),
    ∀ z, z ∈ sectorNeighborhood W.S base ε ε → ∀ v : Fin k → Parameter W.S,
      (∀ i, parameterGrading W.S base (v i) ≤ 1) →
    ∀ R : ℝ, 1 ≤ R → parameterGrading W.S (base + s + shift * K + 1) z ≤ R →
      (∀ i, parameterGrading W.S (base + s + shift * K + 1) (v i) ≤ R) →
      ‖J.D k z v‖ ≤ B * W.T.E0 (W.negativeHalfSample e m side) ^ B *
        parameterHeightWeight (W.T.H (W.negativeHalfSample e m side) ^ (3 / 4 : ℝ)) k *
          R ^ (((a + b + shift * k : ℕ) : ℝ) / (((s + shift * K : ℕ) : ℝ) + 1))

/-- Scalar conversion of the actual positive-band interval to a
material interval. No inverse of the chosen band radius is lost. -/
theorem negativeRoot_band_material_values
    {E δ B D C M L p q r χ : ℝ}
    (hE : 1 ≤ E) (hδ : 0 < δ) (hB : 0 < B) (hD : 0 < D)
    (hC : 0 ≤ C) (hr : 0 ≤ r)
    (hδcost : δ⁻¹ ≤ D * E ^ q) (hMcost : M ≤ L * E ^ r)
    (hlo : (B * (δ⁻¹) ^ 2 * E ^ p)⁻¹ / 2 ≤ χ) (hhi : χ ≤ 1 + C * M) :
    (2 * B * D ^ 2)⁻¹ * E ^ (-(q * 2 + p)) ≤ χ ∧
      χ ≤ (1 + C * L) * E ^ r := by
  have hEp : 0 < E := zero_lt_one.trans_le hE
  have hpow := pow_le_pow_left₀ (inv_nonneg.mpr hδ.le) hδcost 2
  have hden : B * (δ⁻¹) ^ 2 * E ^ p ≤ B * D ^ 2 * E ^ (q * 2 + p) := by
    have hb := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hpow hB.le)
      (Real.rpow_nonneg hEp.le p)
    simpa only [mul_pow, ← Real.rpow_mul_natCast hEp.le, Nat.cast_ofNat,
      Real.rpow_add hEp, mul_assoc] using hb
  have hi := div_le_div_of_nonneg_right
    (inv_anti₀ (show 0 < B * (δ⁻¹) ^ 2 * E ^ p by positivity) hden)
    (by norm_num : (0 : ℝ) ≤ 2)
  refine ⟨?_, ?_⟩
  · have he : (B * D ^ 2 * E ^ (q * 2 + p))⁻¹ / 2 =
        (2 * B * D ^ 2)⁻¹ * E ^ (-(q * 2 + p)) := by
      rw [Real.rpow_neg hEp.le, mul_inv_rev, mul_inv_rev, mul_inv_rev, mul_inv_rev]
      ring
    exact he.symm.trans_le (hi.trans hlo)
  · exact hhi.trans ((add_le_add (Real.one_le_rpow hE hr)
      (mul_le_mul_of_nonneg_left hMcost hC)).trans_eq (by ring))

variable {W : N04RealizationStart} {e : ℕ ≃ N04PieceIndex W.D}
  {base : ℕ} {ε C : ℝ} {σ : ℕ → Bool → ℝ}
  (A : RootCoordinatePrefixData W e base ε C σ)

include A in
theorem RootCoordinatePrefixData.scale_component (m : ℕ) (side : Bool) :
    W.negativeChartRootScale e C m side * 2 ≤ W.C.right m - W.C.left m := by
  have hs := W.negativeChartRootScale_bounds e A.scale m side
  have hc := (W.negativeMaterialCollar_bounds m).2.2.2 side
  have hw := W.negativeOpticalWidth_pos m side
  exact hs.2.2.1.trans ((by linarith only [hc, hw] :
    W.negativeMaterialCollar m ≤ W.negativeOpticalWidth m side).trans
      (W.negativeOpticalWidth_le_component m side))

def RootCoordinatePrefixData.regularity (m : ℕ) (side odd : Bool) :
    MixedJetRegularity (sectorNeighborhood W.S base ε ε) (Ioo (0 : ℝ) 2 ×ˢ univ)
      (W.negativeRootPrefixField m side odd (W.negativeChartRootScale e C m side)) := by
  have hδ := (W.negativeChartRootScale_bounds e A.scale m side).1
  have hband := A.scale_component m side
  have hsub := sectorNeighborhood_mono W.S A.base_le A.ε_le A.ε_le
  have hU := isOpen_sectorNeighborhood W.S base ε ε
  cases odd with
  | false =>
    exact (n04Realization_jointMixedRegularity
      (W.negativeRootAngleDefectJointTower m side hδ hband)
      (isOpen_sectorNeighborhood W.S W.base W.ε W.ε) (isOpen_Ioo.prod isOpen_univ)
      ((sectorNeighborhood_convex W.S W.base W.ε W.ε).prod
        ((convex_Ioo _ _).prod convex_univ))).height_restrict hU hsub
  | true =>
    exact (W.negativeRootTravelCoefficientMixedRegularity m side hδ hband).height_restrict hU hsub

include A in
theorem RootCoordinatePrefixData.coefficient_pos (m : ℕ) (side : Bool)
    {z : Parameter W.S} (hz : z ∈ sectorNeighborhood W.S base ε ε)
    {q : PolarPoint} (hq : q ∈ Ioo (0 : ℝ) 2 ×ˢ (univ : Set ℝ)) :
    0 < W.negativeRootTravelCoefficient m side (W.negativeChartRootScale e C m side) z q :=
  W.negativeRootTravelCoefficient_pos m side
    (W.negativeChartRootScale_bounds e A.scale m side).1 (A.scale_component m side)
    (sectorNeighborhood_mono W.S A.base_le A.ε_le A.ε_le hz) hq.1

def negativeRootPowerCoordinate (W : N04RealizationStart) (m : ℕ) (side radial : Bool)
    (δ : ℝ) (z : Parameter W.S) (q : PolarPoint) : ℝ :=
  if radial then q.1 * W.negativeRootTravelCoefficient m side δ z q ^ (2 / 3 : ℝ)
    else W.negativeRootAngleDefect m side δ z q

def RootCoordinatePrefixData.powerRegularity (m : ℕ) (side : Bool) :
    MixedJetRegularity (sectorNeighborhood W.S base ε ε) (Ioo (0 : ℝ) 2 ×ˢ univ)
      (fun z q => W.negativeRootTravelCoefficient m side
        (W.negativeChartRootScale e C m side) z q ^ (2 / 3 : ℝ)) :=
  (A.regularity m side true).scalarComp
    (isOpen_sectorNeighborhood W.S base ε ε) (isOpen_Ioo.prod isOpen_univ) isOpen_Ioi
    (fun x hx => (Real.contDiffAt_rpow_const_of_ne (ne_of_gt hx)).contDiffWithinAt)
    (fun z hz q hq => A.coefficient_pos m side hz hq)

def RootCoordinatePrefixData.coordinateRegularity (m : ℕ) (side radial : Bool) :
    MixedJetRegularity (sectorNeighborhood W.S base ε ε) (Ioo (0 : ℝ) 2 ×ˢ univ)
      (W.negativeRootPowerCoordinate m side radial (W.negativeChartRootScale e C m side)) := by
  cases radial with
  | false => exact A.regularity m side false
  | true =>
      exact (n04Realization_mixedJetRegularity_fixedSpatial
        (isOpen_sectorNeighborhood W.S base ε ε) contDiff_fst.contDiffOn).mul
        (A.powerRegularity m side) (isOpen_sectorNeighborhood W.S base ε ε)
        (isOpen_Ioo.prod isOpen_univ)

include A in
theorem RootCoordinatePrefixData.chart_factorization (m : ℕ) (side radial : Bool)
    {z : Parameter W.S} (hz : z ∈ sectorNeighborhood W.S base ε ε)
    {q : PolarPoint} (hq : q ∈ Ioo (0 : ℝ) 2 ×ˢ (univ : Set ℝ)) :
    (if radial then
      (n04bActualNegativeChart W.hT W.hS W.through03 W.field (liftSectorParameter W.S W.C z)
        m side (W.negativeInwardPoint m side (W.negativeChartRootScale e C m side * q.1, q.2))).1
    else
      (n04bActualNegativeChart W.hT W.hS W.through03 W.field (liftSectorParameter W.S W.C z)
        m side (W.negativeInwardPoint m side (W.negativeChartRootScale e C m side * q.1, q.2))).2) -
      (if radial then 0 else q.2) =
    (if radial then (3 / 2 : ℝ) ^ (2 / 3 : ℝ) else 1) *
      W.negativeRootPowerCoordinate m side radial (W.negativeChartRootScale e C m side) z q := by
  have hzW := sectorNeighborhood_mono W.S A.base_le A.ε_le A.ε_le hz
  have hp := W.negativeScaledPoint_mem_component m side
    (W.negativeChartRootScale_bounds e A.scale m side).1 (A.scale_component m side) hq.1
  have he := ((n04bActualNegativeFunctions_spec W.hT W.hS W.through03 W.field
    (liftSectorParameter_mem_stateNeighborhood hzW le_rfl)
    (W.through03.1.1.2.2.1.liftSectorParameter_sector z) m side).component_chart_germ hp).self_of_nhds
  rw [he]
  cases radial with
  | false => simp only [Bool.false_eq_true, ↓reduceIte, negativeRootPowerCoordinate,
      one_mul, n04bRootPhysicalChart, n04bRootStripChart, negativeRootAngleDefect]
  | true =>
    let χ := W.negativeRootTravelCoefficient m side (W.negativeChartRootScale e C m side) z q
    have hχ : 0 < χ := A.coefficient_pos m side hz hq
    have htravel : n04bTravelOrientation (W.C.travel m) side
        (n04bActualTravelChart W.S W.C W.L (liftSectorParameter W.S W.C z) m
          (W.negativeInwardPoint m side (W.negativeChartRootScale e C m side * q.1, q.2))).1 =
        χ * q.1 ^ (3 / 2 : ℝ) := (div_mul_cancel₀ _
          (Real.rpow_pos_of_pos hq.1.1 (3 / 2 : ℝ)).ne').symm
    change (3 * _ / 2) ^ (2 / 3 : ℝ) - 0 = (3 / 2 : ℝ) ^ (2 / 3 : ℝ) * (q.1 * χ ^ (2 / 3 : ℝ))
    rw [htravel, sub_zero, show 3 * (χ * q.1 ^ (3 / 2 : ℝ)) / 2 =
      ((3 / 2 : ℝ) * χ) * q.1 ^ (3 / 2 : ℝ) by ring]
    rw [Real.mul_rpow (mul_nonneg (by norm_num) hχ.le) (Real.rpow_nonneg hq.1.1.le _),
      Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 3 / 2) hχ.le, ← Real.rpow_mul hq.1.1.le]
    norm_num <;> ring

private theorem fractional_oneHigh (p : ℕ → Seminorm ℝ (Parameter W.S))
    (base high k : ℕ) (z : Parameter W.S) (L : Parameter W.S [×k]→L[ℝ] ℝ)
    {M α : ℝ} (hM : 0 ≤ M) (hα : α ≤ 1)
    (hb : ∀ v : Fin k → Parameter W.S, (∀ i, p base (v i) ≤ 1) →
      ∀ R : ℝ, 1 ≤ R → p high z ≤ R → (∀ i, p high (v i) ≤ R) →
        ‖L v‖ ≤ M * R ^ α) (v : Fin k → Parameter W.S) :
    ‖L v‖ ≤ M * oneHighVariationWeight p base high z v := by
  have hh := multilinear_bound_of_unitBall L (normSeminorm ℝ ℝ) (p base) (p high)
    hM (a := 1 + p high z) (fun u hu => by
      let R : ℝ := (1 + p high z) + ∑ i, p high (u i)
      have hs : 0 ≤ ∑ i, p high (u i) := Finset.sum_nonneg (fun i _ => apply_nonneg _ _)
      have hR : 1 ≤ R := by dsimp only [R]; linarith [apply_nonneg (p high) z]
      have hzR : p high z ≤ R := by dsimp only [R]; linarith
      have huR (i : Fin k) : p high (u i) ≤ R :=
        (Finset.single_le_sum (fun j _ => apply_nonneg _ _) (Finset.mem_univ i)).trans
          (le_add_of_nonneg_left (by positivity))
      have h := (hb u (fun i => (hu i).le) R hR hzR huR).trans
        (mul_le_mul_of_nonneg_left (Real.rpow_le_self_of_one_le hR hα) hM)
      simpa only [coe_normSeminorm, R] using h)
  simpa only [coe_normSeminorm, multilinearTameSize, oneHighVariationWeight] using hh v

set_option diagnostics true in
include A in
/-- Positive powers and multiplication by the normalized radius keep
one height factor and the original parameter base. -/
theorem RootCoordinatePrefixData.normalized_positive_bounds :
    ∀ n : ℕ, 0 < n → ∃ loss : ℕ, ∀ s : ℕ, ∃ B : ℝ, 0 < B ∧
    ∀ m (side radial : Bool) (q : PolarPoint), q.1 ∈ Ioc (0 : ℝ) (σ m side) →
    ∀ a b : ℕ, a + b ≤ s →
    ∀ J : SmoothDirections (sectorNeighborhood W.S base ε ε)
      (fun z => mixedDerivative a b
        (W.negativeRootPowerCoordinate m side radial (W.negativeChartRootScale e C m side) z) q),
    ∀ z ∈ sectorNeighborhood W.S base ε ε, ∀ v : Fin n → Parameter W.S,
      |J.D n z v| ≤ B * W.T.E0 (W.negativeHalfSample e m side) ^ B *
        W.T.H (W.negativeHalfSample e m side) ^ (3 / 4 : ℝ) *
          oneHighVariationWeight (parameterGrading W.S) base (s + loss) z v := by
  let l := A.values.choose
  let Au := A.values.choose_spec.choose
  let P := A.values.choose_spec.choose_spec.choose
  let Q := A.values.choose_spec.choose_spec.choose_spec.choose
  have hv := A.values.choose_spec.choose_spec.choose_spec.choose_spec
  have hheight := materialHeight_E0_weight_bounded W.hT (γ := (3 / 4 : ℝ)) (by norm_num) 0
  let RH := hheight.choose
  intro n hn
  have hpref := A.«prefix» n hn
  let shift := hpref.choose
  refine ⟨base + shift * n + 1, fun s => ?_⟩
  have hraw := hpref.choose_spec s
  let Bf := hraw.choose
  have hBf : 0 < Bf := hraw.choose_spec.1
  have hb := hraw.choose_spec.2
  have hpower := n04NegativeChart_positivePower_positive_oneHigh
    (X := Parameter W.S) n s shift RH (2 / 3 : ℝ)
    hv.1 hv.2.1 hv.2.2.1 hv.2.2.2.1 hBf.le hBf.le
  let Bp := hpower.choose
  have hBp : 0 < Bp := hpower.choose_spec.1
  have hpow := hpower.choose_spec.2
  have henv := coefficientEnvelope_pack ((2 : ℝ) ^ s * Bp + Bf) (Bp + Bf)
  let B := henv.choose
  have hB := henv.choose_spec.1
  have hpack := henv.choose_spec.2
  refine ⟨B, hB, fun m side radial q hq a b hab J z hz v => ?_⟩
  rw [← show base + s + shift * n + 1 = s + (base + shift * n + 1) by omega]
  let U := sectorNeighborhood W.S base ε ε
  let Ω := Ioo (0 : ℝ) 2 ×ˢ (univ : Set ℝ)
  let E := W.T.E0 (W.negativeHalfSample e m side)
  let H := W.T.H (W.negativeHalfSample e m side) ^ (3 / 4 : ℝ)
  let V := oneHighVariationWeight (parameterGrading W.S) base (base + s + shift * n + 1) z v
  have hE : 1 ≤ E := W.floor _
  have hH : 0 ≤ H := Real.rpow_nonneg (W.hT.2.1 _
    (materialSample_mem_radialCore W.hT W.radial.1.choose_spec.2.1 _)).2.1.le _
  have hHR : H ≤ RH := by
    simpa only [Real.rpow_zero, mul_one] using hheight.choose_spec.2
      (W.negativeHalfSample e m side)
        (materialSample_mem_radialCore W.hT W.radial.1.choose_spec.2.1 _)
  have hV : 0 ≤ V := oneHighVariationWeight_nonneg _ _ _ _ _
  have hq₂ : q ∈ Ω := ⟨⟨hq.1, (hq.2.trans (A.band m side).2).trans_lt (by norm_num)⟩, mem_univ _⟩
  have hlow := n04NegativeHeight_parameterGrading_le_one A.ε_small hz
  have hcmpP : (2 : ℝ) ^ s * Bp * E ^ Bp ≤ B * E ^ B :=
    (mul_le_mul (le_add_of_nonneg_right hBf.le)
      (Real.rpow_le_rpow_of_exponent_le hE (le_add_of_nonneg_right hBf.le))
      (Real.rpow_nonneg (zero_le_one.trans hE) _) (by positivity)).trans (hpack E hE)
  have hcmpF : Bf * E ^ Bf ≤ B * E ^ B :=
    (mul_le_mul (le_add_of_nonneg_left (by positivity : 0 ≤ (2 : ℝ) ^ s * Bp))
      (Real.rpow_le_rpow_of_exponent_le hE (le_add_of_nonneg_left hBp.le))
      (Real.rpow_nonneg (zero_le_one.trans hE) _) (by positivity)).trans (hpack E hE)
  cases radial with
  | false =>
    have hm : 0 ≤ Bf * E ^ Bf * H := by positivity
    have hnorm := fractional_oneHigh (parameterGrading W.S) base
      (base + s + shift * n + 1) n z (J.D n z) hm
      (spatialOrder_fraction_le_one (Nat.add_le_add_right hab (shift * n)))
      (fun w hw R hR hzR hwR => by
        simpa only [parameterHeightWeight, if_neg (Nat.ne_of_gt hn)] using
          hb m side false q hq n le_rfl a b hab J z hz w hw R hR hzR hwR) v
    have hfinal := hnorm.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hcmpF hH) hV)
    simpa only [Real.norm_eq_abs] using hfinal
  | true =>
    let F := A.regularity m side true
    let R := A.powerRegularity m side
    have hpowerBound (u w : ℕ) (huw : u + w ≤ s) :
        |(R.parameter u w q hq₂).D n z v| ≤ Bp * E ^ Bp * H * V := by
      have h := hpow (parameterGrading W.S) 0 base (base + s + shift * n + 1)
        U (isOpen_sectorNeighborhood W.S base ε ε) Ω (isOpen_Ioo.prod isOpen_univ)
        (W.negativeRootTravelCoefficient m side (W.negativeChartRootScale e C m side)) F
        (fun y hy p hp => A.coefficient_pos m side hy hp) q hq₂ E H hE hH hHR z hz
        (by simpa only [sub_zero] using hlow)
        (hv.2.2.2.2 m side z hz q hq).1 (hv.2.2.2.2 m side z hz q hq).2
        (fun j hj u w huw dirs hdirs R₀ hR₀ hzR hdR => by
          simpa only [sub_zero] using hb m side true q hq j hj u w huw
            (F.parameter u w q hq₂) z hz dirs hdirs R₀ hR₀
              (by simpa only [sub_zero] using hzR) hdR)
        n le_rfl hn u w huw (R.parameter u w q hq₂) v
      simpa only [sub_zero, Real.norm_eq_abs] using h
    have hrad := n04NegativeChart_radialProduct_parameterJet_bound
      (isOpen_Ioo.prod isOpen_univ) R a b s n hab hq₂
      (by simpa only [abs_of_pos hq.1] using hq.2.trans (A.band m side).2)
      J hz v (by positivity : 0 ≤ Bp * E ^ Bp * H * V) hpowerBound
    calc
      _ ≤ (2 : ℝ) ^ s * (Bp * E ^ Bp * H * V) := hrad
      _ = ((2 : ℝ) ^ s * Bp * E ^ Bp) * H * V := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hcmpP hH) hV

set_option diagnostics true in
include A in
/-- Undo the fixed inward scale at the end. Its inverse pays only a
material power; the high parameter order keeps spatial coefficient one. -/
theorem RootCoordinatePrefixData.physical_positive_bounds :
    ∀ n : ℕ, 0 < n → ∃ loss : ℕ, ∀ s : ℕ, ∃ B : ℝ, 0 < B ∧
    ∀ m (side radial : Bool) (q : PolarPoint), q.1 ∈ Ioo (0 : ℝ) (σ m side) →
    ∀ a b : ℕ, a + b ≤ s →
    ∀ J : SmoothDirections (sectorNeighborhood W.S base ε ε)
      (fun z => mixedDerivative a b (fun p => if radial then
        (n04bActualNegativeChart W.hT W.hS W.through03 W.field
          (liftSectorParameter W.S W.C z) m side p).1
        else (n04bActualNegativeChart W.hT W.hS W.through03 W.field
          (liftSectorParameter W.S W.C z) m side p).2)
        (W.negativeInwardPoint m side (W.negativeChartRootScale e C m side * q.1, q.2))),
    ∀ z ∈ sectorNeighborhood W.S base ε ε, ∀ v : Fin n → Parameter W.S,
      |J.D n z v| ≤ B * W.T.E0 (W.negativeHalfSample e m side) ^ B *
        W.T.H (W.negativeHalfSample e m side) ^ (3 / 4 : ℝ) *
          oneHighVariationWeight (parameterGrading W.S) base (s + loss) z v := by
  have hscale := W.negativeChartRootScale_inverse_material e A.scale
  let D := hscale.choose
  let P := hscale.choose_spec.choose
  have hD := hscale.choose_spec.choose_spec.1
  have hcost := hscale.choose_spec.choose_spec.2.2
  let S : ℝ := 1 + (3 / 2 : ℝ) ^ (2 / 3 : ℝ)
  have hS : 0 < S := by dsimp only [S]; positivity
  intro n hn
  have hnB := A.normalized_positive_bounds n hn
  let loss := hnB.choose
  refine ⟨loss, fun s => ?_⟩
  have hs := hnB.choose_spec s
  let Bg := hs.choose
  have hBg : 0 < Bg := hs.choose_spec.1
  have hb := hs.choose_spec.2
  have henv := coefficientEnvelope_pack (S * D ^ s * Bg) (P * (s : ℝ) + Bg)
  let B := henv.choose
  refine ⟨B, henv.choose_spec.1, fun m side radial q hq a b hab J z hz v => ?_⟩
  let δ := W.negativeChartRootScale e C m side
  let c := n01ComponentRootOrientation side * δ
  let d : ℝ := if radial then (3 / 2 : ℝ) ^ (2 / 3 : ℝ) else 1
  let h : PolarPoint → ℝ := fun p => if radial then 0 else p.2
  let U := sectorNeighborhood W.S base ε ε
  let Ω := Ioo (W.C.left m) (W.C.right m) ×ˢ (univ : Set ℝ)
  let f : Parameter W.S → PolarPoint → ℝ := fun x p => if radial then
    (n04bActualNegativeChart W.hT W.hS W.through03 W.field
      (liftSectorParameter W.S W.C x) m side p).1 else
    (n04bActualNegativeChart W.hT W.hS W.through03 W.field
      (liftSectorParameter W.S W.C x) m side p).2
  have hd : 0 < d := by cases radial <;> dsimp only [d] <;> positivity
  have hδ := W.negativeChartRootScale_bounds e A.scale m side
  have hcabs : |c| = δ := by
    have ho : |n01ComponentRootOrientation side| = 1 := by
      cases side <;> norm_num [n01ComponentRootOrientation]
    change |n01ComponentRootOrientation side * δ| = δ
    rw [abs_mul, ho, abs_of_pos hδ.1, one_mul]
  have hc : c ≠ 0 := abs_pos.mp (hδ.1.trans_eq hcabs.symm)
  have hpoint (p : PolarPoint) :
      (n01ComponentRoot W.C m side + c * p.1, p.2) =
        W.negativeInwardPoint m side (δ * p.1, p.2) := by
    rw [W.negativeInwardPoint_root_add]
    simp only [c, mul_assoc]
  have hmap : MapsTo (fun p : PolarPoint =>
      (n01ComponentRoot W.C m side + c * p.1, p.2)) unitStrip Ω := by
    intro p hp
    change (n01ComponentRoot W.C m side + c * p.1, p.2) ∈ Ω
    rw [hpoint]
    exact W.negativeScaledPoint_mem_component m side hδ.1 (A.scale_component m side)
      ⟨hp.1.1, hp.1.2.trans (by norm_num)⟩
  have hqU : q ∈ unitStrip := ⟨⟨hq.1, hq.2.trans_le (A.band m side).2⟩, mem_univ _⟩
  have hq₂ : q ∈ Ioo (0 : ℝ) 2 ×ˢ (univ : Set ℝ) :=
    ⟨⟨hq.1, hqU.1.2.trans (by norm_num)⟩, mem_univ _⟩
  have hf (x : Parameter W.S) (hx : x ∈ U) : ContDiffOn ℝ ∞ (f x) Ω := by
    have hxW := sectorNeighborhood_mono W.S A.base_le A.ε_le A.ε_le hx
    cases radial with
    | false => exact (W.negativeChartMixedRegularity m side (ContinuousLinearMap.snd ℝ ℝ ℝ)).spatial x hxW
    | true => exact (W.negativeChartMixedRegularity m side (ContinuousLinearMap.fst ℝ ℝ ℝ)).spatial x hxW
  have hh : ContDiffOn ℝ ∞ h unitStrip := by
    cases radial <;> first | exact contDiff_snd.contDiffOn | exact contDiffOn_const
  let Jg := (A.coordinateRegularity m side radial).parameter a b q hq₂
  let JP : SmoothDirections U (fun x => mixedDerivative a b (f x)
      (n01ComponentRoot W.C m side + c * q.1, q.2)) :=
    J.congrOn (fun x _ => congrArg (mixedDerivative a b (f x)) (hpoint q).symm)
  have hfactor (x : Parameter W.S) (hx : x ∈ U) (p : PolarPoint) (hp : p ∈ unitStrip) :
      W.negativeRootPowerCoordinate m side radial δ x p =
        d⁻¹ * (f x (n01ComponentRoot W.C m side + c * p.1, p.2) - h p) := by
    have ht := A.chart_factorization m side radial hx
      (show p ∈ Ioo (0 : ℝ) 2 ×ˢ (univ : Set ℝ) from
        ⟨⟨hp.1.1, hp.1.2.trans (by norm_num)⟩, mem_univ _⟩)
    change f x (W.negativeInwardPoint m side (δ * p.1, p.2)) - h p =
      d * W.negativeRootPowerCoordinate m side radial δ x p at ht
    rw [← hpoint p] at ht
    rw [ht, ← mul_assoc, inv_mul_cancel₀ hd.ne', one_mul]
  let K : SmoothDirections U (fun x => mixedDerivative a b
      (fun p : PolarPoint => d⁻¹ * (f x (n01ComponentRoot W.C m side + c * p.1, p.2) - h p)) q) :=
    Jg.congrOn (fun x hx => mixedDerivative_congr_on_open
      (isOpen_Ioo.prod isOpen_univ) (fun p hp => hfactor x hx p hp) a b hqU)
  have hjet : Jg.D n z v = (c ^ a / d) * J.D n z v :=
    n04NegativeChart_coordinatePullback_positiveJet (isOpen_sectorNeighborhood W.S base ε ε)
      (n01ComponentRoot W.C m side) c d h hh hf hmap a b hqU JP K hn hz v
  have hj : J.D n z v = (d / c ^ a) * Jg.D n z v := by
    have hcancel (r : ℝ) : (d / c ^ a) * ((c ^ a / d) * r) = r := by
      field_simp [hc, hd.ne'] <;> ring
    exact ((congrArg (fun r : ℝ => (d / c ^ a) * r) hjet).trans (hcancel _)).symm
  let E := W.T.E0 (W.negativeHalfSample e m side)
  let H := W.T.H (W.negativeHalfSample e m side) ^ (3 / 4 : ℝ)
  let V := oneHighVariationWeight (parameterGrading W.S) base (s + loss) z v
  have hE : 1 ≤ E := W.floor _
  have hEp : 0 < E := zero_lt_one.trans_le hE
  have hH : 0 ≤ H := Real.rpow_nonneg (W.hT.2.1 _
    (materialSample_mem_radialCore W.hT W.radial.1.choose_spec.2.1 _)).2.1.le _
  have hV : 0 ≤ V := oneHighVariationWeight_nonneg _ _ _ _ _
  have hinv : 1 ≤ δ⁻¹ := (one_le_inv₀ hδ.1).2 hδ.2.1
  have hpow : (δ⁻¹) ^ a ≤ D ^ s * E ^ (P * (s : ℝ)) := by
    apply (pow_le_pow_right₀ hinv (show a ≤ s by omega)).trans
    have hp := pow_le_pow_left₀ (inv_nonneg.mpr hδ.1.le) (hcost m side) s
    simpa only [mul_pow, ← Real.rpow_mul_natCast hEp.le] using hp
  have hdS : |d| ≤ S := by
    rw [abs_of_pos hd]
    cases radial with
    | false => exact le_add_of_nonneg_right (Real.rpow_nonneg (by norm_num) _)
    | true => exact le_add_of_nonneg_left zero_le_one
  have hcoef : |d / c ^ a| ≤ (S * D ^ s) * E ^ (P * (s : ℝ)) := by
    rw [abs_div, abs_pow, hcabs, div_eq_mul_inv, ← inv_pow]
    exact (mul_le_mul hdS hpow (pow_nonneg (inv_nonneg.mpr hδ.1.le) _) hS.le).trans_eq
      (mul_assoc _ _ _).symm
  have hnorm := hb m side radial q ⟨hq.1, hq.2.le⟩ a b hab Jg z hz v
  calc
    |J.D n z v| = |d / c ^ a| * |Jg.D n z v| := by rw [hj, abs_mul]
    _ ≤ ((S * D ^ s) * E ^ (P * (s : ℝ))) * (Bg * E ^ Bg * H * V) :=
      mul_le_mul hcoef hnorm (abs_nonneg _) (by positivity)
    _ = ((S * D ^ s * Bg) * E ^ (P * (s : ℝ) + Bg)) * H * V := by
      rw [Real.rpow_add hEp]
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (henv.choose_spec.2 E hE) hH) hV

end N04RealizationStart
end ContinuousFlexibility.Analysis

/-- info: 'ContinuousFlexibility.Analysis.N04RealizationStart.RootCoordinatePrefixData.physical_positive_bounds'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ContinuousFlexibility.Analysis.N04RealizationStart.RootCoordinatePrefixData.physical_positive_bounds
