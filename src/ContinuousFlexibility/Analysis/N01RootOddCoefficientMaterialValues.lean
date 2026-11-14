module

public import ContinuousFlexibility.Analysis.N01RootSpeedPowerMaterialJets
public import ContinuousFlexibility.Analysis.RootFlowParameterUnscale
public import ContinuousFlexibility.Analysis.N01RootFieldLocalization
public import ContinuousFlexibility.Analysis.N01RootLabels
public import ContinuousFlexibility.Analysis.RootChartExtension
public import ContinuousFlexibility.Analysis.ActualRootChart

/-!
# The actual odd root coefficient and its reciprocal

The true unit-parameter flow gives chi=(2/3)c*label'. The original label
derivative lies between one quarter and four. Thus the already derived
material costs of c and its reciprocal control the same genuine odd
extension at the root, without charging either localization radius.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set ContinuousFlexibility.Statements
open scoped ContDiff

private theorem oddRoot_value_inverse_of_speed
    {c a : ℝ} (hc : 0 < c) (ha : a ∈ Icc (1 / 4 : ℝ) 4) :
    0 < ((2 : ℝ) / 3) * c * a ∧
      ((2 : ℝ) / 3) * c * a ≤ 3 * c ∧
      (((2 : ℝ) / 3) * c * a)⁻¹ ≤ 6 * c⁻¹ := by
  have ha0 : 0 < a := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1 / 4) ha.1
  have hpos := mul_pos (mul_pos (by norm_num : (0 : ℝ) < 2 / 3) hc) ha0
  have hlo : c / 6 ≤ ((2 : ℝ) / 3) * c * a := by
    nlinarith only [mul_le_mul_of_nonneg_left ha.1 hc.le]
  have hhi : ((2 : ℝ) / 3) * c * a ≤ 3 * c := by
    nlinarith only [mul_le_mul_of_nonneg_left ha.2 hc.le, hc]
  have hi := inv_anti₀ (div_pos hc (by norm_num : (0 : ℝ) < 6)) hlo
  refine ⟨hpos, hhi, ?_⟩
  calc
    _ ≤ (c / 6)⁻¹ := hi
    _ = 6 * c⁻¹ := by rw [inv_div, div_eq_mul_inv]

/-- Real bookkeeping for a zeroth jet with the state grading kept abstract. -/
private theorem le_two_mul_of_norm_jet_zero {f : PolarPoint → ℝ} {q : PolarPoint}
    {v B W : ℝ} {P : ℕ → ℝ} {k k' : ℕ} (hk : k' = k)
    (hb : ‖iteratedFDeriv ℝ 0 f q‖ ≤ B * W ^ B * (1 + P k')) (hfv : f q = v)
    (hv : 0 ≤ v) (ht : P k ≤ 1) (hB : 0 ≤ B) (hW : 1 ≤ W) :
    v ≤ 2 * B * W ^ B := by
  rw [hk, norm_iteratedFDeriv_zero, hfv, Real.norm_of_nonneg hv] at hb
  have hBW : 0 ≤ B * W ^ B := mul_nonneg hB (Real.rpow_nonneg (zero_le_one.trans hW) _)
  have h := mul_le_mul_of_nonneg_left ht hBW
  nlinarith only [hb, h]

theorem n01_rootOddCoefficient_unit_material_values_of_component_optical
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {base loss : ℕ} {ε K : ℝ}
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    (hN : N01Properties D T S C base loss ε)
    (hflow : OrdinaryFlowJacobianBounds S C base ε) (hK : 0 < K) :
    ∃ C0 : ℝ, ∃ low : ℕ, ∃ P : ℝ, 1 ≤ C0 ∧
      (∀ j, 1 ≤ C0 * T.E0 (T.sample j)) ∧ 1 ≤ P ∧
      ∀ z ∈ stateNeighborhood S C base ε, stateSector S z.1 →
        pairGrading (stateGrading S) realGrading low (z - (C.referenceState, 0)) ≤ 1 →
      ∀ m j : ℕ, Ioo (C.left m) (C.right m) ⊆ D.cells j →
      (∀ x ∈ Ioo (C.left m) (C.right m),
        K⁻¹ * T.E0 (T.sample j) ^ (-K) * min (x - C.left m) (C.right m - x) ≤
          -deriv D.w x / (x * D.w x)) →
      ∀ (side : Bool) (g : ℝ → ℝ), ContDiff ℝ ∞ g →
      (∀ x, -deriv D.w (n01ComponentRoot C m side +
        n01ComponentRootOrientation side * x) = x * g x) →
      ∀ R : ℝ, ∀ hR : 0 < R,
      RootCoefficientStripConditions D.w g (stateProfile D S C z.1)
        (stateHeight D S C z) (n01ComponentRoot C m side)
        (n01ComponentRootOrientation side) R →
      ∀ δ : ℝ, δ ≠ 0 → ∀ Θ : (ℝ × ℝ) → ℝ → ℝ → ℝ,
      N04FlowEquations (rootRescaledField
        (localizedRootDrift D S C (n01ComponentRoot C m side)
          (n01ComponentRootOrientation side) hR z)
        (localizedRootSpeed D S C g (n01ComponentRoot C m side)
          (n01ComponentRootOrientation side) hR z) δ) Θ →
      ∀ θ : ℝ,
        let G := rootInverseCoordinate (rootFlowParameterUnscale Θ δ)
          (n01RootLabel S C z m side)
        0 < extendedRootOddCoefficient G (0, θ) ∧
          extendedRootOddCoefficient G (0, θ) ≤
            P * (C0 * T.E0 (T.sample j)) ^ P ∧
          (extendedRootOddCoefficient G (0, θ))⁻¹ ≤
            P * (C0 * T.E0 (T.sample j)) ^ P := by
  refine (n01_rootSpeed_axis_rpow_material_jets_of_component_optical hS hT hN hK).elim ?_
  intro C0 hS1
  refine hS1.elim ?_
  intro low hS2
  refine hS2.elim ?_
  intro lossS hS3
  have hC0 := hS3.1
  have hfloor := hS3.2.1
  have hpowers := hS3.2.2
  refine (hpowers 1).elim ?_
  intro BP hBPplus
  have hBP := hBPplus.1
  have hplus := hBPplus.2
  refine (hpowers (-1)).elim ?_
  intro BM hBMminus
  have hBM := hBMminus.1
  have hminus := hBMminus.2
  have hp : Monotone (pairGrading (stateGrading S) realGrading) :=
    tamePairGrading_monotone (stateGrading_monotone S) (fun _ _ _ => le_rfl)
  let P : ℝ := 1 + 12 * BP 0 + 12 * BM 0
  have hP : 1 ≤ P := by dsimp only [P]; linarith only [hBP 0, hBM 0]
  have hBPexp : BP 0 ≤ P := by dsimp only [P]; linarith only [hBP 0, hBM 0]
  have hBMexp : BM 0 ≤ P := by dsimp only [P]; linarith only [hBP 0, hBM 0]
  have hBPcoef : 6 * BP 0 ≤ P := by dsimp only [P]; linarith only [hBP 0, hBM 0]
  have hBMcoef : 12 * BM 0 ≤ P := by dsimp only [P]; linarith only [hBP 0, hBM 0]
  refine ⟨C0, max low lossS, P, hC0, hfloor, hP, ?_⟩
  intro z hz hs hlow m j hhost hoptical side g hg hfactor R hR hstrip δ hδ Θ hΘ θ
  have hzlow := (hp (le_max_left low lossS) _).trans hlow
  have hzloss := (hp (le_max_right low lossS) _).trans hlow
  let W : ℝ := C0 * T.E0 (T.sample j)
  have hW : 1 ≤ W := hfloor j
  let r : ℝ := n01ComponentRoot C m side
  let σ : ℝ := n01ComponentRootOrientation side
  let d : PolarPoint → ℝ := localizedRootDrift D S C r σ hR z
  let c : PolarPoint → ℝ := localizedRootSpeed D S C g r σ hR z
  let v : ℝ := factoredCharacteristicSpeed D.w g (stateProfile D S C z.1)
    (stateHeight D S C z) r σ (0, θ)
  let l : ℝ → ℝ := n01RootLabel S C z m side
  let Θ₁ : (ℝ × ℝ) → ℝ → ℝ → ℝ := rootFlowParameterUnscale Θ δ
  let G : ℝ × ℝ × ℝ → ℝ := rootInverseCoordinate Θ₁ l
  have hregular := contDiff_localizedRootFields_of_n01 hS hT hN
    (g := g) (r := r) (σ := σ) (z := z) hg hR hstrip
  have hperiod := periodic_localizedRootFields hS C g r σ hR z
  have hfield := contDiff_rootRegularizedField hregular.1 hregular.2
  have hfieldPeriod := rootRegularizedField_periodic hperiod.1 hperiod.2
  have hΘ₁ : N04FlowEquations (rootRegularizedField d c) Θ₁ :=
    rootFlowParameterUnscale_equations (d := d) (c := c) (Θ := Θ) hδ hΘ
  have ht : (1 : ℝ) ∈ Icc 0 1 := ⟨zero_le_one, le_rfl⟩
  have hEndpoint : ContDiff ℝ ∞ (fun q : (ℝ × ℝ) × ℝ => Θ₁ q.1 1 q.2) :=
    n04Flow_contDiff_slice hfield hfieldPeriod hΘ₁ ht
  have hpositive : ∀ p θ, 0 < deriv (fun η => Θ₁ p 1 η) θ :=
    fun p θ => n04Flow_angular_deriv_pos hfield hfieldPeriod hΘ₁ ht p θ
  have hendpointPeriod : ∀ p θ, Θ₁ p 1 (θ + Real.pi) = Θ₁ p 1 θ + Real.pi :=
    fun p θ => n04Flow_period_add hfield hfieldPeriod hΘ₁ p θ ht
  have hzero : ((0, θ) : PolarPoint) ∈ Ioo (-R - R) (R + R) ×ˢ (univ : Set ℝ) := by
    refine ⟨⟨?_, ?_⟩, mem_univ _⟩ <;> linarith only [hR]
  have hdata := hstrip (0, θ) hzero
  have hv : 0 < v := factoredCharacteristicSpeed_pos
    hdata.1 hdata.2.1 hdata.2.2.1 hdata.2.2.2.1 hdata.2.2.2.2.1
  have hcvalue : c (0, θ) = v := by
    change rootFieldLocalization
      (factoredCharacteristicSpeed D.w g (stateProfile D S C z.1)
        (stateHeight D S C z) r σ) hR (0, θ) = _
    apply rootFieldLocalization_eqOn hR
    refine ⟨⟨?_, ?_⟩, mem_univ _⟩ <;> linarith only [hR]
  have hχeq : extendedRootOddCoefficient G (0, θ) =
      ((2 : ℝ) / 3) * v * deriv l θ := by
    rw [extendedRootOddCoefficient_of_nonneg G (by norm_num : (0 : ℝ) ≤ 0)]
    have he : rootOddCoefficient G (0, θ) =
        ((2 : ℝ) / 3) * c (0, θ) * deriv l θ :=
      rootOddCoefficient_rootInverseCoordinate_zero Real.pi_ne_zero hregular.2
        hΘ₁.1 hΘ₁.2 (n04Flow_joint_continuousOn hfield hfieldPeriod hΘ₁)
        hEndpoint hpositive hendpointPeriod (n01RootLabel_contDiff hS hT hN hz hs m side) θ
    change rootOddCoefficient G (0, θ) = _
    rw [he, hcvalue]
  have hscalar := oddRoot_value_inverse_of_speed hv
    (n01RootLabel_deriv_mem_quarter_four hN hflow hz hs m side θ)
  have hvalue : v ≤ 2 * BP 0 * W ^ (BP 0) :=
    le_two_mul_of_norm_jet_zero
      (P := fun k => pairGrading (stateGrading S) realGrading k (z - (C.referenceState, 0)))
      (Nat.zero_add lossS)
      (hplus z hz hs hzlow m j hhost hoptical side g hg hfactor R hR hstrip θ 0)
      (Real.rpow_one _) hv.le hzloss (hBP 0).le hW
  have hinverse : v⁻¹ ≤ 2 * BM 0 * W ^ (BM 0) :=
    le_two_mul_of_norm_jet_zero
      (P := fun k => pairGrading (stateGrading S) realGrading k (z - (C.referenceState, 0)))
      (Nat.zero_add lossS)
      (hminus z hz hs hzlow m j hhost hoptical side g hg hfactor R hR hstrip θ 0)
      (Real.rpow_neg_one _) (inv_nonneg.mpr hv.le) hzloss (hBM 0).le hW
  change 0 < extendedRootOddCoefficient G (0, θ) ∧ _
  rw [hχeq]
  refine ⟨hscalar.1, ?_, ?_⟩
  · calc
      _ ≤ 3 * v := hscalar.2.1
      _ ≤ 3 * (2 * BP 0 * W ^ (BP 0)) :=
        mul_le_mul_of_nonneg_left hvalue (by norm_num : (0 : ℝ) ≤ 3)
      _ = (6 * BP 0) * W ^ (BP 0) := by ring
      _ ≤ P * W ^ P := mul_le_mul hBPcoef
        (Real.rpow_le_rpow_of_exponent_le hW hBPexp)
        (Real.rpow_nonneg (zero_le_one.trans hW) _) (zero_le_one.trans hP)
  · calc
      _ ≤ 6 * v⁻¹ := hscalar.2.2
      _ ≤ 6 * (2 * BM 0 * W ^ (BM 0)) :=
        mul_le_mul_of_nonneg_left hinverse (by norm_num : (0 : ℝ) ≤ 6)
      _ = (12 * BM 0) * W ^ (BM 0) := by ring
      _ ≤ P * W ^ P := mul_le_mul hBMcoef
        (Real.rpow_le_rpow_of_exponent_le hW hBMexp)
        (Real.rpow_nonneg (zero_le_one.trans hW) _) (zero_le_one.trans hP)

end ContinuousFlexibility.Analysis
