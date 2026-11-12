import ContinuousFlexibility.Analysis.N01RootEvenOddAxisMaterialJets
import ContinuousFlexibility.Analysis.N01RootOddCoefficientMaterialValues
import ContinuousFlexibility.Analysis.PositivePowerPolynomialMaterialJets

/-!
# Actual odd-coefficient powers at the root

The genuine odd extension has a derived material jet tower, positive
value and reciprocal at the same root. The scalar power calculus has
explicit polynomial costs, so its common low order and loss precede
the real exponent. No interval of possible values is chosen afterward.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set ContinuousFlexibility.Statements
open scoped ContDiff

theorem n01_rootOddCoefficient_unit_rpow_material_jets_of_component_optical
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {base loss : ℕ} {ε K : ℝ}
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    (hN : N01Properties D T S C base loss ε)
    (hflow : OrdinaryFlowJacobianBounds S C base ε) (hK : 0 < K) :
    ∃ C0 : ℝ, ∃ low outLoss : ℕ, 1 ≤ C0 ∧
      (∀ j, 1 ≤ C0 * T.E0 (T.sample j)) ∧
      ∀ γ : ℝ, ∃ B : ℕ → ℝ, (∀ n, 0 < B n) ∧
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
      ∀ θ : ℝ, ∀ n : ℕ,
        let G := rootInverseCoordinate (rootFlowParameterUnscale Θ δ)
          (n01RootLabel S C z m side)
        ‖iteratedFDeriv ℝ n (fun p => extendedRootOddCoefficient G p ^ γ) (0, θ)‖ ≤
          B n * (C0 * T.E0 (T.sample j)) ^ (B n) *
            (1 + pairGrading (stateGrading S) realGrading (n + outLoss)
              (z - (C.referenceState, 0))) := by
  have hp : Monotone (pairGrading (stateGrading S) realGrading) :=
    tamePairGrading_monotone (stateGrading_monotone S) (fun _ _ _ => le_rfl)
  have hI := coordinate_hasInterpolation_pair (stateGrading_monotone S)
    (fun _ _ _ => le_rfl) (coordinate_hasInterpolation_stateGrading hS)
    coordinate_hasInterpolation_realGrading
  obtain ⟨CJ, lowJ, lossJ, hCJ, hfloorJ, BJ, hBJ, hjets⟩ :=
    n01_rootEvenOdd_unit_axis_material_jets_of_component_optical hS hT hN hflow hK
  obtain ⟨CV, lowV, PV, hCV, hfloorV, hPV, hvalues⟩ :=
    n01_rootOddCoefficient_unit_material_values_of_component_optical hS hT hN hflow hK
  let C0 : ℝ := max CJ CV
  have hC0 : 1 ≤ C0 := hCJ.trans (le_max_left _ _)
  have hE (j : ℕ) : 0 < T.E0 (T.sample j) :=
    (hT.2.1 _ (materialSample_mem_interval hN.1.1 hT j)).2.2.1
  have hfloor (j : ℕ) : 1 ≤ C0 * T.E0 (T.sample j) :=
    (hfloorJ j).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (hE j).le)
  obtain ⟨lowP, outLoss, hpowers⟩ :=
    positivePower_polynomial_material_bound (X := PolarPoint) hp hI lossJ
  let A : ℕ → ℝ := fun n => max 1 (BJ n)
  have hA (n : ℕ) : 1 ≤ A n := le_max_left _ _
  have hJA (n : ℕ) : BJ n ≤ A n := le_max_right _ _
  refine ⟨C0, max lowJ (max lowV lowP), outLoss, hC0, hfloor, ?_⟩
  intro γ
  obtain ⟨B, hB, hbound⟩ := hpowers γ PV hPV A hA
  refine ⟨B, hB, ?_⟩
  intro z hz hs hlow m j hhost hoptical side g hg hfactor R hR hstrip δ hδ Θ hΘ θ n
  have hzJ := (hp (le_max_left lowJ (max lowV lowP)) _).trans hlow
  have hzV := (hp ((le_max_left lowV lowP).trans
    (le_max_right lowJ (max lowV lowP))) _).trans hlow
  have hzP := (hp ((le_max_right lowV lowP).trans
    (le_max_right lowJ (max lowV lowP))) _).trans hlow
  let W : ℝ := C0 * T.E0 (T.sample j)
  have hW : 1 ≤ W := hfloor j
  have hWJ : CJ * T.E0 (T.sample j) ≤ W :=
    mul_le_mul_of_nonneg_right (le_max_left _ _) (hE j).le
  have hWV : CV * T.E0 (T.sample j) ≤ W :=
    mul_le_mul_of_nonneg_right (le_max_right _ _) (hE j).le
  let r : ℝ := n01ComponentRoot C m side
  let σ : ℝ := n01ComponentRootOrientation side
  let d : PolarPoint → ℝ := localizedRootDrift D S C r σ hR z
  let c : PolarPoint → ℝ := localizedRootSpeed D S C g r σ hR z
  let Θ₁ : (ℝ × ℝ) → ℝ → ℝ → ℝ := rootFlowParameterUnscale Θ δ
  let l : ℝ → ℝ := n01RootLabel S C z m side
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
  have hG : ContDiff ℝ ∞ G := contDiff_rootInverseCoordinate Real.pi_ne_zero
    hEndpoint hpositive hendpointPeriod (n01RootLabel_contDiff hS hT hN hz hs m side)
  have hGperiod : ∀ x ζ θ, G (x, ζ, θ + Real.pi) = G (x, ζ, θ) + Real.pi :=
    rootInverseCoordinate_period_add Real.pi_ne_zero hEndpoint hpositive hendpointPeriod
      (n01RootLabel_period_add hN hz hs m side)
  have hχ : ContDiff ℝ ∞ (extendedRootOddCoefficient G) :=
    contDiff_extendedRootOddCoefficient hG Real.pi_ne_zero
      (fun x _ => rootOddCoefficient_periodic hGperiod x)
  have hvalue := hvalues z hz hs hzV m j hhost hoptical side g hg hfactor R hR hstrip
    δ hδ Θ hΘ θ
  have hvalueMono : PV * (CV * T.E0 (T.sample j)) ^ PV ≤ PV * W ^ PV :=
    mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow (zero_le_one.trans (hfloorV j)) hWV (zero_le_one.trans hPV))
      (zero_le_one.trans hPV)
  refine hbound (z - (C.referenceState, 0)) hzP W hW
    (extendedRootOddCoefficient G) (0, θ) hχ.contDiffAt hvalue.1
    (hvalue.2.1.trans hvalueMono) (hvalue.2.2.trans hvalueMono) ?_ n
  intro k _hk
  have hb := (hjets z hz hs hzJ m j hhost hoptical side g hg hfactor R hR hstrip
    δ hδ Θ hΘ θ k).2
  have hpower : (CJ * T.E0 (T.sample j)) ^ (BJ k) ≤ W ^ (A k) :=
    (Real.rpow_le_rpow (zero_le_one.trans (hfloorJ j)) hWJ (hBJ k).le).trans
      (Real.rpow_le_rpow_of_exponent_le hW (hJA k))
  exact hb.trans (mul_le_mul_of_nonneg_right
    (mul_le_mul (hJA k) hpower
      (Real.rpow_nonneg (zero_le_one.trans (hfloorJ j)) _)
      (zero_le_one.trans (hA k)))
    (add_nonneg zero_le_one (apply_nonneg _ _)))

end ContinuousFlexibility.Analysis
