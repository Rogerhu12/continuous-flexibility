module

public import ContinuousFlexibility.Analysis.N01RootEvenOddAxisMaterialJets
public import ContinuousFlexibility.Analysis.N01RootOddCoefficientMaterialValues
public import ContinuousFlexibility.Analysis.PositivePowerPolynomialMaterialJets

/-!
# Actual odd-coefficient powers at the root

The genuine odd extension has a derived material jet tower, positive
value and reciprocal at the same root. The scalar power calculus has
explicit polynomial costs, so its common low order and loss precede
the real exponent. No interval of possible values is chosen afterward.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set ContinuousFlexibility.Statements
open scoped ContDiff

/-- The power estimate for an arbitrary graded state space. All grading
manipulations happen here, away from the actual state spaces. -/
private theorem rootOddPower_jet_bound_generic {E : Type} [AddCommGroup E] [Module ℝ E]
    {p : ℕ → Seminorm ℝ E} (x : E) {lowP lossJ outLoss : ℕ} (hx : p lowP x ≤ 1)
    {BJ A B : ℕ → ℝ} (hBJ : ∀ k, 0 < BJ k) (hA : ∀ k, 1 ≤ A k) (hJA : ∀ k, BJ k ≤ A k)
    {VJ W PV γ : ℝ} (hVJ : 1 ≤ VJ) (hVJW : VJ ≤ W) (hW : 1 ≤ W)
    {f : PolarPoint → ℝ} {q : PolarPoint} (hf : ContDiffAt ℝ ∞ f q) (hpos : 0 < f q)
    (hval : f q ≤ PV * W ^ PV) (hinv : (f q)⁻¹ ≤ PV * W ^ PV)
    (hjets : ∀ k, ‖iteratedFDeriv ℝ k f q‖ ≤
      BJ k * VJ ^ (BJ k) * (1 + p (k + lossJ) x))
    (hbound : ∀ z : E, p lowP z ≤ 1 → ∀ W : ℝ, 1 ≤ W →
      ∀ g : PolarPoint → ℝ, ∀ y : PolarPoint, ContDiffAt ℝ ∞ g y →
        0 < g y → g y ≤ PV * W ^ PV → (g y)⁻¹ ≤ PV * W ^ PV →
        (∀ k, 1 ≤ k → ‖iteratedFDeriv ℝ k g y‖ ≤
          A k * W ^ (A k) * (1 + p (k + lossJ) z)) →
        ∀ k, ‖iteratedFDeriv ℝ k (fun y => g y ^ γ) y‖ ≤
          B k * W ^ (B k) * (1 + p (k + outLoss) z))
    (n : ℕ) :
    ‖iteratedFDeriv ℝ n (fun y => f y ^ γ) q‖ ≤
      B n * W ^ (B n) * (1 + p (n + outLoss) x) := by
  refine hbound x hx W hW f q hf hpos hval hinv ?_ n
  intro k _hk
  have hpower : VJ ^ (BJ k) ≤ W ^ (A k) :=
    (Real.rpow_le_rpow (zero_le_one.trans hVJ) hVJW (hBJ k).le).trans
      (Real.rpow_le_rpow_of_exponent_le hW (hJA k))
  exact (hjets k).trans (mul_le_mul_of_nonneg_right
    (mul_le_mul (hJA k) hpower (Real.rpow_nonneg (zero_le_one.trans hVJ) _)
      (zero_le_one.trans (hA k)))
    (add_nonneg zero_le_one (apply_nonneg _ _)))

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
  refine (n01_rootEvenOdd_unit_axis_material_jets_of_component_optical
    hS hT hN hflow hK).elim ?_
  intro CJ hJ1
  refine hJ1.elim ?_
  intro lowJ hJ2
  refine hJ2.elim ?_
  intro lossJ hJ3
  have hCJ := hJ3.1
  have hfloorJ := hJ3.2.1
  refine hJ3.2.2.elim ?_
  intro BJ hBJj
  have hBJ := hBJj.1
  have hjets := hBJj.2
  refine (n01_rootOddCoefficient_unit_material_values_of_component_optical
    hS hT hN hflow hK).elim ?_
  intro CV hV1
  refine hV1.elim ?_
  intro lowV hV2
  refine hV2.elim ?_
  intro PV hV3
  have hfloorV := hV3.2.1
  have hPV := hV3.2.2.1
  have hvalues := hV3.2.2.2
  let C0 : ℝ := max CJ CV
  have hC0 : 1 ≤ C0 := hCJ.trans (le_max_left _ _)
  have hE (j : ℕ) : 0 < T.E0 (T.sample j) :=
    (hT.2.1 _ (materialSample_mem_interval hN.1.1 hT j)).2.2.1
  have hfloor (j : ℕ) : 1 ≤ C0 * T.E0 (T.sample j) :=
    (hfloorJ j).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (hE j).le)
  refine (positivePower_polynomial_material_bound (X := PolarPoint) hp hI lossJ).elim ?_
  intro lowP hP1
  refine hP1.elim ?_
  intro outLoss hpowers
  let A : ℕ → ℝ := fun n => max 1 (BJ n)
  have hA (n : ℕ) : 1 ≤ A n := le_max_left _ _
  have hJA (n : ℕ) : BJ n ≤ A n := le_max_right _ _
  refine ⟨C0, max lowJ (max lowV lowP), outLoss, hC0, hfloor, ?_⟩
  intro γ
  refine (hpowers γ PV hPV A hA).elim ?_
  intro B hBb
  have hB := hBb.1
  have hbound := hBb.2
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
  exact rootOddPower_jet_bound_generic (z - (C.referenceState, 0)) hzP hBJ hA hJA
    (hfloorJ j) hWJ hW hχ.contDiffAt hvalue.1
    (hvalue.2.1.trans hvalueMono) (hvalue.2.2.trans hvalueMono)
    (fun k => (hjets z hz hs hzJ m j hhost hoptical side g hg hfactor R hR hstrip
      δ hδ Θ hΘ θ k).2) hbound n

end ContinuousFlexibility.Analysis
