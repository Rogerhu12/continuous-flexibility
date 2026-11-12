import ContinuousFlexibility.Analysis.N01RootOddPowerMaterialJets
import ContinuousFlexibility.Analysis.RootDividedHeight
import ContinuousFlexibility.Analysis.PointwiseProductPolynomialMaterialJets

/-!
# Material jets of the same unit-normalized divided height

The actual height is a product of powers of the genuine odd coefficient
and the actual divided discriminant. Both powers already have explicit
material costs at the same root and sample. The sole remaining scalar
factor depends only on the requested exponent, never on a chosen box.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter ContinuousFlexibility.Statements
open scoped ContDiff Topology

private theorem unitRootHeight_rpow_eq
    {V : PolarPoint → ℝ} {G : ℝ × ℝ × ℝ → ℝ} {p : PolarPoint}
    (hV : 0 < V p) (hχ : 0 < extendedRootOddCoefficient G p) (γ : ℝ) :
    rootDividedHeight 1 V G p ^ γ = (3 / 2 : ℝ) ^ (γ / 6) *
      (extendedRootOddCoefficient G p ^ (γ / 6) * V p ^ (-γ / 4)) := by
  have ha : 0 < (3 / 2 : ℝ) * extendedRootOddCoefficient G p :=
    mul_pos (by norm_num) hχ
  rw [rootDividedHeight_eq_powers (by norm_num : (0 : ℝ) < 1) hV hχ, one_mul,
    Real.mul_rpow (Real.rpow_nonneg ha.le _) (Real.rpow_nonneg hV.le _),
    ← Real.rpow_mul ha.le, ← Real.rpow_mul hV.le,
    show (1 / 6 : ℝ) * γ = γ / 6 by ring,
    show (-(1 / 4 : ℝ)) * γ = -γ / 4 by ring,
    Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 3 / 2) hχ.le]
  ring

private theorem unitRootHeight_material_mono
    {E : Type} [AddCommGroup E] [Module ℝ E]
    {p : ℕ → Seminorm ℝ E} (hp : Monotone p)
    {a b V W : ℝ} {k l m : ℕ} (ha : 0 ≤ a) (hab : a ≤ b) (hb : 0 ≤ b)
    (hV : 1 ≤ V) (hVW : V ≤ W) (hlm : l ≤ m) (z : E) :
    a * V ^ a * (1 + p (k + l) z) ≤ b * W ^ b * (1 + p (k + m) z) := by
  have hW : 1 ≤ W := hV.trans hVW
  have hpower : V ^ a ≤ W ^ b :=
    (Real.rpow_le_rpow (zero_le_one.trans hV) hVW ha).trans
      (Real.rpow_le_rpow_of_exponent_le hW hab)
  exact mul_le_mul
    (mul_le_mul hab hpower (Real.rpow_nonneg (zero_le_one.trans hV) _) hb)
    (add_le_add_left (hp (Nat.add_le_add_left hlm k) z) 1)
    (add_nonneg zero_le_one (apply_nonneg _ _))
    (mul_nonneg hb (Real.rpow_nonneg (zero_le_one.trans hW) _))

theorem n01_rootDividedHeight_unit_rpow_material_jets_of_component_optical
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
        let V := rootCoefficientRadialFactor D.w g (stateProfile D S C z.1)
          (stateHeight D S C z) (n01ComponentRoot C m side)
          (n01ComponentRootOrientation side)
        ‖iteratedFDeriv ℝ n (fun p => rootDividedHeight 1 V G p ^ γ) (0, θ)‖ ≤
          B n * (C0 * T.E0 (T.sample j)) ^ (B n) *
            (1 + pairGrading (stateGrading S) realGrading (n + outLoss)
              (z - (C.referenceState, 0))) := by
  have hp : Monotone (pairGrading (stateGrading S) realGrading) :=
    tamePairGrading_monotone (stateGrading_monotone S) (fun _ _ _ => le_rfl)
  have hI := coordinate_hasInterpolation_pair (stateGrading_monotone S)
    (fun _ _ _ => le_rfl) (coordinate_hasInterpolation_stateGrading hS)
    coordinate_hasInterpolation_realGrading
  obtain ⟨Cχ, lowχ, lossχ, hCχ, hfloorχ, hpowersχ⟩ :=
    n01_rootOddCoefficient_unit_rpow_material_jets_of_component_optical hS hT hN hflow hK
  obtain ⟨CV, lowV, lossV, hCV, hfloorV, hpowersV⟩ :=
    n01_rootFactor_axis_rpow_material_jets_of_component_optical hS hT hN hK
  obtain ⟨_, lowPos, _, _, _, _, hvaluesχ⟩ :=
    n01_rootOddCoefficient_unit_material_values_of_component_optical hS hT hN hflow hK
  let inputLoss : ℕ := max lossχ lossV
  obtain ⟨productLow, outLoss, hproduct⟩ :=
    pointwiseProduct_polynomial_material_bound (X := PolarPoint) hp hI inputLoss
  let C0 : ℝ := max Cχ CV
  have hC0 : 1 ≤ C0 := hCχ.trans (le_max_left _ _)
  have hE (j : ℕ) : 0 < T.E0 (T.sample j) :=
    (hT.2.1 _ (materialSample_mem_interval hN.1.1 hT j)).2.2.1
  have hfloor (j : ℕ) : 1 ≤ C0 * T.E0 (T.sample j) :=
    (hfloorχ j).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (hE j).le)
  refine ⟨C0, max lowχ (max lowV (max lowPos productLow)), outLoss, hC0, hfloor, ?_⟩
  intro γ
  obtain ⟨Bχ, hBχ, hjetsχ⟩ := hpowersχ (γ / 6)
  obtain ⟨BV, hBV, hjetsV⟩ := hpowersV (-γ / 4)
  let A : ℕ → ℝ := fun k => max 1 (max (Bχ k) (BV k))
  have hA (k : ℕ) : 1 ≤ A k := le_max_left _ _
  have hχA (k : ℕ) : Bχ k ≤ A k := (le_max_left _ _).trans (le_max_right _ _)
  have hVA (k : ℕ) : BV k ≤ A k := (le_max_right _ _).trans (le_max_right _ _)
  obtain ⟨BP, hBP, hbound⟩ := hproduct A hA
  let Q : ℝ := (3 / 2 : ℝ) ^ (γ / 6)
  have hQ : 0 < Q := Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 3 / 2) _
  let B : ℕ → ℝ := fun k => 1 + (1 + Q) * BP k
  have hB (k : ℕ) : 0 < B k := by
    dsimp only [B]
    exact add_pos zero_lt_one (mul_pos (add_pos zero_lt_one hQ) (hBP k))
  refine ⟨B, hB, ?_⟩
  intro z hz hs hlow m j hhost hoptical side g hg hfactor R hR hstrip δ hδ Θ hΘ θ n
  have hzχ := (hp (le_max_left lowχ (max lowV (max lowPos productLow))) _).trans hlow
  have hzV := (hp ((le_max_left lowV (max lowPos productLow)).trans
    (le_max_right lowχ (max lowV (max lowPos productLow)))) _).trans hlow
  have hzPos := (hp ((le_max_left lowPos productLow).trans
    ((le_max_right lowV (max lowPos productLow)).trans
      (le_max_right lowχ (max lowV (max lowPos productLow))))) _).trans hlow
  have hzP := (hp ((le_max_right lowPos productLow).trans
    ((le_max_right lowV (max lowPos productLow)).trans
      (le_max_right lowχ (max lowV (max lowPos productLow))))) _).trans hlow
  let W : ℝ := C0 * T.E0 (T.sample j)
  have hW : 1 ≤ W := hfloor j
  have hWχ : Cχ * T.E0 (T.sample j) ≤ W :=
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
  let V : PolarPoint → ℝ := rootCoefficientRadialFactor D.w g (stateProfile D S C z.1)
    (stateHeight D S C z) r σ
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
  have hχpos : 0 < extendedRootOddCoefficient G (0, θ) :=
    (hvaluesχ z hz hs hzPos m j hhost hoptical side g hg hfactor R hR hstrip
      δ hδ Θ hΘ θ).1
  have hzero : ((0, θ) : PolarPoint) ∈ Ioo (-R - R) (R + R) ×ˢ (univ : Set ℝ) := by
    refine ⟨⟨?_, ?_⟩, mem_univ _⟩ <;> linarith only [hR]
  have hdata := hstrip (0, θ) hzero
  have hV : ContDiffAt ℝ ∞ V (0, θ) :=
    contDiffAt_rootCoefficientRadialFactor hN.1.1.choose_spec.1.2.2.1.1 hg
      (contDiff_stateProfile_of_n01 hS hT hN z.1)
      (contDiff_stateHeight_of_n01 hS hT hN z)
      hdata.1 hdata.2.1 hdata.2.2.1 hdata.2.2.2.1 hdata.2.2.2.2.1
  have hVpos : 0 < V (0, θ) := by
    change 0 < rootCoefficientRadialFactor D.w g (stateProfile D S C z.1)
      (stateHeight D S C z) r σ (0, θ)
    rw [rootCoefficientRadialFactor_eq hdata.1 hdata.2.1 hdata.2.2.1
      hdata.2.2.2.1 hdata.2.2.2.2.1.ne']
    exact div_pos (rootProfileRadicand_pos hdata.1 hdata.2.1 hdata.2.2.1)
      (pow_pos hdata.2.2.2.1 2)
  let f : PolarPoint → ℝ := fun p => extendedRootOddCoefficient G p ^ (γ / 6)
  let q : PolarPoint → ℝ := fun p => V p ^ (-γ / 4)
  have hf : ContDiffAt ℝ ∞ f (0, θ) := hχ.contDiffAt.rpow_const_of_ne hχpos.ne'
  have hq : ContDiffAt ℝ ∞ q (0, θ) := hV.rpow_const_of_ne hVpos.ne'
  have hb := hbound (z - (C.referenceState, 0)) hzP W hW f q (0, θ) hf hq
    (fun k => (hjetsχ z hz hs hzχ m j hhost hoptical side g hg hfactor R hR hstrip
      δ hδ Θ hΘ θ k).trans (unitRootHeight_material_mono hp (hBχ k).le (hχA k)
        (zero_le_one.trans (hA k)) (hfloorχ j) hWχ (le_max_left lossχ lossV) _))
    (fun k => (hjetsV z hz hs hzV m j hhost hoptical side g hg hfactor R hR hstrip
      θ k).trans (unitRootHeight_material_mono hp (hBV k).le (hVA k)
        (zero_le_one.trans (hA k)) (hfloorV j) hWV (le_max_right lossχ lossV) _)) n
  have he : (fun p => rootDividedHeight 1 V G p ^ γ) =ᶠ[𝓝 (0, θ)]
      (fun p => Q * (f p * q p)) := by
    filter_upwards [hχ.continuousAt.eventually (Ioi_mem_nhds hχpos),
      hV.continuousAt.eventually (Ioi_mem_nhds hVpos)] with p hpχ hpV
    exact unitRootHeight_rpow_eq hpV hpχ γ
  have hscale : ‖iteratedFDeriv ℝ n (fun p => Q * (f p * q p)) (0, θ)‖ =
      Q * ‖iteratedFDeriv ℝ n (fun p => f p * q p) (0, θ)‖ := by
    have hh := iteratedFDeriv_const_smul_apply' (a := Q)
      ((hf.mul hq).of_le (by simp : (n : ℕ∞ω) ≤ ∞))
    simpa only [smul_eq_mul, norm_smul, Real.norm_of_nonneg hQ.le] using congrArg norm hh
  change ‖iteratedFDeriv ℝ n (fun p => rootDividedHeight 1 V G p ^ γ) (0, θ)‖ ≤ _
  rw [(he.iteratedFDeriv ℝ n).self_of_nhds, hscale]
  apply (mul_le_mul_of_nonneg_left hb hQ.le).trans
  have hPB : BP n ≤ B n := by
    dsimp only [B]
    nlinarith only [mul_pos hQ (hBP n)]
  have hQPB : Q * BP n ≤ B n := by dsimp only [B]; linarith only [hBP n]
  calc
    _ = (Q * BP n) * W ^ (BP n) *
        (1 + pairGrading (stateGrading S) realGrading (n + outLoss)
          (z - (C.referenceState, 0))) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right
      (mul_le_mul hQPB (Real.rpow_le_rpow_of_exponent_le hW hPB)
        (Real.rpow_nonneg (zero_le_one.trans hW) _) (hB n).le)
      (add_nonneg zero_le_one (apply_nonneg _ _))

end ContinuousFlexibility.Analysis
