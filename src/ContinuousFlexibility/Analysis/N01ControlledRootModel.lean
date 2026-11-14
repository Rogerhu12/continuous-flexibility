module

public import ContinuousFlexibility.Analysis.N01ControlledRootInput
public import ContinuousFlexibility.Analysis.N01DividedRootBand
public import ContinuousFlexibility.Analysis.RootInputOrdinaryJets
public import ContinuousFlexibility.Analysis.RootOddUniformValueInterval
public import ContinuousFlexibility.Analysis.RootDividedModelMaterialJets
public import ContinuousFlexibility.Analysis.RootScaledJacobianClosedBand

/-!
# The actual controlled root model on a uniform closed band

The existing chosen-flow input supplies the genuine even and odd jets.
The actual N01 factorization supplies the divided determinant jets and
positive value range. Only the usable radial band is shortened. One
common neighborhood and derivative loss control the resulting chart,
Jacobian, height and inverse height, with a genuine numerical Jacobian
lower bound throughout the closed band.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set ContinuousFlexibility.Statements
open scoped ContDiff

set_option backward.isDefEq.respectTransparency false

def N01ControlledRootModelAtState
    (D : ReferenceData) (S : PhysicalSpacesData) (C : NonlinearGeometryData S)
    (m : ℕ) (rightEnd : Bool) (g : ℝ → ℝ) {R : ℝ} (hR : 0 < R)
    (δ ρ Λ J₀ : ℝ) (flowLoss modelLoss : ℕ) (A B : ℕ → ℝ)
    (z : AnnularState S × ℝ) : Prop :=
  let r := n01ComponentRoot C m rightEnd
  let σ := n01ComponentRootOrientation rightEnd
  let V := rootScaledDividedDiscriminant D S C z g r σ δ
  let d := localizedRootDrift D S C r σ hR z
  let c := localizedRootSpeed D S C g r σ hR z
  N04FlowAngularControl (rootRescaledField d c δ) Λ ∧
    ∃ Θ : (ℝ × ℝ) → ℝ → ℝ → ℝ,
      N04FlowEquations (rootRescaledField d c δ) Θ ∧
      let G := rootScaledInverseCoordinate Θ (n01RootLabel S C z m rightEnd) (Real.sqrt δ)
      ContDiff ℝ ∞ G ∧
        (∀ x ζ θ, G (x, ζ, θ + Real.pi) = G (x, ζ, θ) + Real.pi) ∧
        (∀ s : ℕ, CSBound s
          (Icc (0 : ℝ) 1 ×ˢ Icc (-1 : ℝ) 1 ×ˢ Icc (-Real.pi) Real.pi) G
          (A s * (1 + pairGrading (stateGrading S) realGrading (s + flowLoss)
            (z - (C.referenceState, 0))))) ∧
        (∀ q : PolarPoint, q.1 ∈ Icc (0 : ℝ) ρ →
          ContDiffAt ℝ ∞ V q ∧ 0 < V q ∧ 0 < extendedRootOddCoefficient G q ∧
            J₀ ≤ planeJacobian (extendedRootEvenOddChart G) q) ∧
        ∀ q : PolarPoint, q.1 ∈ Icc (0 : ℝ) ρ → q.2 ∈ Icc (-Real.pi) Real.pi →
          RootDividedModelJetBound (pairGrading (stateGrading S) realGrading)
            modelLoss B (z - (C.referenceState, 0)) δ V G q

private theorem bound_one_add_le_twice {A t : ℝ} (hA : 0 ≤ A) (ht : t ≤ 1) :
    A * (1 + t) ≤ 2 * A := by
  have h := mul_le_mul_of_nonneg_left (add_le_add (le_refl (1 : ℝ)) ht) hA
  nlinarith only [h]

/-- The common low order and output loss precede every component,
endpoint, previously chosen scale and numerical flow majorant. -/
theorem n01_controlledRootInput_uniform_model
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {base loss : ℕ} {ε : ℝ}
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    (hN : N01Properties D T S C base loss ε)
    (hflow : OrdinaryFlowJacobianBounds S C base ε) (flowLoss : ℕ) :
    ∃ low outLoss : ℕ, ∀ m : ℕ, ∀ rightEnd : Bool,
      ∀ g : ℝ → ℝ, ∀ R : ℝ, ∀ hR : 0 < R,
      ContDiff ℝ ∞ g →
      (∀ z ∈ stateNeighborhood S C base ε, stateSector S z.1 →
        RootCoefficientStripConditions D.w g (stateProfile D S C z.1)
          (stateHeight D S C z) (n01ComponentRoot C m rightEnd)
          (n01ComponentRootOrientation rightEnd) R) →
      ∀ κ δ Λ η : ℝ, 0 < κ → 0 < δ → δ ≤ 1 → 0 < η → η ≤ 1 →
      ∀ A : ℕ → ℝ, (∀ n, 0 < A n) →
      N01ControlledRootInputFamily D S C base flowLoss ε m rightEnd g hR κ δ Λ A →
      ∃ ρ J₀ : ℝ, ∃ B : ℕ → ℝ,
        0 < ρ ∧ ρ ≤ η ∧ δ * ρ ≤ R / 4 ∧ 0 < J₀ ∧ (∀ n, 0 < B n) ∧
        ∀ z ∈ stateNeighborhood S C (max base low) (min ε (1 / 2 : ℝ)),
          stateSector S z.1 →
          N01ControlledRootModelAtState D S C m rightEnd g hR δ ρ Λ J₀
            flowLoss outLoss A B z := by
  have hp : Monotone (pairGrading (stateGrading S) realGrading) :=
    tamePairGrading_monotone (stateGrading_monotone S) (fun _ _ _ => le_rfl)
  have hI := coordinate_hasInterpolation_pair (stateGrading_monotone S)
    (fun _ _ _ => le_rfl) (coordinate_hasInterpolation_stateGrading hS)
    coordinate_hasInterpolation_realGrading
  obtain ⟨lowV, lossV, hVband⟩ := n01_exists_dividedRootBand hS hT hN
  let inputLoss := max (flowLoss + 1) lossV
  obtain ⟨lowM, outLoss, hmaterial⟩ := rootDividedModel_fixed_loss_material_bound hp hI inputLoss
  let low := max (2 + flowLoss) (max lowV lowM)
  refine ⟨low, outLoss, ?_⟩
  intro m rightEnd g R hR hg hstrip κ δ Λ η hκ hδ hδone hη hηone A hA hinput
  let r := n01ComponentRoot C m rightEnd
  let σ := n01ComponentRootOrientation rightEnd
  obtain ⟨ρV, lV, uV, κV, BV, hρV, hρVη, hρVR, hlV, hluV, hκV, hBV, hV⟩ :=
    hVband r σ g R (n01_component_root_data hN m rightEnd).1
      (n01ComponentRootOrientation_eq rightEnd) hR hg hstrip δ η hδ hη
  let χ₀ := δ * Real.sqrt δ * κ / (if rightEnd then (6 : ℝ) else 3)
  have hχ₀ : 0 < χ₀ := div_pos
    (mul_pos (mul_pos hδ (Real.sqrt_pos.mpr hδ)) hκ)
    (by cases rightEnd <;> norm_num)
  obtain ⟨ρ, u, hρ, hρV', hu, hχband⟩ :=
    exists_rootOddCoefficient_uniform_positive_band hρV (hρVη.trans hηone) hχ₀
      (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) (hA 2).le)
  let uχ := max u (χ₀ / 2)
  have hluχ : χ₀ / 2 ≤ uχ := le_max_right _ _
  have huχ : 0 < uχ := hu.trans_le (le_max_left _ _)
  obtain ⟨BO, hBO, hordinary⟩ := exists_rootInput_ordinaryField_bound hp flowLoss A hA
  let Q : ℕ → ℝ := fun n => BO n + BV n
  have hQ (n : ℕ) : 0 < Q n := add_pos (hBO n) (hBV n)
  obtain ⟨B, hB, hmodel⟩ := hmaterial Q hQ δ (χ₀ / 2) uχ lV uV
    hδ (half_pos hχ₀) hluχ hlV hluV
  let J₀ := ((δ * Real.sqrt δ) * κV) * (Real.exp (-Λ) / 4) ^ 2 /
    Real.sqrt (((3 / 2 : ℝ) * uχ) ^ (2 / 3 : ℝ))
  have hJ₀ : 0 < J₀ := div_pos
    (mul_pos (mul_pos (mul_pos hδ (Real.sqrt_pos.mpr hδ)) hκV)
      (pow_pos (div_pos (Real.exp_pos _) (by norm_num)) 2))
    (Real.sqrt_pos.mpr (Real.rpow_pos_of_pos (mul_pos (by norm_num) huχ) _))
  have hρR : δ * ρ ≤ R / 4 :=
    (mul_le_mul_of_nonneg_left hρV' hδ.le).trans hρVR
  refine ⟨ρ, J₀, B, hρ, hρV'.trans hρVη, hρR, hJ₀, hB, ?_⟩
  intro z hz hs
  have hzold : z ∈ stateNeighborhood S C base ε :=
    stateNeighborhood_mono S C (le_max_left _ _) (min_le_left _ _) hz
  have hzlow : z ∈ stateNeighborhood S C low (min ε (1 / 2 : ℝ)) :=
    stateNeighborhood_mono S C (le_max_right _ _) le_rfl hz
  have hlow : pairGrading (stateGrading S) realGrading low
      (z - (C.referenceState, 0)) ≤ 1 :=
    (pairGrading_displacement_le_two_mul_radius hzlow).trans (by
      have he : min ε (1 / 2 : ℝ) ≤ 1 / 2 := min_le_right _ _
      linarith only [he])
  have hsmall (j : ℕ) (hj : j ≤ low) :
      pairGrading (stateGrading S) realGrading j (z - (C.referenceState, 0)) ≤ 1 :=
    (hp hj _).trans hlow
  obtain ⟨hcontrol, Θ, hΘ, hG, hperiod, _hzero, hroot, hjets⟩ := hinput z hzold hs
  let G := rootScaledInverseCoordinate Θ (n01RootLabel S C z m rightEnd) (Real.sqrt δ)
  let V := rootScaledDividedDiscriminant D S C z g r σ δ
  have hCS2 : CSBound 2
      (Icc (0 : ℝ) 1 ×ˢ Icc (-1 : ℝ) 1 ×ˢ Icc (-Real.pi) Real.pi) G (2 * A 2) :=
    (hjets 2).mono_bound (bound_one_add_le_twice (hA 2).le
      (hsmall (2 + flowLoss) (le_max_left _ _)))
  have hχvalues (q : PolarPoint) (hq : q.1 ∈ Icc (0 : ℝ) ρ) :
      extendedRootOddCoefficient G q ∈ Icc (χ₀ / 2) uχ := by
    have hh := hχband G hG hperiod hCS2 hroot q.1 hq q.2
    exact ⟨hh.1, hh.2.trans (le_max_left _ _)⟩
  have hVvalues (q : PolarPoint) (hq : q.1 ∈ Icc (0 : ℝ) ρ) :
      ContDiffAt ℝ ∞ V q ∧
      PointwiseMaterialJetBound (pairGrading (stateGrading S) realGrading) lossV BV
        (z - (C.referenceState, 0)) V q ∧
      V q ∈ Icc lV uV ∧
      κV ≤ localizedRootSpeed D S C g r σ hR z (δ * q.1, q.2) :=
    hV z hzold hs (hsmall lowV ((le_max_left _ _).trans (le_max_right _ _))) q
      ⟨hq.1, hq.2.trans hρV'⟩
  have hfields := contDiff_localizedRootFields_of_n01 hS hT hN hg hR (hstrip z hzold hs)
  have hfieldPeriod := periodic_localizedRootFields hS C g r σ hR z
  have hlabel := n01RootLabel_contDiff hS hT hN hzold hs m rightEnd
  have hlabelPeriod := n01RootLabel_period_add hN hzold hs m rightEnd
  have hτ : |Real.sqrt δ| ≤ 1 := by
    simpa only [one_mul] using
      abs_signed_sqrt_le_one (η := (1 : ℝ)) hδ.le hδone (Or.inl rfl)
  have hJclosed := (rootScaledJacobian_lower_closed_band hfields.1 hfields.2
    hfieldPeriod.1 hfieldPeriod.2 hΘ hcontrol hlabel hlabelPeriod
    (n01RootLabel_deriv_mem_quarter_four hN hflow hzold hs m rightEnd)
    hδ (Real.sqrt_pos.mpr hδ) hτ hκV hρ (hρV'.trans (hρVη.trans hηone))
    (fun q hq => (hVvalues q hq).2.2.2)
    (fun q hq => ⟨(half_pos hχ₀).trans_le (hχvalues q hq).1, (hχvalues q hq).2⟩)).2
  have hO := hordinary (z - (C.referenceState, 0)) G hG hperiod hjets
  refine ⟨hcontrol, Θ, hΘ, hG, hperiod, hjets, ?_, ?_⟩
  · intro q hq
    exact ⟨(hVvalues q hq).1, hlV.trans_le (hVvalues q hq).2.2.1.1,
      (half_pos hχ₀).trans_le (hχvalues q hq).1, hJclosed q hq⟩
  · intro q hq hθ
    have hbox : q ∈ Icc (0 : ℝ) 1 ×ˢ Icc (-Real.pi) Real.pi :=
      ⟨⟨hq.1, hq.2.trans (hρV'.trans (hρVη.trans hηone))⟩, hθ⟩
    have hφjet : PointwiseMaterialJetBound (pairGrading (stateGrading S) realGrading)
        (flowLoss + 1) BO (z - (C.referenceState, 0)) (extendedRootEven G) q :=
      fun n => (hO.2.2 n).1 n le_rfl q hbox
    have hχjet : PointwiseMaterialJetBound (pairGrading (stateGrading S) realGrading)
        (flowLoss + 1) BO (z - (C.referenceState, 0)) (extendedRootOddCoefficient G) q :=
      fun n => (hO.2.2 n).2 n le_rfl q hbox
    have hφQ := hφjet.mono hp (le_max_left (flowLoss + 1) lossV) (fun n => (hBO n).le)
      (fun n => le_add_of_nonneg_right (hBV n).le)
    have hχQ := hχjet.mono hp (le_max_left (flowLoss + 1) lossV) (fun n => (hBO n).le)
      (fun n => le_add_of_nonneg_right (hBV n).le)
    have hVQ := (hVvalues q hq).2.1.mono hp (le_max_right (flowLoss + 1) lossV) (fun n => (hBV n).le)
      (fun n => le_add_of_nonneg_left (hBO n).le)
    exact hmodel (z - (C.referenceState, 0))
      (hsmall lowM ((le_max_right _ _).trans (le_max_right _ _))) G V q
      hO.1.contDiffAt hO.2.1.contDiffAt (hVvalues q hq).1
      (by simpa only [abs_of_nonneg hq.1] using hbox.1.2)
      (hχvalues q hq) (hVvalues q hq).2.2.1 hφQ hχQ hVQ

end ContinuousFlexibility.Analysis
