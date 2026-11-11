import ContinuousFlexibility.Analysis.N01ControlledLeftRootFields
import ContinuousFlexibility.Analysis.N01RootRadialCoefficientValues
import ContinuousFlexibility.Analysis.RootBoundaryOrdinaryFieldBounds

/-!
# Actual controlled left-root charts and heights with all boundary jets

One state neighborhood and one derivative loss work for every left
component root. The actual regularized flow, its genuine inverse, the
N01 left angular lift, and the original radial coefficient determine
the chart and height. No target chart or height estimate is input.

These are the normalized coordinates x = (r-r₀)/δ and the normalized
radial coefficient a/δ. Identification with a global negative atlas is
a separate transport statement; it is not presumed here.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set
open ContinuousFlexibility.Statements
open scoped ContDiff

set_option backward.isDefEq.respectTransparency false

def N01ControlledLeftRootBoundaryAtState
    (D : ReferenceData) (S : PhysicalSpacesData) (C : NonlinearGeometryData S)
    (m : ℕ) (g : ℝ → ℝ) {R : ℝ} (hR : 0 < R)
    (κ δ Λ : ℝ) (loss : ℕ) (B : ℕ → ℝ) (z : AnnularState S × ℝ) : Prop :=
  let d := localizedRootDrift D S C (C.left m) 1 hR z
  let c := localizedRootSpeed D S C g (C.left m) 1 hR z
  N04FlowAngularControl (rootRescaledField d c δ) Λ ∧
    ∃ Θ : (ℝ × ℝ) → ℝ → ℝ → ℝ,
      N04FlowEquations (rootRescaledField d c δ) Θ ∧
      let G := rootScaledInverseCoordinate Θ (stateLeftChart S z.1 m) (Real.sqrt δ)
      let a := rootScaledRadialCoefficient D S C z (C.left m) 1 δ
      ContDiff ℝ ∞ G ∧
        (∀ x ζ θ, G (x, ζ, θ + Real.pi) = G (x, ζ, θ) + Real.pi) ∧
        (∀ θ, G (0, 0, θ) = stateLeftChart S z.1 m θ) ∧
        (∀ θ, δ * Real.sqrt δ * κ / 3 ≤ rootOddCoefficient G (0, θ)) ∧
        ∀ θ ∈ Icc (-Real.pi) Real.pi,
          RootBoundaryMaterialJetBound (pairGrading (stateGrading S) realGrading)
            loss B (z - (C.referenceState, 0)) a G θ

def N01ControlledLeftRootBoundaryFamily
    (D : ReferenceData) (S : PhysicalSpacesData) (C : NonlinearGeometryData S)
    (base loss : ℕ) (ε : ℝ) (m : ℕ) (g : ℝ → ℝ)
    {R : ℝ} (hR : 0 < R) (κ δ Λ : ℝ) (B : ℕ → ℝ) : Prop :=
  ∀ z ∈ stateNeighborhood S C base ε, stateSector S z.1 →
    N01ControlledLeftRootBoundaryAtState D S C m g hR κ δ Λ loss B z

private theorem n01_leftRootBoundary_of_actual_fields
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {base coefficientLoss fieldLoss low outLoss : ℕ}
    {ε : ℝ} {m : ℕ} {g : ℝ → ℝ} {R κ δ Λ : ℝ} (hR : 0 < R)
    (hS : IsPhysicalSpaces D T S) (hN : N01Properties D T S C base coefficientLoss ε)
    (hr : C.left m ∈ Ioo D.a D.b) (hδ : 0 < δ)
    {A C' B : ℕ → ℝ}
    (hcontrol : RootBoundaryOrdinaryFieldControl
      (pairGrading (stateGrading S) realGrading) fieldLoss coefficientLoss low outLoss A C'
      (δ * Real.sqrt δ * κ / 3) (D.w (C.left m) / (8 * δ))
      (16 * D.w (C.left m) / δ) B)
    (hcoefficient : N01ScaledRadialCoefficientRootJetBound D S C base coefficientLoss ε
      (C.left m) 1 δ C')
    {z : AnnularState S × ℝ} (hz : z ∈ stateNeighborhood S C base ε)
    (hs : stateSector S z.1)
    (hlow : pairGrading (stateGrading S) realGrading low (z - (C.referenceState, 0)) ≤ 1)
    (hfields : N01ControlledLeftRootFieldsAtState D S C m g hR κ δ Λ fieldLoss A z) :
    N01ControlledLeftRootBoundaryAtState D S C m g hR κ δ Λ outLoss B z := by
  obtain ⟨hangular, Θ, hΘ, hG, hperiod, hzero, hpositive, hjets⟩ := hfields
  refine ⟨hangular, Θ, hΘ, hG, hperiod, hzero, hpositive, ?_⟩
  intro θ hθ
  have hderiv := ((contDiff_stateLeftChart hS z.1 m).differentiable (by simp) θ).hasDerivAt
  have hk := hN.2.2.2.2.2.2.2.1 z hz hs m θ
  have hk' : deriv (stateLeftChart S z.1 m) θ ∈ Icc (1 / 4 : ℝ) 4 :=
    ⟨(by norm_num : (1 / 4 : ℝ) ≤ 1 / 2).trans hk.1,
      hk.2.1.trans (by norm_num : (2 : ℝ) ≤ 4)⟩
  have ha := hcoefficient z hz hs θ
  exact hcontrol (z - (C.referenceState, 0)) hlow
    (rootScaledInverseCoordinate Θ (stateLeftChart S z.1 m) (Real.sqrt δ))
    (rootScaledRadialCoefficient D S C z (C.left m) 1 δ)
    (stateLeftChart S z.1 m) θ (deriv (stateLeftChart S z.1 m) θ) hθ
    hG hperiod hzero hderiv hk' (hpositive θ) ha.1
    (n01_scaledRadialCoefficient_root_values hN hr hδ hz hs θ) hjets ha.2

/-- Every component receives an actual normalized root chart and height
with all ordinary boundary jets on one common neighborhood. The positive
collar scale and numerical constants are chosen before each state. -/
theorem n01_exists_common_left_root_boundary_jets
    (hFlow : N04FlowJetsTarget)
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {base loss : ℕ} {ε : ℝ}
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    (hN : N01Properties D T S C base loss ε) :
    ∃ newBase outLoss : ℕ, ∃ ε' : ℝ, base ≤ newBase ∧ 0 < ε' ∧ ε' ≤ ε ∧
      ∀ m : ℕ, ∃ g : ℝ → ℝ, ∃ R : ℝ, ∃ hR : 0 < R, ∃ κ : ℝ,
        ContDiff ℝ ∞ g ∧ 0 < g 0 ∧ 0 < κ ∧
        (∀ t : ℝ, -deriv D.w (C.left m + t) = t * g t) ∧
        N01ActualRootFieldGeometry D S C newBase ε' (C.left m) 1 g hR ∧
        ∀ Λ : ℝ, 0 < Λ → ∃ δ : ℝ, ∃ B : ℕ → ℝ,
          0 < δ ∧ δ ≤ R / 4 ∧ δ ≤ 1 ∧ (∀ s, 0 < B s) ∧
          N01ControlledLeftRootBoundaryFamily D S C newBase outLoss ε'
            m g hR κ δ Λ B := by
  have hp : Monotone (pairGrading (stateGrading S) realGrading) :=
    tamePairGrading_monotone (stateGrading_monotone S) (fun _ _ _ => le_rfl)
  have hI : HasInterpolation (pairGrading (stateGrading S) realGrading) :=
    coordinate_hasInterpolation_pair (stateGrading_monotone S)
      (fun _ _ _ => le_rfl) (coordinate_hasInterpolation_stateGrading hS)
      coordinate_hasInterpolation_realGrading
  obtain ⟨fieldBase, fieldLoss, η, hb, hη, hηε, hroots⟩ :=
    n01_exists_common_left_root_ordinary_fields hFlow hS hT hN
  obtain ⟨low, outLoss, hbound⟩ := rootBoundary_from_ordinaryFields_fixed_loss hp hI fieldLoss loss
  let ε' := min η (1 / 2 : ℝ)
  have hε' : 0 < ε' := lt_min hη (by norm_num)
  have hsmall : ε' ≤ η := min_le_left _ _
  have hhalf : ε' ≤ 1 / 2 := min_le_right _ _
  have hU : stateNeighborhood S C (max fieldBase low) ε' ⊆
      stateNeighborhood S C fieldBase η :=
    stateNeighborhood_mono S C (le_max_left _ _) hsmall
  have hUold : stateNeighborhood S C (max fieldBase low) ε' ⊆
      stateNeighborhood S C base ε := hU.trans (stateNeighborhood_mono S C hb hηε)
  have hlow (z : AnnularState S × ℝ)
      (hz : z ∈ stateNeighborhood S C (max fieldBase low) ε') :
      pairGrading (stateGrading S) realGrading low (z - (C.referenceState, 0)) ≤ 1 := by
    have hz' := stateNeighborhood_mono S C (le_max_right fieldBase low) le_rfl hz
    exact (pairGrading_displacement_le_two_mul_radius hz').trans (by linarith)
  refine ⟨max fieldBase low, outLoss, ε', hb.trans (le_max_left _ _),
    hε', hsmall.trans hηε, ?_⟩
  intro m
  obtain ⟨g, R, hR, κ, hg, hg0, hκ, hdivide, hgeometry, hfields⟩ := hroots m
  have hr : C.left m ∈ Ioo D.a D.b := by
    simpa only [n01ComponentRoot, Bool.false_eq_true, ↓reduceIte] using
      (n01_component_root_data hN m false).1
  obtain ⟨_, hD⟩ := hN.1.1
  have hw : 0 < D.w (C.left m) := hD.1.2.2.2.2.1 (C.left m) hr
  refine ⟨g, R, hR, κ, hg, hg0, hκ, hdivide,
    ⟨fun z hz hs => hgeometry.1 z (hU hz) hs, hgeometry.2⟩, ?_⟩
  intro Λ hΛ
  obtain ⟨δ, A, hδ, hδR, hδone, hA, hinput⟩ := hfields Λ hΛ
  obtain ⟨C', hC', hcoefficient⟩ := n01_scaledRadialCoefficient_root_fixed_loss hS hT hN hr 1 δ
  have hχl : 0 < δ * Real.sqrt δ * κ / 3 :=
    div_pos (mul_pos (mul_pos hδ (Real.sqrt_pos.mpr hδ)) hκ) (by norm_num)
  have hal : 0 < D.w (C.left m) / (8 * δ) :=
    div_pos hw (mul_pos (by norm_num) hδ)
  have halu : D.w (C.left m) / (8 * δ) ≤ 16 * D.w (C.left m) / δ := by
    rw [← div_div]
    exact div_le_div_of_nonneg_right (by linarith) hδ.le
  obtain ⟨B, hB, hmaterial⟩ := hbound A C' hA hC' (δ * Real.sqrt δ * κ / 3)
    (D.w (C.left m) / (8 * δ)) (16 * D.w (C.left m) / δ) hχl hal halu
  refine ⟨δ, B, hδ, hδR, hδone, hB, ?_⟩
  intro z hz hs
  exact n01_leftRootBoundary_of_actual_fields hR hS hN hr hδ hmaterial hcoefficient
    (hUold hz) hs (hlow z hz) (hinput z (hU hz) hs)

end ContinuousFlexibility.Analysis
