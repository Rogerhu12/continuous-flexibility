import ContinuousFlexibility.Analysis.N04bActualTravelChart
import ContinuousFlexibility.Analysis.N04bReferenceTravelCut
import ContinuousFlexibility.Analysis.N04bErrorFactorization
import ContinuousFlexibility.Analysis.N08ReferenceFlow
import ContinuousFlexibility.Analysis.N01CoefficientValueJets
import ContinuousFlexibility.Analysis.EvenPeriodicTestGerms
import ContinuousFlexibility.Analysis.OperatorCoefficientClassification
import ContinuousFlexibility.Analysis.OffAxisContinuousRecovery

/-!
# The actual reference travel chart is the radial optical chart

At the reference state, the genuine return residual vanishes. The N03
factorization and actual height-test germs recover the smooth corrected
coefficients. Integrating the N03 flow equation gives the optical translation,
before canonical coordinates are introduced. Its literal chosen angular
inverse then gives the optical travel and the unchanged angular coordinate.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter
open ContinuousFlexibility.Statements
open scoped ContDiff Topology

set_option backward.isDefEq.respectTransparency false

theorem n04b_referenceState_sector
    {D : ReferenceData} {S : PhysicalSpacesData} {C : NonlinearGeometryData S}
    (href : referenceStateConditions D S C) :
    stateSector S C.referenceState := by
  have hκ : C.referenceState.2.2.1 = 0 := href.2.2.2.1
  have hh : C.referenceState.2.2.2 = 0 := href.2.2.2.2.1
  constructor
  · intro m θ φ
    simp only [hκ, map_zero, Pi.zero_apply]
  · intro m θ
    simp only [hh, map_zero, Pi.zero_apply, neg_zero]

theorem n04b_referenceState_leftChart
    {D : ReferenceData} {S : PhysicalSpacesData} {C : NonlinearGeometryData S}
    (href : referenceStateConditions D S C) (m : ℕ) (θ : ℝ) :
    stateLeftChart S C.referenceState m θ = θ := by
  have hh : C.referenceState.2.2.2 = 0 := href.2.2.2.2.1
  simp only [stateLeftChart, hh, map_zero, Pi.zero_apply, add_zero]

private theorem coefficients_eq_of_smooth_heightPair_action
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    {A B : SymmetricCoefficients}
    (hAa : ContDiffOn ℝ ∞ A.a (annularOpen D))
    (hAb : ContDiffOn ℝ ∞ A.b (annularOpen D))
    (hAc : ContDiffOn ℝ ∞ A.c (annularOpen D))
    (hBa : ContDiffOn ℝ ∞ B.a (annularOpen D))
    (hBb : ContDiffOn ℝ ∞ B.b (annularOpen D))
    (hBc : ContDiffOn ℝ ∞ B.c (annularOpen D))
    (hop : ∀ η : HeightPair S, ∀ p ∈ annularOpen D,
      divergenceOperator A (heightPairField S η) p =
        divergenceOperator B (heightPairField S η) p)
    {p : PolarPoint} (hp : p ∈ annularOpen D) :
    A.a p = B.a p ∧ A.b p = B.b p ∧ A.c p = B.c p := by
  have hU : IsOpen (annularOpen D) := isOpen_Ioo.prod isOpen_univ
  have hoff (q : PolarPoint) (hq : q ∈ annularOpen D)
      (hsin : Real.sin (2 * q.2) ≠ 0) :
      A.a q = B.a q ∧ A.b q = B.b q ∧ A.c q = B.c q := by
    apply coefficients_eq_of_differentiable_operator_action
      ((hAa.contDiffAt (hU.mem_nhds hq)).differentiableAt (by simp))
      ((hAb.contDiffAt (hU.mem_nhds hq)).differentiableAt (by simp))
      ((hAc.contDiffAt (hU.mem_nhds hq)).differentiableAt (by simp))
      ((hBa.contDiffAt (hU.mem_nhds hq)).differentiableAt (by simp))
      ((hBb.contDiffAt (hU.mem_nhds hq)).differentiableAt (by simp))
      ((hBc.contDiffAt (hU.mem_nhds hq)).differentiableAt (by simp))
    intro u hu
    obtain ⟨η, _, hη⟩ := exists_heightPair_germ_of_nonaxis hT hS hq hsin hu
    calc
      divergenceOperator A u q = divergenceOperator A (heightPairField S η) q :=
        (n04b_divergenceOperator_congr_germ hη).symm
      _ = divergenceOperator B (heightPairField S η) q := hop η q hq
      _ = divergenceOperator B u q := n04b_divergenceOperator_congr_germ hη
  exact ⟨scalar_eq_of_offAxis_on_open hU hp
      (hAa.contDiffAt (hU.mem_nhds hp)).continuousAt
      (hBa.contDiffAt (hU.mem_nhds hp)).continuousAt (fun q hq hs => (hoff q hq hs).1),
    scalar_eq_of_offAxis_on_open hU hp
      (hAb.contDiffAt (hU.mem_nhds hp)).continuousAt
      (hBb.contDiffAt (hU.mem_nhds hp)).continuousAt (fun q hq hs => (hoff q hq hs).2.1),
    scalar_eq_of_offAxis_on_open hU hp
      (hAc.contDiffAt (hU.mem_nhds hp)).continuousAt
      (hBc.contDiffAt (hU.mem_nhds hp)).continuousAt (fun q hq hs => (hoff q hq hs).2.2)⟩

private theorem n04b_referenceCoefficients_eq_original
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {R : ReturnEquationData S}
    {L : ReturnCorrectionData S} {base loss : ℕ} {ε : ℝ}
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (hN : NonlinearPropertiesThrough03 D T S C R L base loss ε)
    (hfield : N04bFieldRegularity D S C L base ε)
    {p : PolarPoint} (hp : p ∈ annularOpen D) :
    (L.coefficients (C.referenceState, 0)).a p =
        (originalCoefficients D S C (C.referenceState, 0)).a p ∧
      (L.coefficients (C.referenceState, 0)).b p =
        (originalCoefficients D S C (C.referenceState, 0)).b p ∧
      (L.coefficients (C.referenceState, 0)).c p =
        (originalCoefficients D S C (C.referenceState, 0)).c p := by
  have hN01 : N01Properties D T S C base loss ε := hN.1.1.2
  have hz : (C.referenceState, 0) ∈ stateNeighborhood S C base ε :=
    reference_mem_stateNeighborhood S C base hN01.2.1
  have hs : stateSector S C.referenceState := hN01.2.2.1.stateSector
  have hreg := hfield.smooth_coefficients (C.referenceState, 0) hz hs
  have ha : ContDiffOn ℝ ∞ (originalCoefficients D S C (C.referenceState, 0)).a
      (annularOpen D) := contDiffOn_originalCoefficientComponent_of_n01 hS hT hN01 hz hs 0
  have hb : ContDiffOn ℝ ∞ (originalCoefficients D S C (C.referenceState, 0)).b
      (annularOpen D) := contDiffOn_originalCoefficientComponent_of_n01 hS hT hN01 hz hs 1
  have hc : ContDiffOn ℝ ∞ (originalCoefficients D S C (C.referenceState, 0)).c
      (annularOpen D) := contDiffOn_originalCoefficientComponent_of_n01 hS hT hN01 hz hs 2
  have hzero : R.residual (C.referenceState, 0) = 0 :=
    n08_returnResidual_reference_zero hS hN01 hN.1.2
  exact coefficients_eq_of_smooth_heightPair_action hT hS
    hreg.1 hreg.2.1 hreg.2.2 ha hb hc
    (fun η q hq => n04b_returnCorrection_operator_eq_of_residual_zero
      hN.2 hz hs hzero η hq) hp

/-- The N03 reference-flow equation integrates to the existing optical
travel, including both physical component endpoints. -/
theorem n04b_referenceMinusFlow_eq_optical
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {R : ReturnEquationData S}
    {L : ReturnCorrectionData S} {base loss : ℕ} {ε : ℝ}
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (hN : NonlinearPropertiesThrough03 D T S C R L base loss ε)
    (hfield : N04bFieldRegularity D S C L base ε)
    (m : ℕ) {r : ℝ} (hr : r ∈ Icc (C.left m) (C.right m)) (θ : ℝ) :
    L.minusFlow (C.referenceState, 0) m r θ =
      θ - opticalTravel D.w (C.left m) r := by
  have hN01 : N01Properties D T S C base loss ε := hN.1.1.2
  have hN03 : N03Properties D T S C R L base ε := hN.2
  have hD : RadialProfileGeometry D := by
    obtain ⟨_, hdata⟩ := hN01.1.1
    exact hdata.1
  have hC : controlGeometryConditions D S C := hN01.2.2.2.1
  have hz : (C.referenceState, 0) ∈ stateNeighborhood S C base ε :=
    reference_mem_stateNeighborhood S C base hN01.2.1
  have hs : stateSector S C.referenceState := hN01.2.2.1.stateSector
  have hflow := hN03.2.2.2.2.1 (C.referenceState, 0) hz hs m θ
  have hcore (s : ℝ) (hs : s ∈ Icc (C.left m) (C.right m)) : s ∈ radialCore D :=
    ⟨(hC.1 m).1.trans_le hs.1, hs.2.trans_lt (hC.1 m).2.2⟩
  have hderiv (s : ℝ) (hs : s ∈ Ioo (C.left m) (C.right m)) :
      HasDerivAt (fun t => L.minusFlow (C.referenceState, 0) m t θ)
        (-opticalSpeed D.w s) s := by
    have hsD := hcore s (Ioo_subset_Icc_self hs)
    have he := n04b_referenceCoefficients_eq_original hT hS hN hfield
      (p := (s, L.minusFlow (C.referenceState, 0) m s θ)) ⟨hsD, mem_univ _⟩
    have hspeed :
        minusCharacteristicSpeed (L.coefficients (C.referenceState, 0))
            (s, L.minusFlow (C.referenceState, 0) m s θ) =
          minusCharacteristicSpeed (originalCoefficients D S C (C.referenceState, 0))
            (s, L.minusFlow (C.referenceState, 0) m s θ) := by
      simp only [minusCharacteristicSpeed, he.1, he.2.1, he.2.2]
    exact (hflow.2.2.1 s hs).congr_deriv (hspeed.trans
      (n08_minusCharacteristicSpeed_reference hD hN01.2.2.1 s _ hsD))
  have he := n08_radialFlow_eq_sub_integral hD.2.2.1.1
    (fun s hs => ⟨hD.1.trans (hcore s hs).1, hD.2.2.2.2.1 s (hcore s hs)⟩)
    hflow.2.1 hderiv hr
  simpa only [hflow.1, opticalTravel] using he

/-- The chosen inverse of the actual reference flow is the actual
opposite optical translation. -/
theorem n04b_referenceMinusFlow_inverse
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {R : ReturnEquationData S}
    {L : ReturnCorrectionData S} {base loss : ℕ} {ε : ℝ}
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (hN : NonlinearPropertiesThrough03 D T S C R L base loss ε)
    (hfield : N04bFieldRegularity D S C L base ε)
    (m : ℕ) {r : ℝ} (hr : r ∈ Icc (C.left m) (C.right m)) (θ : ℝ) :
    Function.invFun (L.minusFlow (C.referenceState, 0) m r) θ =
      θ + opticalTravel D.w (C.left m) r := by
  let f := L.minusFlow (C.referenceState, 0) m r
  have hf (η : ℝ) : f η = η - opticalTravel D.w (C.left m) r :=
    n04b_referenceMinusFlow_eq_optical hT hS hN hfield m hr η
  have hinj : Function.Injective f := by
    intro a b hab
    rw [hf a, hf b] at hab
    linarith only [hab]
  have he : f (θ + opticalTravel D.w (C.left m) r) = θ := by
    rw [hf]
    ring
  have hi := Function.leftInverse_invFun hinj
    (θ + opticalTravel D.w (C.left m) r)
  rw [he] at hi
  exact hi

theorem n04b_reference_firstIntegrals
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {R : ReturnEquationData S}
    {L : ReturnCorrectionData S} {base loss : ℕ} {ε : ℝ}
    (href : referenceStateConditions D S C)
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (hN : NonlinearPropertiesThrough03 D T S C R L base loss ε)
    (hfield : N04bFieldRegularity D S C L base ε)
    (m : ℕ) {r : ℝ} (hr : r ∈ Icc (C.left m) (C.right m)) (θ : ℝ) :
    n04bMinusFirstIntegral (fun p => L.minusFlow (C.referenceState, 0) m p.1 p.2)
        (stateLeftChart S C.referenceState m) (r, θ) =
      θ + opticalTravel D.w (C.left m) r ∧
    n04bPlusFirstIntegral (fun p => L.minusFlow (C.referenceState, 0) m p.1 p.2)
        (stateLeftChart S C.referenceState m) (r, θ) =
      θ - opticalTravel D.w (C.left m) r := by
  have hm (η : ℝ) :
      n04bMinusFirstIntegral (fun p => L.minusFlow (C.referenceState, 0) m p.1 p.2)
          (stateLeftChart S C.referenceState m) (r, η) =
        η + opticalTravel D.w (C.left m) r := by
    change stateLeftChart S C.referenceState m
      (Function.invFun (L.minusFlow (C.referenceState, 0) m r) η) = _
    rw [n04b_referenceMinusFlow_inverse hT hS hN hfield m hr η,
      n04b_referenceState_leftChart href]
  refine ⟨hm θ, ?_⟩
  change -n04bMinusFirstIntegral
    (fun p => L.minusFlow (C.referenceState, 0) m p.1 p.2)
    (stateLeftChart S C.referenceState m) (r, -θ) = _
  rw [hm (-θ)]
  ring

/-- The literal travel chart used in the state-dependent construction
specializes to the actual radial optical travel at the reference state. -/
theorem n04b_reference_actualTravelChart
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {R : ReturnEquationData S}
    {L : ReturnCorrectionData S} {base loss : ℕ} {ε : ℝ}
    (href : referenceStateConditions D S C)
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (hN : NonlinearPropertiesThrough03 D T S C R L base loss ε)
    (hfield : N04bFieldRegularity D S C L base ε)
    (m : ℕ) {r : ℝ} (hr : r ∈ Icc (C.left m) (C.right m)) (θ : ℝ) :
    n04bActualTravelChart S C L (C.referenceState, 0) m (r, θ) =
      (opticalTravel D.w (C.left m) r, θ) := by
  have h := n04b_reference_firstIntegrals href hT hS hN hfield m hr θ
  simp only [n04bActualTravelChart, n04bCharacteristicTravelChart,
    characteristicTravelChart, h.1, h.2]
  apply Prod.ext <;> dsimp only <;> ring

end ContinuousFlexibility.Analysis
