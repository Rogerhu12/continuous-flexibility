module

public import ContinuousFlexibility.Analysis.N01FlowParameterPartialVariation
public import ContinuousFlexibility.Analysis.N01CharacteristicParameterRegularity

/-!
# The actual first height response of the ordinary return

The physical coefficient formulas supply every continuity, boundedness,
and finite-dimensional differentiability premise needed by the dominated
flow-variation argument. Thus the partial-return and complete-return
derivatives below follow directly from N01 and the physical realizations.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Statements

local instance n01FlowHeightResponseStateSMul (S : PhysicalSpacesData) : SMul ℝ (AnnularState S) := Prod.instSMul

open Set Filter MeasureTheory
open ContinuousFlexibility.Analysis
open scoped Topology ContDiff

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {base loss : ℕ} {ε : ℝ}

theorem N01Properties.minusFlow_q_zero_partial_height_response_of_physical
    (hN : N01Properties D T S C base loss ε)
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    {x : AnnularState S} (hx : (x, 0) ∈ stateNeighborhood S C base ε)
    (hsector : stateSector S x) (m : ℕ) (θ : ℝ)
    {b : ℝ} (hb : b ∈ Icc (C.left m) (C.right m)) :
    HasDerivAt (fun q : ℝ => C.minusFlow (x, q) m b θ)
      (∫ r in C.left m..b,
        heightSpeedVariation (stateProfile D S C x) (stateU S x)
          (r, θ - opticalTravel (stateProfile D S C x) (C.left m) r)) 0 := by
  obtain ⟨δ, B, hδ, hδε, hB, hbound⟩ :=
    hN.characteristicParameterDerivatives_uniform_bound hS hT hx hsector m
  let Vq : ℝ → ℝ → ℝ → ℝ := fun q r y =>
    characteristicQDerivative D S C x (q, (r, y))
  let Vθ : ℝ → ℝ → ℝ → ℝ := fun q r y =>
    characteristicAngularDerivative D S C (x, q) (r, y)
  have hcontrol : controlGeometryConditions D S C := hN.2.2.2.1
  have hcore {r : ℝ} (hr : r ∈ Icc (C.left m) (C.right m)) :
      r ∈ Ioo D.a D.b :=
    ⟨(hcontrol.1 m).1.trans_le hr.1, hr.2.trans_lt (hcontrol.1 m).2.2⟩
  have hqmem {q : ℝ} (hq : q ∈ Ioo (-δ) δ) :
      (x, q) ∈ stateNeighborhood S C base ε :=
    ⟨hx.1, (abs_lt.mpr hq).trans hδε⟩
  apply hN.minusFlow_q_zero_partial_height_response hS hT hx.1 m θ hb
    hδ hδε.le Vq Vθ
  · intro q hq p hp
    have hc := hN.minusCharacteristicSpeed_parameter_continuousAt hS hT
      (hqmem hq) hsector (p := p) ⟨hcore hp.1, mem_univ _⟩
    have hmap : ContinuousAt (fun z : PolarPoint => (q, z)) p :=
      continuousAt_const.prodMk continuousAt_id
    exact (hc.comp_of_eq hmap rfl).continuousWithinAt
  · intro q hq r hr y
    exact hN.minusCharacteristicSpeed_hasFDerivAt_q_angle hS hT
      (hqmem hq) hsector (r := r) (θ := y) (hcore ⟨hr.1.le, hr.2.le⟩)
  · refine ⟨B, hB, fun q hq r hr y => ?_⟩
    exact hbound q r y (abs_lt.mpr hq).le ⟨hr.1.le, hr.2.le⟩
  · intro p hp
    have hc := hN.characteristicQDerivative_continuousAt hS hT hx hsector
      (p := p) ⟨hcore hp.1, mem_univ _⟩
    have hmap : ContinuousAt (fun z : PolarPoint => ((0 : ℝ), z)) p :=
      continuousAt_const.prodMk continuousAt_id
    exact (hc.comp_of_eq hmap rfl).continuousWithinAt
  · intro r hr y
    exact hN.characteristicAngularDerivative_q_zero hS hT hx hsector (hcore hr) y

theorem N01Properties.minusFlow_q_zero_height_response_of_physical
    (hN : N01Properties D T S C base loss ε)
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    {x : AnnularState S} (hx : (x, 0) ∈ stateNeighborhood S C base ε)
    (hsector : stateSector S x) (m : ℕ) (θ : ℝ) :
    HasDerivAt (fun q : ℝ => C.minusFlow (x, q) m (C.right m) θ)
      (∫ r in C.left m..C.right m,
        heightSpeedVariation (stateProfile D S C x) (stateU S x)
          (r, θ - opticalTravel (stateProfile D S C x) (C.left m) r)) 0 := by
  have hcontrol : controlGeometryConditions D S C := hN.2.2.2.1
  exact hN.minusFlow_q_zero_partial_height_response_of_physical hS hT hx hsector m θ
    ⟨(hcontrol.1 m).2.1.le, le_rfl⟩

end ContinuousFlexibility.Statements
