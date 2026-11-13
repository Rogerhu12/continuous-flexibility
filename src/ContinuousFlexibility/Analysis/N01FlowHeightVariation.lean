import ContinuousFlexibility.Analysis.N01FlowParameterVariation
import ContinuousFlexibility.Analysis.PolarHeightCharacteristicVariation

/-!
# The actual height response of the N01 return flow

The first parameter derivative of the actual minus return is identified
with the integral of the actual height-speed variation along the radial
optical trajectory. The formula uses the N01 flow itself and the exact
polar characteristic coefficients.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open Set Filter MeasureTheory
open ContinuousFlexibility.Analysis
open scoped Topology ContDiff

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {base loss : ℕ} {ε : ℝ}

theorem N01Properties.minusFlow_q_zero_height_response
    (hN : N01Properties D T S C base loss ε)
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    {x : AnnularState S}
    (hx : stateGrading S base (x - C.referenceState) < ε)
    (m : ℕ) (θ : ℝ)
    {δ : ℝ} (hδ : 0 < δ) (hδε : δ ≤ ε)
    (Vq Vθ : ℝ → ℝ → ℝ → ℝ)
    (hV : ∀ q ∈ Ioo (-δ) δ,
      ContinuousOn
        (fun p : PolarPoint => minusCharacteristicSpeed
          (originalCoefficients D S C (x, q)) p)
        (Icc (C.left m) (C.right m) ×ˢ (univ : Set ℝ)))
    (hjet : ∀ q ∈ Ioo (-δ) δ, ∀ r ∈ Ioo (C.left m) (C.right m), ∀ y : ℝ,
      HasFDerivAt
        (fun p : ℝ × ℝ => minusCharacteristicSpeed
          (originalCoefficients D S C (x, p.1)) (r, p.2))
        ((ContinuousLinearMap.toSpanSingleton ℝ (Vq q r y)).coprod
          (ContinuousLinearMap.toSpanSingleton ℝ (Vθ q r y))) (q, y))
    (hbounded : ∃ K : ℝ, 0 ≤ K ∧ ∀ q ∈ Ioo (-δ) δ,
      ∀ r ∈ Ioo (C.left m) (C.right m), ∀ y : ℝ,
        |Vq q r y| ≤ K ∧ |Vθ q r y| ≤ K)
    (hVq0 : ContinuousOn (fun p : PolarPoint => Vq 0 p.1 p.2)
      (Icc (C.left m) (C.right m) ×ˢ (univ : Set ℝ)))
    (hVθ0 : ∀ r ∈ Icc (C.left m) (C.right m), ∀ y : ℝ, Vθ 0 r y = 0) :
    HasDerivAt (fun q : ℝ => C.minusFlow (x, q) m (C.right m) θ)
      (∫ r in C.left m..C.right m,
        heightSpeedVariation (stateProfile D S C x) (stateU S x)
          (r, θ - opticalTravel (stateProfile D S C x) (C.left m) r)) 0 := by
  have hd := hN.minusFlow_q_zero_hasDerivAt_of_speed hx m θ hδ hδε
    Vq Vθ hV hjet hbounded hVq0 hVθ0
  have hcontrol : controlGeometryConditions D S C := hN.2.2.2.1
  have hab : C.left m < C.right m := (hcontrol.1 m).2.1
  have hzero : (0 : ℝ) ∈ Ioo (-δ) δ := ⟨neg_lt_zero.mpr hδ, hδ⟩
  have hx0 : (x, (0 : ℝ)) ∈ stateNeighborhood S C base ε :=
    ⟨hx, by simpa only [abs_zero] using hN.2.1⟩
  apply hd.congr_deriv
  apply intervalIntegral.integral_congr_ae
  apply ae_uIoc_imp_of_forall_Ioo hab.le
  intro r hr
  let y := C.minusFlow (x, 0) m r θ
  have hp : (r, y) ∈ annularOpen D :=
    ⟨⟨(hcontrol.1 m).1.trans hr.1, hr.2.trans (hcontrol.1 m).2.2⟩, mem_univ _⟩
  have hq : HasDerivAt
      (fun q : ℝ => minusCharacteristicSpeed (originalCoefficients D S C (x, q)) (r, y))
      (Vq 0 r y) 0 := by
    have h := (hjet 0 hzero r hr y).comp_hasDerivAt (0 : ℝ)
      ((hasDerivAt_id (0 : ℝ)).prodMk (hasDerivAt_const (0 : ℝ) y))
    simpa [Function.comp_def, smul_eq_mul] using h
  have heq : Vq 0 r y =
      heightSpeedVariation (stateProfile D S C x) (stateU S x) (r, y) :=
    hq.unique (hN.hasDerivAt_minusCharacteristicSpeed_q_zero hS hT x hp)
  change Vq 0 r y = _
  rw [heq]
  dsimp only [y]
  rw [hN.minusFlow_zero_eq_opticalTravel hS hT hx0 m θ ⟨hr.1.le, hr.2.le⟩]

end ContinuousFlexibility.Statements
