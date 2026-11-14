module

public import ContinuousFlexibility.Analysis.OpticalHalfAiryAverage
public import ContinuousFlexibility.Analysis.ActualReferenceNegativeRadialFields
public import ContinuousFlexibility.Analysis.N01OpticalRootDivision
public import ContinuousFlexibility.Analysis.SolveReturnEquations

/-!
# The stored negative reference chart is the integral Airy coordinate

Both orientations use the actual full-component optical travel. After
the exact simple-zero factorization, the inward integral is precisely
the Airy average already selected on the whole optical half. No chart is
reselected, and no point outside that half enters the identity.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter MeasureTheory ContinuousFlexibility.Statements
open scoped ContDiff Topology

theorem n04b_reference_orientedTravel_inwardIntegral
    {D : ReferenceData} {S : PhysicalSpacesData} {C : NonlinearGeometryData S}
    (hD : RadialProfileGeometry D) (hC : controlGeometryConditions D S C)
    (m : ℕ) (side : Bool) {x : ℝ}
    (hx : x ∈ Icc (0 : ℝ) (C.right m - C.left m)) :
    n04bTravelOrientation (C.travel m) side
        (opticalTravel D.w (C.left m)
          (inwardComponentPoint (C.left m) (C.right m) side x)) =
      ∫ t in (0 : ℝ)..x,
        opticalSpeed D.w (inwardComponentPoint (C.left m) (C.right m) side t) := by
  cases side
  · change (∫ r in C.left m..C.left m + x, opticalSpeed D.w r) =
      ∫ t in (0 : ℝ)..x, opticalSpeed D.w (C.left m + t)
    symm
    simpa only [add_zero] using
      intervalIntegral.integral_comp_add_left (opticalSpeed D.w)
        (a := (0 : ℝ)) (b := x) (C.left m)
  · have hy : C.right m - x ∈ Icc (C.left m) (C.right m) := by
      constructor <;> linarith only [hx.1, hx.2]
    have hv := n04b_referenceOpticalSpeed_continuousOn hD hC m
    have hiL := (hv.mono (Icc_subset_Icc le_rfl hy.2)).intervalIntegrable_of_Icc
      (μ := volume) hy.1
    have hiR := (hv.mono (Icc_subset_Icc hy.1 le_rfl)).intervalIntegrable_of_Icc
      (μ := volume) hy.2
    have hadd := intervalIntegral.integral_add_adjacent_intervals hiL hiR
    have hwhole : (∫ r in C.left m..C.right m, opticalSpeed D.w r) = C.travel m :=
      n04b_referenceTravel_right hC m
    rw [hwhole] at hadd
    change C.travel m - (∫ r in C.left m..C.right m - x, opticalSpeed D.w r) =
      ∫ t in (0 : ℝ)..x, opticalSpeed D.w (C.right m - t)
    rw [intervalIntegral.integral_comp_sub_left, sub_zero]
    linarith only [hadd]

/-- The actual oriented root reparametrization is equal on a complete
closed inward interval to the selected integral-average formula. -/
theorem n04b_reference_rootHalfCoordinate_eq_airy
    {D : ReferenceData} {S : PhysicalSpacesData} {C : NonlinearGeometryData S}
    (hD : RadialProfileGeometry D) (hC : controlGeometryConditions D S C)
    (m : ℕ) (side : Bool) {g c : ℝ → ℝ} {d x : ℝ}
    (hd : d ≤ C.right m - C.left m)
    (hfactor : ∀ t ∈ Icc (0 : ℝ) d,
      n01aOpticalRadicand D.w
        (inwardComponentPoint (C.left m) (C.right m) side t) = t * g t)
    (hc : ∀ t ∈ Icc (0 : ℝ) d, c t = Real.sqrt (g t))
    (hx : x ∈ Icc (0 : ℝ) d) (hA : 0 ≤ n06AiryAverage c x) :
    n04bRootHalfCoordinate (C.travel m) side
        (opticalTravel D.w (C.left m)
          (inwardComponentPoint (C.left m) (C.right m) side x)) =
      n06AiryRadialCoordinate c x := by
  have htravel := n04b_reference_orientedTravel_inwardIntegral hD hC m side
    (show x ∈ Icc (0 : ℝ) (C.right m - C.left m) from ⟨hx.1, hx.2.trans hd⟩)
  have hintegral :
      (∫ t in (0 : ℝ)..x,
        opticalSpeed D.w (inwardComponentPoint (C.left m) (C.right m) side t)) =
      ∫ t in (0 : ℝ)..x, Real.sqrt (t * g t) := by
    apply intervalIntegral.integral_congr
    intro t ht
    have ht' : t ∈ Icc (0 : ℝ) x := by simpa only [uIcc_of_le hx.1] using ht
    change Real.sqrt (n01aOpticalRadicand D.w
      (inwardComponentPoint (C.left m) (C.right m) side t)) = _
    rw [hfactor t ⟨ht'.1, ht'.2.trans hx.2⟩]
  unfold n04bRootHalfCoordinate n04bRootCoordinate
  rw [htravel, hintegral]
  calc
    (3 * (∫ t in (0 : ℝ)..x, Real.sqrt (t * g t)) / 2) ^ (2 / 3 : ℝ) =
        ((3 / 2 : ℝ) * (∫ t in (0 : ℝ)..x, Real.sqrt (t * g t))) ^ (2 / 3 : ℝ) := by
      congr 1
      ring
    _ = n06AiryRadialCoordinate c x :=
      opticalHalf_rootCoordinate_eq_airyRadialCoordinate hx hc hA

/-- This equality concerns the stored chart of the original typed atlas
at every interior point of the displayed inward half. -/
theorem n04Coordinates_actual_reference_negative_airy_chart
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {R : ReturnEquationData S}
    {L : ReturnCorrectionData S} {base loss : ℕ} {ε : ℝ}
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (hN : NonlinearPropertiesThrough03 D T S C R L base loss ε)
    (hfield : N04bFieldRegularity D S C L base ε) (e : ℕ ≃ N04PieceIndex D)
    (m : ℕ) (side : Bool) {g c : ℝ → ℝ} {d : ℝ}
    (hd : d ≤ C.right m - C.left m)
    (hfactor : ∀ t ∈ Icc (0 : ℝ) d,
      n01aOpticalRadicand D.w
        (inwardComponentPoint (C.left m) (C.right m) side t) = t * g t)
    (hc : ∀ t ∈ Icc (0 : ℝ) d, c t = Real.sqrt (g t))
    {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) d) (hA : 0 ≤ n06AiryAverage c x) (θ : ℝ) :
    let K := n04bActualTypedAtlas hT hS hN hfield e
    K.chart (C.referenceState, 0) (e.symm (.inl (m, side)))
        (inwardComponentPoint (C.left m) (C.right m) side x, θ) =
      (n06AiryRadialCoordinate c x, θ) := by
  dsimp only
  let K := n04bActualTypedAtlas hT hS hN hfield e
  let k := e.symm (.inl (m, side))
  let z₀ : AnnularState S × ℝ := (C.referenceState, 0)
  let p : PolarPoint := (inwardComponentPoint (C.left m) (C.right m) side x, θ)
  have hp : p ∈ Ioo (C.left m) (C.right m) ×ˢ (univ : Set ℝ) := by
    refine ⟨?_, mem_univ _⟩
    have hxL := hx.2.trans_le hd
    cases side <;> simp only [p, inwardComponentPoint, Bool.false_eq_true, ↓reduceIte]
      <;> constructor <;> linarith only [hx.1, hxL]
  have href : z₀ ∈ stateNeighborhood S C base ε :=
    reference_mem_stateNeighborhood S C base hN.1.1.2.1
  have hsref : stateSector S z₀.1 := hN.1.1.2.2.1.stateSector
  have hg := n04bActualTypedAtlas_negative_component_germs
    hT hS hN hfield e href hsref k m side (e.apply_symm_apply _) hp
  rw [hg.1.self_of_nhds]
  change n04bRootStripChart (C.travel m) side (n04bActualTravelChart S C L z₀ m p) = _
  rw [n04b_reference_actualTravelChart hN.1.1.2.2.1 hfield m
    ⟨hp.1.1.le, hp.1.2.le⟩ θ]
  change (n04bRootHalfCoordinate (C.travel m) side
    (opticalTravel D.w (C.left m) p.1), θ) = _
  rw [n04b_reference_rootHalfCoordinate_eq_airy
    (n04b_profileGeometry_of_through03 hN) hN.1.1.2.2.2.1 m side hd hfactor hc
    ⟨hx.1.le, hx.2.le⟩ hA]

end ContinuousFlexibility.Analysis
