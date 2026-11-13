import ContinuousFlexibility.Analysis.N04NegativeGeometryChartTowers
import ContinuousFlexibility.Analysis.N04NegativeGeometryHeightTowers
import ContinuousFlexibility.Analysis.N04NegativeGeometryTravelInverseContinuity
import ContinuousFlexibility.Analysis.N04NegativeGeometryPlanarParameterInverse
import ContinuousFlexibility.Analysis.N04NegativeInverseImplicitIdentification
import ContinuousFlexibility.Analysis.N04NegativeGeometrySpatialRegularity
import ContinuousFlexibility.Analysis.N04RealizationLeadNegativeSplit
import ContinuousFlexibility.Analysis.N01cPhysicalFlowGraph

/-!
# The actual negative inverse on fixed parameter and canonical domains

The forward chart is considered on its entire original physical component.
The actual inverse takes its values there even when the physical half-cut
moves with the state.  All identities concern the stored chosen functions.
No regularity of a different representative is substituted.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis.N04RealizationStart

open Set ContinuousFlexibility.Statements
open scoped ContDiff

variable (W : N04RealizationStart)

/-- The angular coordinate of the actual travel chart is strictly regular.
Its derivative is the average of the two positive first-integral derivatives. -/
theorem negativeTravel_angularPartial_pos (m : ℕ)
    {z : StateDirections W.S × ℝ}
    (hz : z ∈ sectorNeighborhood W.S W.base W.ε W.ε)
    {p : PolarPoint} (hp : p ∈ Ioo (W.C.left m) (W.C.right m) ×ˢ (univ : Set ℝ)) :
    0 < angularPartial (fun q =>
      (n04bActualTravelChart W.S W.C W.L (liftSectorParameter W.S W.C z) m q).2) p := by
  let w := liftSectorParameter W.S W.C z
  have hw := liftSectorParameter_mem_stateNeighborhood (C := W.C) hz le_rfl
  have hs := W.through03.1.1.2.2.1.liftSectorParameter_sector z
  have hΦ := n04b_actualMinusFlow_regular W.through03 W.hS W.hT W.field hw hs m
  have hL := stateLeftChart_contDiff W.S w m (W.hS.2.1 (3 / 4 : ℝ))
  have hLpos : ∀ θ, 0 < deriv (stateLeftChart W.S w.1 m) θ := by
    intro θ
    exact lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1 / 2)
      (W.through03.1.1.2.2.2.2.2.2.2.1 w hw hs m θ).1
  let U := n04bPlusFirstIntegral (fun q => W.L.minusFlow w m q.1 q.2)
    (stateLeftChart W.S w.1 m)
  let V := n04bMinusFirstIntegral (fun q => W.L.minusFlow w m q.1 q.2)
    (stateLeftChart W.S w.1 m)
  have hU : DifferentiableAt ℝ U p :=
    ((n04b_plusFirstIntegral_smooth hΦ Real.pi_ne_zero hL).contDiffAt
      ((isOpen_Ioo.prod isOpen_univ).mem_nhds hp)).differentiableAt (by simp)
  have hV : DifferentiableAt ℝ V p :=
    ((n04b_minusFirstIntegral_smooth hΦ Real.pi_ne_zero hL).contDiffAt
      ((isOpen_Ioo.prod isOpen_univ).mem_nhds hp)).differentiableAt (by simp)
  have hd : HasFDerivAt (fun q => (characteristicTravelChart U V q).2)
      ((1 / 2 : ℝ) • (fderiv ℝ U p + fderiv ℝ V p)) p :=
    (hU.hasFDerivAt.fun_add hV.hasFDerivAt).const_mul (1 / 2 : ℝ)
  change 0 < angularPartial (fun q => (characteristicTravelChart U V q).2) p
  unfold angularPartial
  rw [hd.fderiv]
  simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.add_apply, smul_eq_mul]
  exact mul_pos (by norm_num)
    (add_pos (n04b_plusFirstIntegral_angularPartial_pos hΦ Real.pi_ne_zero hL hLpos hp)
      (n04b_minusFirstIntegral_angularPartial_pos hΦ Real.pi_ne_zero hL hLpos hp))

/-- The two endpoint lifts and the positive interior angular derivative give
strict angular monotonicity on each closed physical slice. -/
theorem negativeTravel_angle_strictMono (m : ℕ)
    {z : StateDirections W.S × ℝ}
    (hz : z ∈ sectorNeighborhood W.S W.base W.ε W.ε)
    {r : ℝ} (hr : r ∈ Icc (W.C.left m) (W.C.right m)) :
    StrictMono (fun θ =>
      (n04bActualTravelChart W.S W.C W.L (liftSectorParameter W.S W.C z) m (r, θ)).2) := by
  let w := liftSectorParameter W.S W.C z
  have hw := liftSectorParameter_mem_stateNeighborhood (C := W.C) hz le_rfl
  have hs := W.through03.1.1.2.2.1.liftSectorParameter_sector z
  apply strictMono_travelStrip_angle
    (n04b_actualTravelChart_smooth W.through03 W.hS W.hT W.field hw hs m)
    (fun _ hp => W.negativeTravel_angularPartial_pos m hz hp) ?_ ?_ hr
  · have he : (fun θ => (n04bActualTravelChart W.S W.C W.L w m
        (W.C.left m, θ)).2) = stateLeftChart W.S w.1 m := by
      funext θ
      exact congrArg Prod.snd
        (n04b_actualTravelChart_endpoints W.through03 W.hS W.hT W.field hw hs m θ).1
    rw [he]
    exact strictMono_of_deriv_pos (fun θ => lt_of_lt_of_le
      (by norm_num : (0 : ℝ) < 1 / 2)
      (W.through03.1.1.2.2.2.2.2.2.2.1 w hw hs m θ).1)
  · have he : (fun θ => (n04bActualTravelChart W.S W.C W.L w m
        (W.C.right m, θ)).2) = rightChartCandidate W.S W.C w m := by
      funext θ
      exact congrArg Prod.snd
        (n04b_actualTravelChart_endpoints W.through03 W.hS W.hT W.field hw hs m θ).2
    rw [he]
    exact strictMono_of_deriv_pos
      (N01Properties.rightChart_deriv_pos W.S W.C w m W.through03.1.1 hw hs)

theorem negativeTravel_angle_surjective (m : ℕ)
    {z : StateDirections W.S × ℝ}
    (hz : z ∈ sectorNeighborhood W.S W.base W.ε W.ε)
    {r : ℝ} (hr : r ∈ Icc (W.C.left m) (W.C.right m)) :
    Function.Surjective (fun θ =>
      (n04bActualTravelChart W.S W.C W.L (liftSectorParameter W.S W.C z) m (r, θ)).2) := by
  have hw := liftSectorParameter_mem_stateNeighborhood (C := W.C) hz le_rfl
  have hs := W.through03.1.1.2.2.1.liftSectorParameter_sector z
  apply surjective_of_continuous_periodic_lift Real.pi_ne_zero
  · exact ((n04b_actualTravelChart_continuous W.through03 W.hS W.hT W.field hw hs m).snd)
      .comp_continuous (continuous_const.prodMk continuous_id)
        (fun θ => ⟨hr, mem_univ θ⟩)
  · intro θ
    exact congrArg Prod.snd
      (n04b_actualTravelChart_period_add W.through03 W.hS W.hT W.field hw hs m hr θ)

/-- The literal travel inverse is continuous for the original state topology,
jointly with its canonical point. -/
theorem negativeTravelInverse_continuousOn (m : ℕ) :
    ContinuousOn (fun x : (StateDirections W.S × ℝ) × PolarPoint =>
      n04bActualTravelInverse W.S W.C W.L (liftSectorParameter W.S W.C x.1) m x.2)
      (sectorNeighborhood W.S W.base W.ε W.ε ×ˢ
        (Ioo (0 : ℝ) (W.C.travel m) ×ˢ univ)) := by
  apply n04NegativeGeometry_travelInverse_continuousOn
    (W.negativeTravelJointTower m).continuousOn
    (fun z hz r hr => W.negativeTravel_angle_strictMono m hz (Ioo_subset_Icc_self hr))
    (fun z hz r hr => W.negativeTravel_angle_surjective m hz (Ioo_subset_Icc_self hr))
  · intro z hz θ
    have hw := liftSectorParameter_mem_stateNeighborhood (C := W.C) hz le_rfl
    have hs := W.through03.1.1.2.2.1.liftSectorParameter_sector z
    exact (strictMonoOn_angleNormalizedTravel
      (n04b_actualTravelChart_continuous W.through03 W.hS W.hT W.field hw hs m)
      (n04b_actualTravelChart_smooth W.through03 W.hS W.hT W.field hw hs m)
      (fun _ hp => W.negativeTravel_angularPartial_pos m hz hp)
      (fun _ hp => n04b_actualTravelChart_jacobian_pos W.through03 W.hS W.hT W.field hw hs m hp)
      (fun r hr => W.negativeTravel_angle_strictMono m hz hr)
      (fun r hr => W.negativeTravel_angle_surjective m hz hr) θ).mono Ioo_subset_Icc_self
  · intro x hx
    exact (n04b_actualTravelInverse_spec W.through03 W.hS W.hT W.field
      (liftSectorParameter_mem_stateNeighborhood hx.1 le_rfl)
      (W.through03.1.1.2.2.1.liftSectorParameter_sector x.1) m).1 hx.2
  · intro x hx
    exact (n04b_actualTravelInverse_spec W.through03 W.hS W.hT W.field
      (liftSectorParameter_mem_stateNeighborhood hx.1 le_rfl)
      (W.through03.1.1.2.2.1.liftSectorParameter_sector x.1) m).2.2.1 hx.2

/-- The fixed root-strip inverse lands in the full travel strip. -/
theorem negativeRootStripInverse_mapsTo (m : ℕ) (side : Bool) :
    MapsTo (n04bRootStripInverse (W.C.travel m) side)
      (Ioo (0 : ℝ) (n04bRootCutRadius (W.C.travel m)) ×ˢ (univ : Set ℝ))
      (Ioo (0 : ℝ) (W.C.travel m) ×ˢ (univ : Set ℝ)) := by
  have hT := n04b_actualTravel_positive W.through03 W.hS W.hT W.field
    (n04b_reference_valid_of_through03 W.through03).1
    (n04b_reference_valid_of_through03 W.through03).2 m
  intro q hq
  have hq' := (n04b_rootStrip_chart_data hT side).2.1 hq
  exact ⟨n04b_travelHalfInterval_subset hT side hq'.1, hq'.2⟩

/-- The chosen inverse agrees with the explicit travel inverse on its fixed
canonical strip, so its parameter continuity is independent of the choice. -/
theorem negativeInverse_continuousOn (m : ℕ) (side : Bool) :
    ContinuousOn (fun x : (StateDirections W.S × ℝ) × PolarPoint =>
      n04bActualNegativeInverse W.hT W.hS W.through03 W.field
        (liftSectorParameter W.S W.C x.1) m side x.2)
      (sectorNeighborhood W.S W.base W.ε W.ε ×ˢ
        (Ioo (0 : ℝ) (n04bRootCutRadius (W.C.travel m)) ×ˢ univ)) := by
  have hc := (W.negativeTravelInverse_continuousOn m).comp
    (continuous_fst.prodMk
      ((n04b_continuous_rootStripInverse (W.C.travel m) side).comp continuous_snd)).continuousOn
    (fun x hx => ⟨hx.1, W.negativeRootStripInverse_mapsTo m side hx.2⟩)
  exact hc.congr (fun x hx =>
    ((n04bActualNegativeFunctions_spec W.hT W.hS W.through03 W.field
      (liftSectorParameter_mem_stateNeighborhood hx.1 le_rfl)
      (W.through03.1.1.2.2.1.liftSectorParameter_sector x.1) m side).open_inverse_eq hx.2).symm)

/-- The whole-component forward map is injective; the inverse root change
recovers the travel chart on this larger fixed domain. -/
theorem negativeChart_injOn_component (m : ℕ) (side : Bool)
    {z : StateDirections W.S × ℝ}
    (hz : z ∈ sectorNeighborhood W.S W.base W.ε W.ε) :
    InjOn (n04bActualNegativeChart W.hT W.hS W.through03 W.field
      (liftSectorParameter W.S W.C z) m side)
      (Ioo (W.C.left m) (W.C.right m) ×ˢ (univ : Set ℝ)) := by
  have hw := liftSectorParameter_mem_stateNeighborhood (C := W.C) hz le_rfl
  have hs := W.through03.1.1.2.2.1.liftSectorParameter_sector z
  have H := n04bActualNegativeFunctions_spec W.hT W.hS W.through03 W.field hw hs m side
  have hBij := n04b_actualTravelChart_bijOn W.through03 W.hS W.hT W.field hw hs m
  intro p hp q hq he
  apply hBij.injOn hp hq
  rw [(H.component_chart_germ hp).self_of_nhds,
    (H.component_chart_germ hq).self_of_nhds] at he
  have hh := congrArg (n04bRootStripInverse (W.C.travel m) side) he
  exact (n04bRootStripInverse_chart_of_oriented_nonneg _ side
      (n04b_travelOrientation_pos_of_fullStrip side (hBij.mapsTo hp).1).le).symm.trans
    (hh.trans (n04bRootStripInverse_chart_of_oriented_nonneg _ side
      (n04b_travelOrientation_pos_of_fullStrip side (hBij.mapsTo hq).1).le))

theorem negativeChart_jacobian_ne_zero (m : ℕ) (side : Bool)
    {z : StateDirections W.S × ℝ}
    (hz : z ∈ sectorNeighborhood W.S W.base W.ε W.ε)
    {p : PolarPoint} (hp : p ∈ Ioo (W.C.left m) (W.C.right m) ×ˢ (univ : Set ℝ)) :
    planeJacobian (n04bActualNegativeChart W.hT W.hS W.through03 W.field
      (liftSectorParameter W.S W.C z) m side) p ≠ 0 := by
  have hw := liftSectorParameter_mem_stateNeighborhood (C := W.C) hz le_rfl
  have hs := W.through03.1.1.2.2.1.liftSectorParameter_sector z
  have H := n04bActualNegativeFunctions_spec W.hT W.hS W.through03 W.field hw hs m side
  have he := H.component_chart_germ hp
  have hj : planeJacobian (n04bActualNegativeChart W.hT W.hS W.through03 W.field
      (liftSectorParameter W.S W.C z) m side) p =
      planeJacobian (n04bRootPhysicalChart
        (n04bActualTravelChart W.S W.C W.L (liftSectorParameter W.S W.C z) m)
        (W.C.travel m) side) p := by
    unfold planeJacobian
    rw [he.fderiv_eq]
  rw [hj]
  exact (n04b_actualRootPhysical_regular_at W.through03 W.hS W.hT W.field hw hs m side hp).2.2.1

theorem negativeInverse_maps_component (m : ℕ) (side : Bool)
    {z : StateDirections W.S × ℝ}
    (hz : z ∈ sectorNeighborhood W.S W.base W.ε W.ε) :
    MapsTo (n04bActualNegativeInverse W.hT W.hS W.through03 W.field
      (liftSectorParameter W.S W.C z) m side)
      (Ioo (0 : ℝ) (n04bRootCutRadius (W.C.travel m)) ×ˢ (univ : Set ℝ))
      (Ioo (W.C.left m) (W.C.right m) ×ˢ (univ : Set ℝ)) := by
  have hw := liftSectorParameter_mem_stateNeighborhood (C := W.C) hz le_rfl
  have hs := W.through03.1.1.2.2.1.liftSectorParameter_sector z
  have H := n04bActualNegativeFunctions_spec W.hT W.hS W.through03 W.field hw hs m side
  intro q hq
  exact n04b_actualNegativeDomain_subset_component W.C W.L _ m side
    ((H.open_chart_data W.through03 W.hS W.hT W.field hw hs).2.1 hq)

theorem negativeInverse_right (m : ℕ) (side : Bool)
    {z : StateDirections W.S × ℝ}
    (hz : z ∈ sectorNeighborhood W.S W.base W.ε W.ε)
    {q : PolarPoint}
    (hq : q ∈ Ioo (0 : ℝ) (n04bRootCutRadius (W.C.travel m)) ×ˢ (univ : Set ℝ)) :
    n04bActualNegativeChart W.hT W.hS W.through03 W.field
      (liftSectorParameter W.S W.C z) m side
      (n04bActualNegativeInverse W.hT W.hS W.through03 W.field
        (liftSectorParameter W.S W.C z) m side q) = q := by
  have hw := liftSectorParameter_mem_stateNeighborhood (C := W.C) hz le_rfl
  have hs := W.through03.1.1.2.2.1.liftSectorParameter_sector z
  exact ((n04bActualNegativeFunctions_spec W.hT W.hS W.through03 W.field hw hs m side)
    .open_chart_data W.through03 W.hS W.hT W.field hw hs).2.2.2 q hq

/-- Angular translation of the actual inverse follows from injectivity of
the same stored forward chart. -/
theorem negativeInverse_period (m : ℕ) (side : Bool)
    {z : StateDirections W.S × ℝ}
    (hz : z ∈ sectorNeighborhood W.S W.base W.ε W.ε)
    {q : PolarPoint}
    (hq : q ∈ Ioo (0 : ℝ) (n04bRootCutRadius (W.C.travel m)) ×ˢ (univ : Set ℝ)) :
    n04bActualNegativeInverse W.hT W.hS W.through03 W.field
        (liftSectorParameter W.S W.C z) m side (q + (0, Real.pi)) =
      n04bActualNegativeInverse W.hT W.hS W.through03 W.field
        (liftSectorParameter W.S W.C z) m side q + (0, Real.pi) := by
  have hw := liftSectorParameter_mem_stateNeighborhood (C := W.C) hz le_rfl
  have hs := W.through03.1.1.2.2.1.liftSectorParameter_sector z
  have H := n04bActualNegativeFunctions_spec W.hT W.hS W.through03 W.field hw hs m side
  have hq' : q + (0, Real.pi) ∈
      Ioo (0 : ℝ) (n04bRootCutRadius (W.C.travel m)) ×ˢ (univ : Set ℝ) :=
    ⟨by simpa only [Prod.fst_add, add_zero] using hq.1, mem_univ _⟩
  have hp := W.negativeInverse_maps_component m side hz hq
  apply W.negativeChart_injOn_component m side hz
    (W.negativeInverse_maps_component m side hz hq')
    ⟨by simpa only [Prod.fst_add, add_zero] using hp.1, mem_univ _⟩
  rw [W.negativeInverse_right m side hz hq',
    (H.period W.through03 W.hS W.hT W.field hw hs hp).1,
    W.negativeInverse_right m side hz hq]

/-- The height evaluated at the actual inverse is periodic on the fixed
canonical strip. -/
theorem negativePulledHeight_period (m : ℕ) (side : Bool)
    {z : StateDirections W.S × ℝ}
    (hz : z ∈ sectorNeighborhood W.S W.base W.ε W.ε)
    {q : PolarPoint}
    (hq : q ∈ Ioo (0 : ℝ) (n04bRootCutRadius (W.C.travel m)) ×ˢ (univ : Set ℝ)) :
    n04bActualNegativeHeight W.hT W.hS W.through03 W.field
      (liftSectorParameter W.S W.C z) m side
      (n04bActualNegativeInverse W.hT W.hS W.through03 W.field
        (liftSectorParameter W.S W.C z) m side (q + (0, Real.pi))) =
    n04bActualNegativeHeight W.hT W.hS W.through03 W.field
      (liftSectorParameter W.S W.C z) m side
      (n04bActualNegativeInverse W.hT W.hS W.through03 W.field
        (liftSectorParameter W.S W.C z) m side q) := by
  rw [W.negativeInverse_period m side hz hq]
  have hw := liftSectorParameter_mem_stateNeighborhood (C := W.C) hz le_rfl
  have hs := W.through03.1.1.2.2.1.liftSectorParameter_sector z
  exact ((n04bActualNegativeFunctions_spec W.hT W.hS W.through03 W.field hw hs m side)
    .period W.through03 W.hS W.hT W.field hw hs
      (W.negativeInverse_maps_component m side hz hq)).2

/-- Every finite affine state slice of the stored inverse is jointly smooth.
The implicit theorem uses the fixed whole component, and therefore remains
valid at points whose moving physical half differs from the reference half. -/
theorem negativeInverse_contDiffOn_finiteAffine
    {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]
    (m : ℕ) (side : Bool) (z₀ : StateDirections W.S × ℝ)
    (L : P →L[ℝ] (StateDirections W.S × ℝ)) :
    ContDiffOn ℝ ∞ (fun x : P × PolarPoint =>
      n04bActualNegativeInverse W.hT W.hS W.through03 W.field
        (liftSectorParameter W.S W.C (z₀ + L x.1)) m side x.2)
      (((fun p => z₀ + L p) ⁻¹' sectorNeighborhood W.S W.base W.ε W.ε) ×ˢ
        (Ioo (0 : ℝ) (n04bRootCutRadius (W.C.travel m)) ×ˢ univ)) := by
  apply n04NegativeGeometry_inverse_contDiffOn_finiteAffine
    (W.negativeChartJointTower m side)
    (sectorNeighborhood_isOpen W.S W.base W.ε W.ε)
    (isOpen_Ioo.prod isOpen_univ) (isOpen_Ioo.prod isOpen_univ)
    (fun x hx => W.negativeChart_jacobian_ne_zero m side hx.1 hx.2)
    (fun z hz => W.negativeChart_injOn_component m side hz)
    (fun x hx => W.negativeInverse_maps_component m side hx.1 hx.2)
    (fun x hx => W.negativeInverse_right m side hx.1 hx.2)

/-- The actual chosen inverse has one all-order joint directional tower
on the original sector neighborhood and its fixed canonical root strip. -/
def negativeInverseJointTower (m : ℕ) (side : Bool) :
    SmoothDirections
      (sectorNeighborhood W.S W.base W.ε W.ε ×ˢ
        (Ioo (0 : ℝ) (n04bRootCutRadius (W.C.travel m)) ×ˢ univ))
      (fun x : (StateDirections W.S × ℝ) × PolarPoint =>
        n04bActualNegativeInverse W.hT W.hS W.through03 W.field
          (liftSectorParameter W.S W.C x.1) m side x.2) :=
  n04NegativeInverse_jointTower (W.negativeChartJointTower m side)
    (sectorNeighborhood_isOpen W.S W.base W.ε W.ε)
    (isOpen_Ioo.prod isOpen_univ) (isOpen_Ioo.prod isOpen_univ)
    (W.negativeInverse_continuousOn m side)
    (fun x hx => W.negativeChart_jacobian_ne_zero m side hx.1 hx.2)
    (fun z hz => W.negativeChart_injOn_component m side hz)
    (fun x hx => W.negativeInverse_maps_component m side hx.1 hx.2)
    (fun x hx => W.negativeInverse_right m side hx.1 hx.2)

/-- Composition of the actual height tower with the actual inverse point.
The graph retains the original sector parameter, so every derivative
differentiates both the height and its moving argument. -/
def negativePulledHeightJointTower (m : ℕ) (side : Bool) :
    SmoothDirections
      (sectorNeighborhood W.S W.base W.ε W.ε ×ˢ
        (Ioo (0 : ℝ) (n04bRootCutRadius (W.C.travel m)) ×ˢ univ))
      (fun x : (StateDirections W.S × ℝ) × PolarPoint =>
        n04bActualNegativeHeight W.hT W.hS W.through03 W.field
          (liftSectorParameter W.S W.C x.1) m side
          (n04bActualNegativeInverse W.hT W.hS W.through03 W.field
            (liftSectorParameter W.S W.C x.1) m side x.2)) := by
  letI : LocallyConvexSpace ℝ (StateDirections W.S × ℝ) :=
    (sectorPairGrading_withSeminorms W.S).toLocallyConvexSpace
  let J := W.negativeInverseJointTower m side
  let P := smoothDirectionsLinearOn
    (ContinuousLinearMap.fst ℝ (StateDirections W.S × ℝ) PolarPoint) J.open_domain
  exact smoothDirections_realCompTVS (smoothDirectionsProd P J)
    (W.negativeHeightJointTower m side)
    (fun x hx => ⟨hx.1, W.negativeInverse_maps_component m side hx.1 hx.2⟩)

end ContinuousFlexibility.Analysis.N04RealizationStart

namespace ContinuousFlexibility.Analysis

open Set ContinuousFlexibility.Statements CanonicalGeometry
open scoped ContDiff

/-- Affine canonical unit normalization of a genuine joint tower. -/
def n04NegativeInverse_canonicalUnitJointTower
    {X F : Type*} [TopologicalSpace X] [AddCommGroup X] [Module ℝ X]
    [IsTopologicalAddGroup X] [ContinuousSMul ℝ X]
    [TopologicalSpace F] [AddCommGroup F] [Module ℝ F]
    {S : PhysicalSpacesData} (K : CanonicalData S) (k : ℕ)
    {U : Set X} {Ω : Set PolarPoint} {f : X × PolarPoint → F}
    (hU : IsOpen U) (J : SmoothDirections (U ×ˢ Ω) f)
    (hmap : MapsTo (canonicalUnitPoint K k) unitStrip Ω) :
    SmoothDirections (U ×ˢ unitStrip)
      (fun x : X × PolarPoint => f (x.1, canonicalUnitPoint K k x.2)) := by
  let Q : PolarPoint →L[ℝ] PolarPoint :=
    ((K.right k - K.left k) • ContinuousLinearMap.fst ℝ ℝ ℝ).prod
      (ContinuousLinearMap.snd ℝ ℝ ℝ)
  let P : (X × PolarPoint) →L[ℝ] X × PolarPoint :=
    (ContinuousLinearMap.fst ℝ X PolarPoint).prod
      (Q.comp (ContinuousLinearMap.snd ℝ X PolarPoint))
  let c : X × PolarPoint := (0, (K.left k, 0))
  have hpoint (x : X × PolarPoint) :
      c + P x = (x.1, canonicalUnitPoint K k x.2) := by
    simp only [c, P, Q, canonicalUnitPoint, ContinuousLinearMap.prod_apply,
      ContinuousLinearMap.comp_apply, ContinuousLinearMap.coe_fst',
      ContinuousLinearMap.coe_snd', smul_apply, smul_eq_mul,
      Prod.mk_add_mk, zero_add]
  apply (J.compAffine P c (hU.prod (isOpen_Ioo.prod isOpen_univ))
    (fun x hx => ?_)).congrOn
  · rw [hpoint]
    exact ⟨hx.1, hmap hx.2⟩
  · intro x hx
    exact congrArg f (hpoint x)

namespace N04RealizationStart

variable (W : N04RealizationStart)

/-- The canonical unit point of a typed negative half lands in its exact
root strip, before applying its actual inverse. -/
theorem negativeCanonicalUnit_mapsTo
    (e : ℕ ≃ N04PieceIndex W.D) (k m : ℕ) (side : Bool)
    (hi : e k = .inl (m, side)) :
    MapsTo (canonicalUnitPoint (W.A e) k) unitStrip
      (Ioo (0 : ℝ) (n04bRootCutRadius (W.C.travel m)) ×ˢ (univ : Set ℝ)) := by
  let K := W.A e
  have hA := n04b_actualTypedAtlas_partA W.hT W.hS W.through03 W.field e
  have hcan := (n04bTypedAtlasData_negative_fields
    (C := W.C) (L := W.L) (z := (W.C.referenceState, 0)) e
    (n04bActualNegativeChart W.hT W.hS W.through03 W.field)
    (n04bActualNegativeHeight W.hT W.hS W.through03 W.field)
    (n04bActualNegativeInverse W.hT W.hS W.through03 W.field)
    (n04bActualReferenceCut W.through03) k m side hi).2.1
  have hm : MapsTo (canonicalUnitPoint K k) unitStrip (canonicalOpen W.S K k) :=
    (n04NegativeGeometry_affine_unitPoint (K.left k) (K.right k)
      (hA.referenceBounds k).2.1).2.1
  simpa only [hcan] using hm

/-- Both actual normalized inverse atoms have genuine joint towers. -/
def negativeInverseAtomJointTower
    (e : ℕ ≃ N04PieceIndex W.D) (k m : ℕ) (side : Bool)
    (hi : e k = .inl (m, side)) (a : Atom) (ha : atomIsNegativeInverse a) :
    SmoothDirections (sectorNeighborhood W.S W.base W.ε W.ε ×ˢ unitStrip)
      (fun x : (StateDirections W.S × ℝ) × PolarPoint =>
        atom W.D W.U W.S W.C W.L (W.A e)
          (liftSectorParameter W.S W.C x.1) k a x.2) := by
  let K := W.A e
  have hU := sectorNeighborhood_isOpen W.S W.base W.ε W.ε
  let J := n04NegativeInverse_canonicalUnitJointTower K k hU
    (W.negativeInverseJointTower m side) (W.negativeCanonicalUnit_mapsTo e k m side hi)
  have hinverse (z : StateDirections W.S × ℝ) :
      K.inverseChart (liftSectorParameter W.S W.C z) k =
        n04bActualNegativeInverse W.hT W.hS W.through03 W.field
          (liftSectorParameter W.S W.C z) m side :=
    (n04bTypedAtlasData_negative_fields
      (C := W.C) (L := W.L) (z := liftSectorParameter W.S W.C z) e
      (n04bActualNegativeChart W.hT W.hS W.through03 W.field)
      (n04bActualNegativeHeight W.hT W.hS W.through03 W.field)
      (n04bActualNegativeInverse W.hT W.hS W.through03 W.field)
      (n04bActualReferenceCut W.through03) k m side hi).2.2.2.2.1
  cases a <;> simp only [atomIsNegativeInverse] at ha
  · apply (J.comp_contDiff isOpen_univ
      (((contDiff_fst.sub contDiff_const).div_const (K.physicalRight k - K.physicalLeft k)) :
        ContDiff ℝ ∞ (fun p : PolarPoint =>
          (p.1 - K.physicalLeft k) / (K.physicalRight k - K.physicalLeft k))).contDiffOn
      (fun _ _ => mem_univ _)).congrOn
    intro x hx
    change (_ - K.physicalLeft k) / (K.physicalRight k - K.physicalLeft k) =
      ((K.inverseChart (liftSectorParameter W.S W.C x.1) k (canonicalUnitPoint K k x.2)).1 -
        K.physicalLeft k) / (K.physicalRight k - K.physicalLeft k)
    rw [hinverse]
  · let L : ((StateDirections W.S × ℝ) × PolarPoint) →L[ℝ] ℝ :=
      (ContinuousLinearMap.snd ℝ ℝ ℝ).comp
        (ContinuousLinearMap.snd ℝ (StateDirections W.S × ℝ) PolarPoint)
    let Jθ := smoothDirectionsLinearOn L (hU.prod (isOpen_Ioo.prod isOpen_univ))
    apply ((smoothDirectionsProd J Jθ).comp_contDiff isOpen_univ
      ((contDiff_fst.snd.sub contDiff_snd) :
        ContDiff ℝ ∞ (fun p : PolarPoint × ℝ => p.1.2 - p.2)).contDiffOn
      (fun _ _ => mem_univ _)).congrOn
    intro x hx
    change _ - x.2.2 =
      (K.inverseChart (liftSectorParameter W.S W.C x.1) k (canonicalUnitPoint K k x.2)).2 - x.2.2
    rw [hinverse]

end N04RealizationStart

namespace N04RealizationGauge

variable (G : N04RealizationGauge)

def negativeInverseAtomJointTower
    (η : (G.W.S.height (3 / 4 : ℝ)).Space) (m : ℕ) (hm : G.Neg η m)
    (a : Atom) (ha : atomIsNegativeInverse a) :
    SmoothDirections (sectorNeighborhood G.W.S G.W.base G.W.ε G.W.ε ×ˢ unitStrip)
      (fun x : (StateDirections G.W.S × ℝ) × PolarPoint => G.atomFamily η a x.1 m x.2) := by
  obtain ⟨j, hi⟩ := (G.neg_iff_inl η m).mp hm
  have hk : G.X.e₀ (G.negativeIndex j) = .inl (j.1, j.2) := G.X.e₀.apply_symm_apply _
  have haux : a ≠ .auxiliaryColumn := by
    intro he
    subst a
    cases ha
  apply (G.W.negativeInverseAtomJointTower G.X.e₀ (G.negativeIndex j) j.1 j.2 hk a ha).congrOn
  intro x hx
  exact (congrFun (G.negative_atomFamily η x.1 m j hi a haux) x.2).symm

def negativeInverseAtomMixedRegularity
    (η : (G.W.S.height (3 / 4 : ℝ)).Space) (m : ℕ) (hm : G.Neg η m)
    (a : Atom) (ha : atomIsNegativeInverse a) :
    MixedJetRegularity (sectorNeighborhood G.W.S G.W.base G.W.ε G.W.ε) unitStrip
      (fun z => G.atomFamily η a z m) :=
  n04Realization_jointMixedRegularity (G.negativeInverseAtomJointTower η m hm a ha)
    (sectorNeighborhood_isOpen G.W.S G.W.base G.W.ε G.W.ε)
    (isOpen_Ioo.prod isOpen_univ)
    ((sectorNeighborhood_convex G.W.S G.W.base G.W.ε G.W.ε).prod
      ((convex_Ioo (0 : ℝ) 1).prod convex_univ))

def negativePulledHeightJointTower
    (η : (G.W.S.height (3 / 4 : ℝ)).Space) (m : ℕ) (hm : G.Neg η m) :
    SmoothDirections (sectorNeighborhood G.W.S G.W.base G.W.ε G.W.ε ×ˢ unitStrip)
      (fun x : (StateDirections G.W.S × ℝ) × PolarPoint => G.pulledHeight η x.1 m x.2) := by
  obtain ⟨j, hi⟩ := (G.neg_iff_inl η m).mp hm
  let k := G.negativeIndex j
  have hk : G.X.e₀ k = .inl (j.1, j.2) := G.X.e₀.apply_symm_apply _
  apply (n04NegativeInverse_canonicalUnitJointTower (G.W.A G.X.e₀) k
    (sectorNeighborhood_isOpen G.W.S G.W.base G.W.ε G.W.ε)
    (G.W.negativePulledHeightJointTower j.1 j.2)
    (G.W.negativeCanonicalUnit_mapsTo G.X.e₀ k j.1 j.2 hk)).congrOn
  intro x hx
  have hf := n04bTypedAtlasData_negative_fields
    (C := G.W.C) (L := G.W.L) (z := liftSectorParameter G.W.S G.W.C x.1) G.X.e₀
    (n04bActualNegativeChart G.W.hT G.W.hS G.W.through03 G.W.field)
    (n04bActualNegativeHeight G.W.hT G.W.hS G.W.through03 G.W.field)
    (n04bActualNegativeInverse G.W.hT G.W.hS G.W.through03 G.W.field)
    (n04bActualReferenceCut G.W.through03) k j.1 j.2 hk
  symm
  rw [G.negative_pulledHeight η x.1 m j hi x.2, hf.2.2.2.2.2, hf.2.2.2.2.1]

def negativePulledHeightMixedRegularity
    (η : (G.W.S.height (3 / 4 : ℝ)).Space) (m : ℕ) (hm : G.Neg η m) :
    MixedJetRegularity (sectorNeighborhood G.W.S G.W.base G.W.ε G.W.ε) unitStrip
      (fun z => G.pulledHeight η z m) :=
  n04Realization_jointMixedRegularity (G.negativePulledHeightJointTower η m hm)
    (sectorNeighborhood_isOpen G.W.S G.W.base G.W.ε G.W.ε)
    (isOpen_Ioo.prod isOpen_univ)
    ((sectorNeighborhood_convex G.W.S G.W.base G.W.ε G.W.ε).prod
      ((convex_Ioo (0 : ℝ) 1).prod convex_univ))

theorem negativePulledHeight_period
    (η : (G.W.S.height (3 / 4 : ℝ)).Space)
    {z : StateDirections G.W.S × ℝ}
    (hz : z ∈ sectorNeighborhood G.W.S G.W.base G.W.ε G.W.ε)
    (m : ℕ) (hm : G.Neg η m) {q : PolarPoint} (hq : q ∈ unitStrip) :
    G.pulledHeight η z m (q + (0, Real.pi)) = G.pulledHeight η z m q := by
  obtain ⟨j, hi⟩ := (G.neg_iff_inl η m).mp hm
  let k := G.negativeIndex j
  have hk : G.X.e₀ k = .inl (j.1, j.2) := G.X.e₀.apply_symm_apply _
  have hf := n04bTypedAtlasData_negative_fields
    (C := G.W.C) (L := G.W.L) (z := liftSectorParameter G.W.S G.W.C z) G.X.e₀
    (n04bActualNegativeChart G.W.hT G.W.hS G.W.through03 G.W.field)
    (n04bActualNegativeHeight G.W.hT G.W.hS G.W.through03 G.W.field)
    (n04bActualNegativeInverse G.W.hT G.W.hS G.W.through03 G.W.field)
    (n04bActualReferenceCut G.W.through03) k j.1 j.2 hk
  have hshift : canonicalUnitPoint (G.W.A G.X.e₀) k (q + (0, Real.pi)) =
      canonicalUnitPoint (G.W.A G.X.e₀) k q + (0, Real.pi) := by
    simp only [canonicalUnitPoint, Prod.fst_add, Prod.snd_add, add_zero, Prod.mk_add_mk]
  rw [G.negative_pulledHeight η z m j hi (q + (0, Real.pi)),
    G.negative_pulledHeight η z m j hi q, hf.2.2.2.2.2, hf.2.2.2.2.1, hshift]
  exact G.W.negativePulledHeight_period j.1 j.2 hz
    (G.W.negativeCanonicalUnit_mapsTo G.X.e₀ k j.1 j.2 hk hq)

end N04RealizationGauge
end ContinuousFlexibility.Analysis

/-- info: 'ContinuousFlexibility.Analysis.N04RealizationStart.negativeInverseJointTower' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ContinuousFlexibility.Analysis.N04RealizationStart.negativeInverseJointTower

/-- info: 'ContinuousFlexibility.Analysis.N04RealizationGauge.negativeInverseAtomMixedRegularity' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ContinuousFlexibility.Analysis.N04RealizationGauge.negativeInverseAtomMixedRegularity

/-- info: 'ContinuousFlexibility.Analysis.N04RealizationGauge.negativePulledHeightMixedRegularity' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ContinuousFlexibility.Analysis.N04RealizationGauge.negativePulledHeightMixedRegularity
