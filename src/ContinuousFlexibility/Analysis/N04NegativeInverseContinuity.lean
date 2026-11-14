module

public import ContinuousFlexibility.Analysis.N04NegativeGeometryChartTowers
public import ContinuousFlexibility.Analysis.N04NegativeGeometryTravelInverseContinuity

/-!
# Continuity and identities for the actual negative inverse

The actual travel inverse is jointly continuous in the original parameter
topology. The fixed root change gives continuity of the stored negative
inverse, while the whole physical component provides its inverse identities
and angular periods. These facts precede the inverse directional tower.
-/

@[expose] public section

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
  · have hcont := n04b_actualTravelChart_continuous W.through03 W.hS W.hT W.field hw hs m
    exact hcont.snd.comp_continuous (f := fun θ : ℝ => (r, θ))
      (continuous_const.prodMk continuous_id) (fun θ => ⟨hr, mem_univ θ⟩)
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
  let Φ : ((StateDirections W.S × ℝ) × PolarPoint) →
      (StateDirections W.S × ℝ) × PolarPoint := fun x =>
    (x.1, n04bRootStripInverse (W.C.travel m) side x.2)
  have hΦ : Continuous Φ := continuous_fst.prodMk
    ((n04b_continuous_rootStripInverse (W.C.travel m) side).comp continuous_snd)
  have hmap : MapsTo Φ
      (sectorNeighborhood W.S W.base W.ε W.ε ×ˢ
        (Ioo (0 : ℝ) (n04bRootCutRadius (W.C.travel m)) ×ˢ univ))
      (sectorNeighborhood W.S W.base W.ε W.ε ×ˢ
        (Ioo (0 : ℝ) (W.C.travel m) ×ˢ univ)) :=
    fun x hx => ⟨hx.1, W.negativeRootStripInverse_mapsTo m side hx.2⟩
  have hc := (W.negativeTravelInverse_continuousOn m).comp hΦ.continuousOn hmap
  exact hc.congr (fun x hx =>
    (n04bActualNegativeFunctions_spec W.hT W.hS W.through03 W.field
      (liftSectorParameter_mem_stateNeighborhood hx.1 le_rfl)
      (W.through03.1.1.2.2.1.liftSectorParameter_sector x.1) m side).open_inverse_eq hx.2)

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
  have H := n04bActualNegativeFunctions_spec W.hT W.hS W.through03 W.field hw hs m side
  exact (H.open_chart_data W.through03 W.hS W.hT W.field hw hs).2.2.2 q hq

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
  have H := n04bActualNegativeFunctions_spec W.hT W.hS W.through03 W.field hw hs m side
  exact (H.period W.through03 W.hS W.hT W.field hw hs
    (W.negativeInverse_maps_component m side hz hq)).2

end ContinuousFlexibility.Analysis.N04RealizationStart
