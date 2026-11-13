import ContinuousFlexibility.Analysis.N04NegativeGeometryChartTowers

/-!
# The two genuine monotonicities of the actual travel chart

The positive angular derivatives of the characteristic first integrals
give angular monotonicity. At fixed target angle, the radial derivative
is the positive travel Jacobian divided by the positive angular derivative.
Both assertions concern the literal corrected characteristic chart.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis.N04RealizationStart

open Set ContinuousFlexibility.Statements
open scoped ContDiff

variable (W : N04RealizationStart)

theorem negativeTravelAngularPositive (m : ℕ) {z : StateDirections W.S × ℝ}
    (hz : z ∈ sectorNeighborhood W.S W.base W.ε W.ε)
    {p : PolarPoint} (hp : p ∈ Ioo (W.C.left m) (W.C.right m) ×ˢ (univ : Set ℝ)) :
    0 < angularPartial
      (fun q => (n04bActualTravelChart W.S W.C W.L
        (liftSectorParameter W.S W.C z) m q).2) p := by
  let w := liftSectorParameter W.S W.C z
  let Φ : PolarPoint → ℝ := fun p => W.L.minusFlow w m p.1 p.2
  let hL : ℝ → ℝ := stateLeftChart W.S w.1 m
  have hw := liftSectorParameter_mem_stateNeighborhood (C := W.C) hz le_rfl
  have hs := W.through03.1.1.2.2.1.liftSectorParameter_sector z
  have hΦ : N04bCircleFlowRegularity Φ (W.C.left m) (W.C.right m) Real.pi :=
    n04b_actualMinusFlow_regular W.through03 W.hS W.hT W.field hw hs m
  have hhL : ContDiff ℝ ∞ hL := stateLeftChart_contDiff W.S w m (W.hS.2.1 (3 / 4 : ℝ))
  have hLpos : ∀ θ, 0 < deriv hL θ := fun θ =>
    lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1 / 2)
      (W.through03.1.1.2.2.2.2.2.2.2.1 w hw hs m θ).1
  have hU := n04b_plusFirstIntegral_smooth hΦ Real.pi_ne_zero hhL
  have hV := n04b_minusFirstIntegral_smooth hΦ Real.pi_ne_zero hhL
  have hUd := (hU.contDiffAt ((isOpen_Ioo.prod isOpen_univ).mem_nhds hp)).differentiableAt
    (by simp)
  have hVd := (hV.contDiffAt ((isOpen_Ioo.prod isOpen_univ).mem_nhds hp)).differentiableAt
    (by simp)
  have hd : HasFDerivAt
      (fun q => (n04bCharacteristicTravelChart Φ hL q).2)
      ((1 / 2 : ℝ) • (fderiv ℝ (n04bPlusFirstIntegral Φ hL) p +
        fderiv ℝ (n04bMinusFirstIntegral Φ hL) p)) p :=
    (hUd.hasFDerivAt.fun_add hVd.hasFDerivAt).const_mul (1 / 2 : ℝ)
  change 0 < angularPartial (fun q => (n04bCharacteristicTravelChart Φ hL q).2) p
  unfold angularPartial
  rw [hd.fderiv]
  simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.add_apply, smul_eq_mul]
  exact mul_pos (by norm_num) (add_pos
    (n04b_plusFirstIntegral_angularPartial_pos hΦ Real.pi_ne_zero hhL hLpos hp)
    (n04b_minusFirstIntegral_angularPartial_pos hΦ Real.pi_ne_zero hhL hLpos hp))

/-- Angular monotonicity and surjectivity on every closed physical
slice, together with fixed-angle radial monotonicity. -/
theorem negativeTravelMonotonicity (m : ℕ) {z : StateDirections W.S × ℝ}
    (hz : z ∈ sectorNeighborhood W.S W.base W.ε W.ε) :
    let F := n04bActualTravelChart W.S W.C W.L (liftSectorParameter W.S W.C z) m
    (∀ r ∈ Icc (W.C.left m) (W.C.right m), StrictMono (fun θ => (F (r, θ)).2)) ∧
      (∀ r ∈ Icc (W.C.left m) (W.C.right m),
        Function.Surjective (fun θ => (F (r, θ)).2)) ∧
      ∀ θ, StrictMonoOn (fun r => angleNormalizedTravel F (r, θ))
        (Icc (W.C.left m) (W.C.right m)) := by
  let w := liftSectorParameter W.S W.C z
  let F := n04bActualTravelChart W.S W.C W.L w m
  have hw := liftSectorParameter_mem_stateNeighborhood (C := W.C) hz le_rfl
  have hs := W.through03.1.1.2.2.1.liftSectorParameter_sector z
  have hc := n04b_actualTravelChart_continuous W.through03 W.hS W.hT W.field hw hs m
  have hd := n04b_actualTravelChart_smooth W.through03 W.hS W.hT W.field hw hs m
  have hpos : ∀ p ∈ Ioo (W.C.left m) (W.C.right m) ×ˢ (univ : Set ℝ),
      0 < angularPartial (fun q => (F q).2) p :=
    fun p hp => W.negativeTravelAngularPositive m hz hp
  have hleft : StrictMono (fun θ => (F (W.C.left m, θ)).2) := by
    have he : (fun θ => (F (W.C.left m, θ)).2) = stateLeftChart W.S w.1 m := by
      funext θ
      exact congrArg Prod.snd
        (n04b_actualTravelChart_endpoints W.through03 W.hS W.hT W.field hw hs m θ).1
    rw [he]
    exact strictMono_of_deriv_pos (fun θ =>
      lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1 / 2)
        (W.through03.1.1.2.2.2.2.2.2.2.1 w hw hs m θ).1)
  have hright : StrictMono (fun θ => (F (W.C.right m, θ)).2) := by
    have he : (fun θ => (F (W.C.right m, θ)).2) = rightChartCandidate W.S W.C w m := by
      funext θ
      exact congrArg Prod.snd
        (n04b_actualTravelChart_endpoints W.through03 W.hS W.hT W.field hw hs m θ).2
    rw [he]
    exact strictMono_of_deriv_pos
      (N01Properties.rightChart_deriv_pos W.S W.C w m W.through03.1.1 hw hs)
  have hm (r : ℝ) (hr : r ∈ Icc (W.C.left m) (W.C.right m)) :
      StrictMono (fun θ => (F (r, θ)).2) :=
    strictMono_travelStrip_angle hd hpos hleft hright hr
  have hsurj (r : ℝ) (hr : r ∈ Icc (W.C.left m) (W.C.right m)) :
      Function.Surjective (fun θ => (F (r, θ)).2) := by
    apply surjective_of_continuous_periodic_lift Real.pi_ne_zero
      (hc.snd.comp_continuous (continuous_const.prodMk continuous_id)
        (fun θ => ⟨hr, mem_univ θ⟩))
    intro θ
    exact congrArg Prod.snd
      (n04b_actualTravelChart_period_add W.through03 W.hS W.hT W.field hw hs m hr θ)
  exact ⟨hm, hsurj, fun θ => strictMonoOn_angleNormalizedTravel hc hd hpos
    (fun p hp => n04b_actualTravelChart_jacobian_pos
      W.through03 W.hS W.hT W.field hw hs m hp) hm hsurj θ⟩

end ContinuousFlexibility.Analysis.N04RealizationStart
