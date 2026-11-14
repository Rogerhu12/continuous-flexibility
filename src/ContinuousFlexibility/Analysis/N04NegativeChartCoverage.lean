import ContinuousFlexibility.Analysis.N04NegativeChartRootCoordinateBounds
import ContinuousFlexibility.Analysis.N04NegativeChartInteriorPhysicalPositive

/-!
# Root and interior coverage of each actual reference half

The physical overlap radius is the product of the selected root scale and
its positive band. Its material reciprocal bound supplies the interior
estimate. Both regions use the same actual chart tower and the same half
sample; the common parameter sector is chosen before all derivative orders.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set ContinuousFlexibility.Statements CanonicalGeometry
open scoped ContDiff

set_option backward.isDefEq.respectTransparency true

private theorem coverage_half_coordinates (l h c x : ℝ) (side : Bool)
    (hx : x ∈ Ioo (if side then c else l) (if side then h else c)) :
    ∃ r : ℝ, r ∈ Ioo (0 : ℝ)
        ((if side then h else c) - (if side then c else l)) ∧
      inwardComponentPoint l h side r = x := by
  cases side with
  | false =>
      refine ⟨x - l, ⟨sub_pos.mpr hx.1, sub_lt_sub_right hx.2 l⟩, ?_⟩
      change l + (x - l) = x
      ring
  | true =>
      refine ⟨h - x, ⟨sub_pos.mpr hx.2, sub_lt_sub_left hx.1 h⟩, ?_⟩
      change h - (h - x) = x
      ring

private theorem coverage_material_weight_mono {x C B E H V V' : ℝ}
    (hE : 1 ≤ E) (hB : 0 ≤ B) (hH : 0 ≤ H) (hV : 0 ≤ V)
    (hCB : C ≤ B) (hVV' : V ≤ V')
    (hx : |x| ≤ C * E ^ C * H * V) :
    |x| ≤ B * E ^ B * H * V' := by
  have hc : C * E ^ C * H ≤ B * E ^ B * H :=
    mul_le_mul_of_nonneg_right
      (mul_le_mul hCB (Real.rpow_le_rpow_of_exponent_le hE hCB)
        (Real.rpow_nonneg (zero_le_one.trans hE) C) hB) hH
  exact hx.trans (mul_le_mul hc hVV' hV
    (mul_nonneg (mul_nonneg hB (Real.rpow_nonneg (zero_le_one.trans hE) B)) hH))

attribute [local instance]
  n07aNonlinearAnnularGroup n07aNonlinearAnnularModule
  n07aNonlinearAnnularAddGroup n07aNonlinearAnnularSMul n07aNonlinearAnnularSub
  n07aNonlinearAnnularParameterGroup n07aNonlinearAnnularParameterModule
  n07aNonlinearAnnularParameterAddGroup n07aNonlinearAnnularParameterSMul
  n07aNonlinearAnnularParameterSub
  n07aNonlinearDirectionsGroup n07aNonlinearDirectionsModule
  n07aNonlinearDirectionsAddGroup n07aNonlinearDirectionsSMul n07aNonlinearDirectionsSub
  n07aNonlinearSectorParameterGroup n07aNonlinearSectorParameterModule
  n07aNonlinearSectorParameterAddGroup n07aNonlinearSectorParameterSMul
  n07aNonlinearSectorParameterSub

namespace N04RealizationStart

attribute [local instance]
  interiorRaw_parameterTopology interiorRaw_parameterAddGroup interiorRaw_parameterSMul

private theorem negativeReferenceHalf_inward (W : N04RealizationStart)
    (e : ℕ ≃ N04PieceIndex W.D) (m : ℕ) (side : Bool) {p : PolarPoint}
    (hp : p ∈ referencePhysicalPieceOpen W.S (W.A e) (e.symm (.inl (m, side)))) :
    ∃ r : ℝ, r ∈ Ioo (0 : ℝ) (W.negativeOpticalWidth m side) ∧
      W.negativeInwardPoint m side (r, p.2) = p := by
  let cut : ℕ → ℝ := n04bActualReferenceCut W.through03
  have hp₀ : p ∈
      Ioo (n04bReferenceTypedLeft W.C cut (e (e.symm (.inl (m, side)))))
        (n04bReferenceTypedRight W.C cut (e (e.symm (.inl (m, side))))) ×ˢ univ := hp
  rw [e.apply_symm_apply] at hp₀
  have hx : p.1 ∈ Ioo (if side then cut m else W.C.left m)
      (if side then W.C.right m else cut m) := hp₀.1
  have hr := coverage_half_coordinates (W.C.left m) (W.C.right m) (cut m) p.1 side hx
  refine ⟨hr.choose, hr.choose_spec.1, ?_⟩
  apply Prod.ext
  · exact hr.choose_spec.2
  · rfl

variable {W : N04RealizationStart} {e : ℕ ≃ N04PieceIndex W.D}
  {base : ℕ} {ε C : ℝ} {σ : ℕ → Bool → ℝ}

private theorem RootCoordinatePrefixData.physical_radius_bounds
    (A : RootCoordinatePrefixData W e base ε C σ) :
    ∀ m side, 0 < W.negativeChartRootScale e C m side * σ m side ∧
      W.negativeChartRootScale e C m side * σ m side ≤ W.negativeMaterialCollar m := by
  intro m side
  have hd := W.negativeChartRootScale_bounds e A.scale m side
  have hs := A.band m side
  refine ⟨mul_pos hd.1 hs.1, ?_⟩
  have hdc : W.negativeChartRootScale e C m side ≤ W.negativeMaterialCollar m := by
    linarith only [hd.1, hd.2.2.1]
  exact ((mul_le_mul_of_nonneg_left hs.2 hd.1.le).trans_eq (mul_one _)).trans hdc

/-- The actual root and interior estimates cover the complete reference
half. Their low order and parameter radius are combined before all jet
orders, and the spatial loss retains coefficient one. -/
theorem RootCoordinatePrefixData.physical_coverage
    (A : RootCoordinatePrefixData W e base ε C σ)
    (hρb : ∃ M P : ℝ, 0 < M ∧ 0 ≤ P ∧ ∀ m side,
      (W.negativeChartRootScale e C m side * σ m side)⁻¹ ≤
        M * W.T.E0 (W.negativeHalfSample e m side) ^ P) :
    ∃ b : ℕ, ∃ η : ℝ, W.base ≤ b ∧ 0 < η ∧
      η ≤ min W.ε (1 / 2 : ℝ) ∧
      N04NegativeChartPhysicalPositiveBounds W e b η := by
  let ρ : ℕ → Bool → ℝ := fun m side => W.negativeChartRootScale e C m side * σ m side
  have hρ : ∀ m side, 0 < ρ m side ∧ ρ m side ≤ W.negativeMaterialCollar m :=
    A.physical_radius_bounds
  have hI := W.negativeInterior_physical_positive_bounds e ρ hρ hρb
  let bI := hI.choose
  let εI := hI.choose_spec.choose
  have hIs := hI.choose_spec.choose_spec
  let b := max base bI
  let η := min ε εI
  have hbW : W.base ≤ b := A.base_le.trans (le_max_left base bI)
  have hηW : η ≤ W.ε := (min_le_left ε εI).trans A.ε_le
  have hηhalf : η ≤ 1 / 2 := (min_le_left ε εI).trans A.ε_small
  have hεIW : εI ≤ W.ε := hIs.2.2.1.trans (min_le_left W.ε (1 / 2 : ℝ))
  have hsubR := sectorNeighborhood_mono W.S (le_max_left base bI)
    (min_le_left ε εI) (min_le_left ε εI)
  have hsubI := sectorNeighborhood_mono W.S (le_max_right base bI)
    (min_le_right ε εI) (min_le_right ε εI)
  have hsubRW := sectorNeighborhood_mono W.S A.base_le A.ε_le A.ε_le
  have hsubIW := sectorNeighborhood_mono W.S hIs.1 hεIW hεIW
  have hsubW := sectorNeighborhood_mono W.S hbW hηW hηW
  refine ⟨b, η, hbW, lt_min A.ε_pos hIs.2.1, le_min hηW hηhalf, fun n hn => ?_⟩
  have hRn := A.physical_positive_bounds n hn
  have hIn := hIs.2.2.2 n hn
  let LR := hRn.choose
  let LI := hIn.choose
  let loss := max LR LI
  refine ⟨loss, fun s => ?_⟩
  have hRs := hRn.choose_spec s
  have hIns := hIn.choose_spec s
  let BR := hRs.choose
  let BI := hIns.choose
  let B := max BR BI
  have hB : 0 < B := hRs.choose_spec.1.trans_le (le_max_left BR BI)
  have hRbound := hRs.choose_spec.2
  have hIbound := hIns.choose_spec.2
  refine ⟨B, hB, fun m side radial p hp a c hac J z hz v => ?_⟩
  let E := W.T.E0 (W.negativeHalfSample e m side)
  let H := W.T.H (W.negativeHalfSample e m side) ^ (3 / 4 : ℝ)
  let V := oneHighVariationWeight (parameterGrading W.S) b (s + loss) z v
  change |J.D n z v| ≤ B * E ^ B * H * V
  have hE : 1 ≤ E := W.floor _
  have hH : 0 ≤ H := Real.rpow_nonneg (W.hT.2.1 _
    (materialSample_mem_interval W.radial.1 W.hT _)).2.1.le _
  have hp' := n04NegativeGeometry_referenceHalf_subset_component
    W.hT W.hS W.through03 W.field e (e.symm (.inl (m, side))) m side
    (e.apply_symm_apply _) hp
  let f : Parameter W.S → PolarPoint → ℝ := fun x q => if radial then
    (n04bActualNegativeChart W.hT W.hS W.through03 W.field
      (liftSectorParameter W.S W.C x) m side q).1 else
    (n04bActualNegativeChart W.hT W.hS W.through03 W.field
      (liftSectorParameter W.S W.C x) m side q).2
  let R := negativePhysicalProjectionRegularity W m side radial
  let J₀ : SmoothDirections (sectorNeighborhood W.S W.base W.ε W.ε)
      (fun x => mixedDerivative a c (f x) p) := R.parameter a c p hp'
  have he : J.D n z v = J₀.D n z v := by
    have hj := congrArg (fun L : Parameter W.S [×n]→L[ℝ] ℝ => L v)
      (J.unique (J₀.restrict (isOpen_sectorNeighborhood W.S b η η) hsubW) n z hz)
    simpa only [SmoothDirections.restrict_D] using hj
  have hexr := negativeReferenceHalf_inward W e m side hp
  let r := hexr.choose
  have hr : r ∈ Ioo (0 : ℝ) (W.negativeOpticalWidth m side) := hexr.choose_spec.1
  have hpoint : W.negativeInwardPoint m side (r, p.2) = p := hexr.choose_spec.2
  have hbound : |J₀.D n z v| ≤ B * E ^ B * H * V := by
    by_cases hsmall : r < ρ m side
    · let δ := W.negativeChartRootScale e C m side
      have hδ : 0 < δ := (W.negativeChartRootScale_bounds e A.scale m side).1
      let q : PolarPoint := (r / δ, p.2)
      have hlt : r < σ m side * δ := by
        calc
          r < δ * σ m side := hsmall
          _ = σ m side * δ := mul_comm _ _
      have hq : q.1 ∈ Ioo (0 : ℝ) (σ m side) :=
        ⟨div_pos hr.1 hδ, (div_lt_iff₀ hδ).mpr hlt⟩
      have hδq : δ * q.1 = r := by
        change δ * (r / δ) = r
        rw [mul_comm, div_mul_cancel₀ _ hδ.ne']
      have hqp : W.negativeInwardPoint m side (δ * q.1, q.2) = p :=
        (congrArg (fun t : ℝ => W.negativeInwardPoint m side (t, p.2)) hδq).trans hpoint
      let JR := J₀.restrict (isOpen_sectorNeighborhood W.S base ε ε) hsubRW
      let JRq : SmoothDirections (sectorNeighborhood W.S base ε ε)
          (fun x => mixedDerivative a c (f x)
            (W.negativeInwardPoint m side (δ * q.1, q.2))) :=
        JR.congrOn (fun x _ => congrArg (mixedDerivative a c (f x)) hqp.symm)
      have hroot : |J₀.D n z v| ≤ BR * E ^ BR * H *
          oneHighVariationWeight (parameterGrading W.S) base (s + LR) z v :=
        hRbound m side radial q hq a c hac JRq z (hsubR hz) v
      have hweight := oneHighVariationWeight_mono (n07aParameterGrading_monotone W.S)
        (le_max_left base bI) (Nat.add_le_add_left (le_max_left LR LI) s) z v
      exact coverage_material_weight_mono hE hB.le hH
        (oneHighVariationWeight_nonneg _ _ _ _ _) (le_max_left BR BI) hweight hroot
    · have hri : ρ m side / 2 ≤ r := by
        have hlarge := le_of_not_gt hsmall
        have hρpos := (hρ m side).1
        linarith only [hlarge, hρpos]
      have hpi : p ∈ W.negativeInteriorPhysicalDomain ρ (m, side) :=
        ⟨(r, p.2), ⟨⟨hri, hr.2.le⟩, mem_univ _⟩, hpoint⟩
      let JI := J₀.restrict (isOpen_sectorNeighborhood W.S bI εI εI) hsubIW
      have hinterior : |J₀.D n z v| ≤ BI * E ^ BI * H *
          oneHighVariationWeight (parameterGrading W.S) bI (s + LI) z v :=
        hIbound m side radial p hpi a c hac JI z (hsubI hz) v
      have hweight := oneHighVariationWeight_mono (n07aParameterGrading_monotone W.S)
        (le_max_right base bI) (Nat.add_le_add_left (le_max_right LR LI) s) z v
      exact coverage_material_weight_mono hE hB.le hH
        (oneHighVariationWeight_nonneg _ _ _ _ _) (le_max_right BR BI) hweight hinterior
  exact (congrArg abs he).trans_le hbound

end N04RealizationStart
end ContinuousFlexibility.Analysis

/-- info: 'ContinuousFlexibility.Analysis.N04RealizationStart.RootCoordinatePrefixData.physical_coverage'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ContinuousFlexibility.Analysis.N04RealizationStart.RootCoordinatePrefixData.physical_coverage
