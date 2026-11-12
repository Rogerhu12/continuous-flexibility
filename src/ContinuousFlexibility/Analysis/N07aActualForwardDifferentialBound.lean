import ContinuousFlexibility.Analysis.N07aInverseChartDifferentialDifference
import ContinuousFlexibility.Analysis.N07aForwardChartBounds

/-!
# Uniform first forward derivatives on moving physical pieces

The relative inverse differential is uniformly smaller than one half on
one stronger low neighborhood. The elementary Neumann norm estimate then
bounds the genuine current forward differential by twice its reference
bound. All sampled subpower factors are absorbed together before shrinking.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set ContinuousFlexibility.Statements
open scoped ContDiff

set_option backward.isDefEq.respectTransparency true

private theorem n07a_absorb_half (v g a : ℝ) (hv : 0 ≤ v)
    (ha : a ≤ 1 / 2) (hb : v ≤ g + v * a) : v ≤ 2 * g := by
  have hsmall := mul_le_mul_of_nonneg_left ha hv
  nlinarith only [hb, hsmall]

private theorem n07a_inverse_perturbation_norm_le
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (P₀ P G₀ V : E →L[ℝ] E)
    (h₀ : ∀ v, P₀ (G₀ v) = v) (hV : ∀ v, V (P v) = v)
    (hrel : ‖(P - P₀).comp G₀‖ < 1 / 2) : ‖V‖ ≤ 2 * ‖G₀‖ := by
  have heq : V = G₀ - V.comp ((P - P₀).comp G₀) := by
    apply ContinuousLinearMap.ext
    intro v
    simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.comp_apply, map_sub,
      h₀, hV]
    abel
  have hbound : ‖V‖ ≤ ‖G₀‖ + ‖V‖ * ‖(P - P₀).comp G₀‖ := by
    calc
      ‖V‖ = ‖G₀ - V.comp ((P - P₀).comp G₀)‖ := congrArg norm heq
      _ ≤ ‖G₀‖ + ‖V.comp ((P - P₀).comp G₀)‖ :=
        norm_sub_le G₀ (V.comp ((P - P₀).comp G₀))
      _ ≤ ‖G₀‖ + ‖V‖ * ‖(P - P₀).comp G₀‖ :=
        add_le_add le_rfl (ContinuousLinearMap.opNorm_comp_le V ((P - P₀).comp G₀))
  exact n07a_absorb_half ‖V‖ ‖G₀‖ ‖(P - P₀).comp G₀‖ (norm_nonneg V) hrel.le hbound

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

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {L : ReturnCorrectionData S} {K : CanonicalData S}
  {base : ℕ} {ε : ℝ}

def N07aActualForwardFirstBound (T : MaterialData) (S : PhysicalSpacesData)
    (C : NonlinearGeometryData S) (K : CanonicalData S) (base : ℕ) (ε : ℝ) : Prop :=
  ∃ b : ℕ → ℝ, N07aSampleSubpower T K b ∧ (∀ m, 0 ≤ b m) ∧
    ∀ z ∈ sectorNeighborhood S base ε ε, ∀ m x,
      x ∈ physicalPieceOpen S K (liftSectorParameter S C z) m →
        ‖fderiv ℝ (K.chart (liftSectorParameter S C z) m) x‖ ≤ b m

theorem N07aActualForwardFirstBound.restrict
    (h : N07aActualForwardFirstBound T S C K base ε)
    {base' : ℕ} {ε' : ℝ} (hb : base ≤ base') (he : ε' ≤ ε) :
    N07aActualForwardFirstBound T S C K base' ε' := by
  obtain ⟨b, hbs, hb0, hbb⟩ := h
  exact ⟨b, hbs, hb0, fun z hz => hbb z (n07a_sectorNeighborhood_mono hb he hz)⟩

private theorem n07a_reference_forward_fderiv_bound
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T) (hε : 0 < ε)
    (hgeom : CanonicalGeometry D S C K base ε)
    (href : CanonicalGeometry.ReferenceJets D T S C L K)
    (hcur : CanonicalGeometry.CurrentJets D T S C L K base ε) :
    ∃ b : ℕ → ℝ, N07aSampleSubpower T K b ∧ (∀ m, 0 ≤ b m) ∧
      ∀ m x, x ∈ referencePhysicalPieceOpen S K m →
        ‖fderiv ℝ (K.chart (C.referenceState, 0) m) x‖ ≤ b m := by
  let bounds := n07a_forwardChart_positive_jets hD hT href hcur
    (fun m => (hgeom.referenceBounds m).2.1) (fun m => (hgeom.referenceBounds m).1)
  let d : ℕ := bounds.choose
  have hb := bounds.choose_spec
  let b : ℕ → ℝ := (hb 1 (by omega)).choose
  have hbs := (hb 1 (by omega)).choose_spec.1
  have hb0 := (hb 1 (by omega)).choose_spec.2.1
  have hbb := (hb 1 (by omega)).choose_spec.2.2
  have hzero : (0 : CanonicalGeometry.Parameter S) ∈ sectorNeighborhood S base ε ε := by
    have h0 : sectorGrading S base (0 : StateDirections S) = 0 :=
      (sectorGrading S base).map_zero'
    exact ⟨by simpa only [Prod.fst_zero] using h0.trans_lt hε,
      by simpa only [Prod.snd_zero, abs_zero] using hε⟩
  have hlift : liftSectorParameter S C (0 : CanonicalGeometry.Parameter S) =
      (C.referenceState, 0) := by
    simp only [liftSectorParameter, Prod.fst_zero, Prod.snd_zero,
      ZeroMemClass.coe_zero, add_zero]
  refine ⟨b, hbs, hb0, fun m x hx => ?_⟩
  have h := hbb 0 hzero m x hx
  rw [norm_iteratedFDeriv_one] at h
  have hpzero : CanonicalGeometry.parameterGrading S (1 - 1 + d)
      (0 : CanonicalGeometry.Parameter S) = 0 :=
    (CanonicalGeometry.parameterGrading S (1 - 1 + d)).map_zero'
  have heq := congrArg (fun q : AnnularState S × ℝ =>
    ‖fderiv ℝ (K.chart q m) x‖) hlift
  have hfactor : b m * (1 + CanonicalGeometry.parameterGrading S (1 - 1 + d)
      (0 : CanonicalGeometry.Parameter S)) = b m :=
    (congrArg (fun a : ℝ => b m * (1 + a)) hpzero).trans (by rw [add_zero, mul_one])
  exact (heq.symm.le.trans h).trans_eq hfactor

theorem n07a_actualForwardFirstBound_neighborhood
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T) (hε : 0 < ε)
    (hrefState : referenceStateConditions D S C)
    (hgeom : CanonicalGeometry D S C K base ε)
    (href : CanonicalGeometry.ReferenceJets D T S C L K)
    (hcur : CanonicalGeometry.CurrentJets D T S C L K base ε) :
    ∃ base' : ℕ, base ≤ base' ∧ ∃ η : ℝ, 0 < η ∧ η ≤ ε ∧
      N07aActualForwardFirstBound T S C K base' η := by
  obtain ⟨low, e, he, he0, heb⟩ := n07a_inverseChart_fderiv_difference_bound
    hD hT hε hrefState hgeom href hcur
  obtain ⟨b, hb, hb0, hbb⟩ := n07a_reference_forward_fderiv_bound hD hT hε hgeom href hcur
  obtain ⟨A, hA, hAb⟩ := (N07aSampleSubpower.mul hD hT he hb).height_absorption
    hD hT (by norm_num : 0 < (3 / 4 : ℝ))
  let η : ℝ := min ε (1 / (4 * A))
  have hη : 0 < η := lt_min hε (div_pos zero_lt_one (mul_pos (by norm_num) hA))
  have hηε : η ≤ ε := min_le_left _ _
  have hηA : η ≤ 1 / (4 * A) := min_le_right _ _
  refine ⟨max base low, le_max_left _ _, η, hη, hηε, (fun m => 2 * b m),
    N07aSampleSubpower.mul hD hT (N07aSampleSubpower.const hD hT 2) hb,
    (fun m => mul_nonneg (by norm_num) (hb0 m)), ?_⟩
  intro z hz m x hx
  have hzold : z ∈ sectorNeighborhood S base ε ε :=
    n07a_sectorNeighborhood_mono (le_max_left _ _) hηε hz
  have hzstate := liftSectorParameter_mem_stateNeighborhood (S := S) (C := C) hzold le_rfl
  have hs := hrefState.liftSectorParameter_sector z
  have hc := hgeom.charts (liftSectorParameter S C z) hzstate hs m
  let y := K.chart (liftSectorParameter S C z) m x
  have hy : y ∈ canonicalOpen S K m := hc.1 hx
  have hxy : K.inverseChart (liftSectorParameter S C z) m y = x := hc.2.2.1 x hx
  have hzref : (C.referenceState, 0) ∈ stateNeighborhood S C base ε := by
    constructor
    · change stateGrading S base (C.referenceState - C.referenceState) < ε
      have hzero : stateGrading S base (0 : AnnularState S) = 0 :=
        (stateGrading S base).map_zero'
      simpa only [sub_self, hzero] using hε
    · simpa only [abs_zero] using hε
  let x₀ := K.inverseChart (C.referenceState, 0) m y
  have hx₀ : x₀ ∈ referencePhysicalPieceOpen S K m := by
    rw [← hgeom.referenceDomain m]
    exact (hgeom.charts (C.referenceState, 0) hzref hrefState.stateSector m).2.1 hy
  let P₀ := fderiv ℝ (K.inverseChart (C.referenceState, 0) m) y
  let P := fderiv ℝ (K.inverseChart (liftSectorParameter S C z) m) y
  let G₀ := fderiv ℝ (K.chart (C.referenceState, 0) m) x₀
  let V := fderiv ℝ (K.chart (liftSectorParameter S C z) m) x
  have hG₀ : ‖G₀‖ ≤ b m := hbb m x₀ hx₀
  have hP₀ : ∀ v, P₀ (G₀ v) = v := by
    intro v
    exact congrArg (fun Q : PolarPoint →L[ℝ] PolarPoint => Q v)
      (n07a_actualChart_fderiv_inverse hgeom hzref hrefState.stateSector m hy).2
  have hVP : ∀ v, V (P v) = v := by
    intro v
    have h := congrArg (fun Q : PolarPoint →L[ℝ] PolarPoint => Q v)
      (n07a_actualChart_fderiv_inverse hgeom hzstate hs m hy).1
    simpa only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply, hxy] using h
  have hp : 0 ≤ CanonicalGeometry.parameterGrading S low z := apply_nonneg _ _
  have hsample := hT.2.1 _
    (materialSample_mem_radialCore hT hD.choose_spec.2.1 (K.cell m))
  have hH : 0 ≤ T.H (T.sample (K.cell m)) ^ (3 / 4 : ℝ) :=
    Real.rpow_nonneg hsample.2.1.le _
  have hsmall : A * CanonicalGeometry.parameterGrading S low z < 1 / 2 := by
    calc
      _ < A * (2 * η) := mul_lt_mul_of_pos_left
        (n07a_parameterGrading_lt_twice_radius (le_max_right _ _) hz) hA
      _ ≤ A * (2 * (1 / (4 * A))) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hηA (by norm_num)) hA.le
      _ = 1 / 2 := by field_simp [hA.ne'] <;> ring
  have hrel : ‖(P - P₀).comp G₀‖ < 1 / 2 := by
    calc
      _ ≤ ‖P - P₀‖ * ‖G₀‖ := ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ (e m * T.H (T.sample (K.cell m)) ^ (3 / 4 : ℝ) *
          CanonicalGeometry.parameterGrading S low z) * b m :=
        mul_le_mul (heb z hzold m y hy) hG₀ (norm_nonneg _)
          (mul_nonneg (mul_nonneg (he0 m) hH) hp)
      _ = (T.H (T.sample (K.cell m)) ^ (3 / 4 : ℝ) * |e m * b m|) *
          CanonicalGeometry.parameterGrading S low z := by
        rw [abs_of_nonneg (mul_nonneg (he0 m) (hb0 m))]
        ring
      _ ≤ A * CanonicalGeometry.parameterGrading S low z :=
        mul_le_mul_of_nonneg_right (hAb m) hp
      _ < 1 / 2 := hsmall
  exact (n07a_inverse_perturbation_norm_le P₀ P G₀ V hP₀ hVP hrel).trans
    (mul_le_mul_of_nonneg_left hG₀ (by norm_num))

end ContinuousFlexibility.Analysis
