import ContinuousFlexibility.Analysis.N07aMaterialLocalWindow
import ContinuousFlexibility.Analysis.N07aMaterialPieceBounds
import ContinuousFlexibility.Analysis.N07aInverseChartDisplacement

/-!
# Sampled material ratios on the actual current physical pieces

Reference ratios are combined with the actual inverse displacement.
The complete subpower coefficient is absorbed against the genuine
H^(3/4) difference gain before choosing one common state neighborhood.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set ContinuousFlexibility.Statements

set_option backward.isDefEq.respectTransparency true

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

/-- A derived geometric certificate, to be restricted together with the
original N04/N06 data. It contains no assertion about solutions. -/
def N07aActualMaterialRatios (T : MaterialData) (S : PhysicalSpacesData)
    (C : NonlinearGeometryData S) (K : CanonicalData S) (base : ℕ) (ε : ℝ) : Prop :=
  ∃ e : ℕ → ℝ, N07aSampleSubpower T K e ∧ (∀ m, 1 ≤ e m) ∧
    ∀ z ∈ sectorNeighborhood S base ε ε, ∀ m p,
      p ∈ physicalPieceOpen S K (liftSectorParameter S C z) m →
        T.H p.1 / T.H (T.sample (K.cell m)) ≤ e m ∧
        T.H (T.sample (K.cell m)) / T.H p.1 ≤ e m ∧
        T.M p.1 / T.M (T.sample (K.cell m)) ≤ e m ∧
        T.M (T.sample (K.cell m)) / T.M p.1 ≤ e m

theorem N07aActualMaterialRatios.restrict
    (h : N07aActualMaterialRatios T S C K base ε)
    {base' : ℕ} {ε' : ℝ} (hb : base ≤ base') (he : ε' ≤ ε) :
    N07aActualMaterialRatios T S C K base' ε' := by
  obtain ⟨e, hes, he1, heb⟩ := h
  exact ⟨e, hes, he1, fun z hz => heb z (n07a_sectorNeighborhood_mono hb he hz)⟩

private theorem n07a_reference_state_mem (hε : 0 < ε) :
    (C.referenceState, 0) ∈ stateNeighborhood S C base ε := by
  constructor
  · change stateGrading S base (C.referenceState - C.referenceState) < ε
    simpa only [sub_self, map_zero] using hε
  · simpa only [abs_zero] using hε

/-- All actual inverse points lie in one fixed relative material window
of their reference inverse points after a single neighborhood restriction. -/
theorem n07a_inverseChart_material_displacement
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T) (hε : 0 < ε)
    (hrefState : referenceStateConditions D S C)
    (hgeom : CanonicalGeometry D S C K base ε)
    (href : CanonicalGeometry.ReferenceJets D T S C L K)
    (hcur : CanonicalGeometry.CurrentJets D T S C L K base ε)
    {δ : ℝ} (hδ : 0 < δ) :
    ∃ base' : ℕ, base ≤ base' ∧ ∃ η : ℝ, 0 < η ∧ η ≤ ε ∧
      ∀ z ∈ sectorNeighborhood S base' η η, ∀ m y, y ∈ canonicalOpen S K m →
        |(K.inverseChart (liftSectorParameter S C z) m y).1 -
            (K.inverseChart (C.referenceState, 0) m y).1| ≤
          δ * T.ell (K.inverseChart (C.referenceState, 0) m y).1 := by
  obtain ⟨low, e, he, he0, heb⟩ := n07a_inverseChart_radial_displacement
    hD hT href hcur (fun m => (hgeom.referenceBounds m).2.1)
      (fun m => (hgeom.referenceBounds m).1)
  obtain ⟨a, ha, ha0, hab⟩ := n07a_reference_materialEllInverse_bound
    hD hT href (fun m => (hgeom.referenceBounds m).1)
  obtain ⟨A, hA, hAb⟩ := (N07aSampleSubpower.mul hD hT he ha).height_absorption
    hD hT (by norm_num : 0 < (3 / 4 : ℝ))
  let η : ℝ := min ε (δ / (2 * A))
  have hη : 0 < η := lt_min hε (div_pos hδ (mul_pos (by norm_num) hA))
  have hηε : η ≤ ε := min_le_left _ _
  have hηδ : η ≤ δ / (2 * A) := min_le_right _ _
  refine ⟨max base low, le_max_left _ _, η, hη, hηε, ?_⟩
  intro z hz m y hy
  have hzold : z ∈ sectorNeighborhood S base ε ε :=
    n07a_sectorNeighborhood_mono (le_max_left _ _) hηε hz
  have hp : 0 ≤ CanonicalGeometry.parameterGrading S low z := apply_nonneg _ _
  have hpsmall : A * CanonicalGeometry.parameterGrading S low z < δ := by
    calc
      _ < A * (2 * η) := mul_lt_mul_of_pos_left
        (n07a_parameterGrading_lt_twice_radius (le_max_right _ _) hz) hA
      _ ≤ A * (2 * (δ / (2 * A))) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hηδ (by norm_num)) hA.le
      _ = δ := by field_simp [hA.ne'] <;> ring
  let x₀ := K.inverseChart (C.referenceState, 0) m y
  have hx₀ : x₀ ∈ referencePhysicalPieceOpen S K m := by
    rw [← hgeom.referenceDomain m]
    exact (hgeom.charts (C.referenceState, 0) (n07a_reference_state_mem hε)
      hrefState.stateSector m).2.1 hy
  have hx₀D : x₀.1 ∈ radialCore D := (hgeom.referenceBounds m).2.2 hx₀.1
  have hℓ : 0 < T.ell x₀.1 := (hT.2.1 x₀.1 hx₀D).1
  have hsample := hT.2.1 _
    (materialSample_mem_radialCore hT hD.choose_spec.2.1 (K.cell m))
  have hHp : 0 ≤ T.H (T.sample (K.cell m)) ^ (3 / 4 : ℝ) :=
    (Real.rpow_pos_of_pos hsample.2.1 _).le
  have hrel : |(K.inverseChart (liftSectorParameter S C z) m y).1 - x₀.1| *
      (T.ell x₀.1)⁻¹ ≤ A * CanonicalGeometry.parameterGrading S low z := by
    calc
      _ ≤ (e m * T.H (T.sample (K.cell m)) ^ (3 / 4 : ℝ) *
          CanonicalGeometry.parameterGrading S low z) * a m :=
        mul_le_mul (heb z hzold m y hy) (hab m x₀ hx₀) (inv_pos.mpr hℓ).le
          (mul_nonneg (mul_nonneg (he0 m) hHp) hp)
      _ = (T.H (T.sample (K.cell m)) ^ (3 / 4 : ℝ) * |e m * a m|) *
          CanonicalGeometry.parameterGrading S low z := by
        rw [abs_of_nonneg (mul_nonneg (he0 m) (ha0 m))]
        ring
      _ ≤ A * CanonicalGeometry.parameterGrading S low z :=
        mul_le_mul_of_nonneg_right (hAb m) hp
  apply (div_le_iff₀ hℓ).mp
  rw [div_eq_mul_inv]
  exact hrel.trans hpsmall.le

private theorem n07a_positive_ratio_chain
    {x y z B E : ℝ} (hy : 0 < y) (hz : 0 < z) (hB : 0 ≤ B)
    (hxy : x / y ≤ B) (hyz : y / z ≤ E) : x / z ≤ B * E := by
  calc
    x / z = (x / y) * (y / z) := by field_simp [hy.ne', hz.ne']
    _ ≤ B * E := mul_le_mul hxy hyz (div_pos hy hz).le hB

/-- The moving-domain material ratio certificate follows from the original
current and reference jets on one common stronger neighborhood. -/
theorem n07a_actualMaterialRatios_neighborhood
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T) (hε : 0 < ε)
    (hrefState : referenceStateConditions D S C)
    (hgeom : CanonicalGeometry D S C K base ε)
    (href : CanonicalGeometry.ReferenceJets D T S C L K)
    (hcur : CanonicalGeometry.CurrentJets D T S C L K base ε) :
    ∃ base' : ℕ, base ≤ base' ∧ ∃ η : ℝ, 0 < η ∧ η ≤ ε ∧
      N07aActualMaterialRatios T S C K base' η := by
  obtain ⟨δ, hδ, hwindow⟩ := n07a_material_local_ratio_window hT
  obtain ⟨base', hb, η, hη, hηε, hdisp⟩ :=
    n07a_inverseChart_material_displacement hD hT hε hrefState hgeom href hcur hδ
  obtain ⟨e, he, he1, heb⟩ := n07a_material_piece_ratio_envelope hD hT href
    (fun m => (hgeom.referenceBounds m).1)
  have hexp : 0 < Real.exp 1 := Real.exp_pos _
  have hexp1 : 1 ≤ Real.exp 1 := by
    simpa only [Real.exp_zero] using Real.exp_le_exp.mpr (show (0 : ℝ) ≤ 1 by norm_num)
  refine ⟨base', hb, η, hη, hηε, (fun m => Real.exp 1 * e m),
    N07aSampleSubpower.mul hD hT (N07aSampleSubpower.const hD hT (Real.exp 1)) he,
    (fun m => hexp1.trans (le_mul_of_one_le_right hexp.le (he1 m))), ?_⟩
  intro z hz m x hx
  have hzold := n07a_sectorNeighborhood_mono (S := S) hb hηε hz
  have hzstate := liftSectorParameter_mem_stateNeighborhood (S := S) (C := C) hzold le_rfl
  have hs := hrefState.liftSectorParameter_sector z
  have hchart := hgeom.charts (liftSectorParameter S C z) hzstate hs m
  let y := K.chart (liftSectorParameter S C z) m x
  have hy : y ∈ canonicalOpen S K m := hchart.1 hx
  have hxy : K.inverseChart (liftSectorParameter S C z) m y = x := hchart.2.2.1 x hx
  let x₀ := K.inverseChart (C.referenceState, 0) m y
  have hx₀ : x₀ ∈ referencePhysicalPieceOpen S K m := by
    rw [← hgeom.referenceDomain m]
    exact (hgeom.charts (C.referenceState, 0) (n07a_reference_state_mem hε)
      hrefState.stateSector m).2.1 hy
  have hxD : x.1 ∈ radialCore D :=
    ((hgeom.domains (liftSectorParameter S C z) hzstate hs m).2.2.1 hx).1
  have hx₀D : x₀.1 ∈ radialCore D := (hgeom.referenceBounds m).2.2 hx₀.1
  have hdist : |x.1 - x₀.1| ≤ δ * T.ell x₀.1 := by
    simpa only [hxy] using hdisp z hz m y hy
  have hw := hwindow x₀.1 hx₀D x.1 hxD hdist
  have hr := heb m x₀ hx₀
  have hp := hT.2.1 x.1 hxD
  have hp₀ := hT.2.1 x₀.1 hx₀D
  have hps := hT.2.1 _
    (materialSample_mem_radialCore hT hD.choose_spec.2.1 (K.cell m))
  have he0 : 0 ≤ e m := zero_le_one.trans (he1 m)
  refine ⟨n07a_positive_ratio_chain hp₀.2.1 hps.2.1 hexp.le hw.1 hr.1, ?_,
    n07a_positive_ratio_chain (zero_lt_one.trans_le hp₀.2.2.2)
      (zero_lt_one.trans_le hps.2.2.2) hexp.le hw.2.2.1 hr.2.2.1, ?_⟩
  · simpa only [mul_comm] using
      n07a_positive_ratio_chain hp₀.2.1 hp.2.1 he0 hr.2.1 hw.2.1
  · simpa only [mul_comm] using
      n07a_positive_ratio_chain (zero_lt_one.trans_le hp₀.2.2.2)
        (zero_lt_one.trans_le hp.2.2.2) he0 hr.2.2.2 hw.2.2.2

end ContinuousFlexibility.Analysis
