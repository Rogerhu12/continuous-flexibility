import ContinuousFlexibility.Analysis.N01cRadialPowerInputs
import ContinuousFlexibility.Analysis.N01cInverseProfileBounds
import ContinuousFlexibility.Analysis.N01cProfileBaseBounds
import ContinuousFlexibility.Analysis.N01cCoefficientMixedParameterJets
import ContinuousFlexibility.Analysis.N01cStateInterpolation

/-!
# The actual radial inputs of the normalized coefficients

The three inputs are the state profile, its first radial derivative, and
its reciprocal. Their quantitative bounds use the original material
estimates, actual localization, and the actual parameter towers.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open Set Filter Function
open ContinuousFlexibility.Analysis ContinuousFlexibility.Blueprint
open scoped Topology ContDiff BigOperators

set_option backward.isDefEq.respectTransparency true

def coefficientRadialInput (D : ReferenceData) (S : PhysicalSpacesData)
    (C : NonlinearGeometryData S) : Fin 3 → AnnularState S → ℝ → ℝ :=
  Fin.cases (stateProfile D S C)
    (Fin.cases (fun x => deriv (stateProfile D S C x))
      (fun _ x r => (stateProfile D S C x r)⁻¹))

def coefficientRadialInputJets
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S}
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    (hA : N01PartA D T S C) (hD : RadialProfileGeometry D)
    (hχ : ContDiff ℝ ∞ D.chi) (n : ℕ) (r : ℝ) (hr : r ∈ Ioo D.a D.b) :
    ∀ i : Fin 3, SmoothDirections univ
      (fun x : AnnularState S => iteratedDeriv n (coefficientRadialInput D S C i x) r) :=
  Fin.cases
    (stateProfileRadialJetSmoothDirections hS hT hA.1.1 hD hA.2.2.1 hχ n r hr)
    (Fin.cases
      ((stateProfileRadialJetSmoothDirections hS hT hA.1.1 hD hA.2.2.1 hχ (n + 1) r hr).congr
        (fun _ _ => by rw [iteratedDeriv_succ']))
      (fun _ => stateInverseProfileRadialJetSmoothDirections
        hS hT hA.1.1 hD hA.2.2.1 hχ n r hr))

/-- The actual partition of unity covers every interior radial point. -/
theorem radialPartition_exists_cell {D : ReferenceData} (hP : RadialPartition D)
    {r : ℝ} (hr : r ∈ Ioo D.a D.b) : ∃ m, r ∈ D.cells m := by
  by_contra hnone
  have hz (m : ℕ) : D.localizer m r = 0 := by
    by_contra hm
    exact hnone ⟨m, hP.2.2.1 m hm⟩
  have hh := (hP.2.2.2.2.1 r hr).2
  simp only [hz, tsum_zero] at hh
  norm_num at hh

def coefficientRadialInput_regular
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {base : ℕ} {ε : ℝ}
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    (hA : N01PartA D T S C) (hB : N01PartB D S C base ε) (i : Fin 3) :
    MixedJetRegularity (stateNeighborhood S C base ε) (annularOpen D)
      (fun z q => coefficientRadialInput D S C i z.1 q.1) := by
  letI : IsTopologicalAddGroup (AnnularState S × ℝ) := inferInstance
  letI : ContinuousSMul ℝ (AnnularState S × ℝ) := inferInstance
  have hD : RadialProfileGeometry D := hA.1.1.choose_spec.1
  have hχ : ContDiff ℝ ∞ D.chi := hA.1.2.2.2.1.1
  let L : (AnnularState S × ℝ) →L[ℝ] AnnularState S :=
    ContinuousLinearMap.fst ℝ (AnnularState S) ℝ
  apply radialMixedRegularity (isOpen_stateNeighborhood S C base ε)
    (fun z r => coefficientRadialInput D S C i z.1 r)
    (Jr := fun n r hr => smoothDirections_precompCLM
      (coefficientRadialInputJets hS hT hA hD hχ n r hr i) L)
  intro z hz
  fin_cases i
  · exact (contDiff_stateProfile_of_partA hS hT hA z.1).contDiffOn
  · exact ((contDiff_infty_iff_deriv.mp
      (contDiff_stateProfile_of_partA hS hT hA z.1)).2).contDiffOn
  · intro r hr
    have hw := (n01PartB_denominators_pos hD hS hA.2.1 hB hz
      (p := (r, 0)) ⟨hr, mem_univ _⟩).1
    exact ((contDiff_stateProfile_of_partA hS hT hA z.1).contDiffAt.inv hw.ne').contDiffWithinAt

/-- The actual profile, profile derivative and inverse profile have the
same mixed power control, at any fixed interpolation indices. -/
theorem coefficientRadialInput_powerBounds
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {base loss : ℕ} {ε : ℝ}
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    (hA : N01PartA D T S C) (hε : 0 < ε)
    (hB : N01PartB D S C base ε)
    (hE : ∀ r ∈ Ioo D.a D.b, 1 ≤ T.E0 r)
    (hloc : ∀ m, Ioo (C.left m) (C.right m) ⊆ D.cells (C.cell m))
    (hχloc : tsupport D.chi ⊆ Ioo D.a D.b) (i : Fin 3) :
    MixedPowerBounds (pairGrading (stateGrading S) realGrading) (C.referenceState, 0)
      base loss (stateNeighborhood S C base ε) (annularOpen D)
      (fun q => T.H q.1 ^ (3 / 4 : ℝ)) (fun q => T.E0 q.1)
      (fun z q => coefficientRadialInput D S C i z.1 q.1) := by
  letI : IsTopologicalAddGroup (AnnularState S × ℝ) := inferInstance
  letI : ContinuousSMul ℝ (AnnularState S × ℝ) := inferInstance
  have hD : RadialProfileGeometry D := hA.1.1.choose_spec.1
  have hχ : ContDiff ℝ ∞ D.chi := hA.1.2.2.2.1.1
  have hP : RadialPartition D := hA.1.1.choose_spec.2.1
  let L : (AnnularState S × ℝ) →L[ℝ] AnnularState S :=
    ContinuousLinearMap.fst ℝ (AnnularState S) ℝ
  apply projectedRadialJets_powerBounds (Y := AnnularState S)
    (pairGrading (stateGrading S) realGrading) (stateGrading S 0)
    (C.referenceState, 0) base loss
    (fun r hr => Real.rpow_nonneg (hT.2.1 r hr).2.1.le _) hE L
    (fun v => by
      simp only [L, ContinuousLinearMap.coe_fst']
      exact ((stateGrading_monotone S (Nat.zero_le base)) v.1).trans
        (by rw [tamePairGrading_apply]; exact le_add_of_nonneg_right (apply_nonneg _ _)))
    (coefficientRadialInput D S C i)
    (fun n r hr => coefficientRadialInputJets hS hT hA hD hχ n r hr i)
  · intro n
    fin_cases i
    · obtain ⟨B, A, hB0, hA0, hb⟩ :=
        iteratedDeriv_stateProfile_material_bound hS hT hA hD hχ hε hB hE hloc hχloc n
      refine ⟨B, A, hB0, hA0.le, fun r hr z hz => ?_⟩
      obtain ⟨m, hm⟩ := radialPartition_exists_cell hP hr
      simpa only [Real.norm_eq_abs, coefficientRadialInput, Fin.cases_zero,
        L, ContinuousLinearMap.coe_fst'] using hb m r hr hm z hz
    · obtain ⟨B, A, hB0, hA0, hb⟩ :=
        iteratedDeriv_stateProfile_material_bound hS hT hA hD hχ hε hB hE hloc hχloc (n + 1)
      refine ⟨B, A, hB0, hA0.le, fun r hr z hz => ?_⟩
      obtain ⟨m, hm⟩ := radialPartition_exists_cell hP hr
      simpa only [Real.norm_eq_abs, coefficientRadialInput, Fin.cases_succ, Fin.cases_zero,
        iteratedDeriv_succ', L, ContinuousLinearMap.coe_fst'] using hb m r hr hm z hz
    · obtain ⟨B, A, hB0, hA0, hb⟩ :=
        iteratedDeriv_stateInverseProfile_material_bound hS hT hA hD hχ hε hB hE hloc hχloc n
      refine ⟨B, A, hB0, hA0.le, fun r hr z hz => ?_⟩
      obtain ⟨m, hm⟩ := radialPartition_exists_cell hP hr
      simpa only [Real.norm_eq_abs, coefficientRadialInput, Fin.cases_succ,
        L, ContinuousLinearMap.coe_fst'] using hb m r hr hm z hz
  · intro n k hk
    fin_cases i
    · obtain ⟨B, A, hB0, hA0, hb⟩ :=
        stateProfileRadialJetSmoothDirections_material_bound
          hS hT hA hD hχ hε hB hE hloc hχloc n k hk
      refine ⟨B, A, hB0, hA0.le, fun r hr z hz v => ?_⟩
      obtain ⟨m, hm⟩ := radialPartition_exists_cell hP hr
      simpa only [Real.norm_eq_abs, coefficientRadialInputJets, Fin.cases_zero,
        L, ContinuousLinearMap.coe_fst', mul_assoc, mul_left_comm, mul_comm] using hb m r hr hm z hz v
    · obtain ⟨B, A, hB0, hA0, hb⟩ :=
        stateProfileRadialJetSmoothDirections_material_bound
          hS hT hA hD hχ hε hB hE hloc hχloc (n + 1) k hk
      refine ⟨B, A, hB0, hA0.le, fun r hr z hz v => ?_⟩
      obtain ⟨m, hm⟩ := radialPartition_exists_cell hP hr
      simpa only [Real.norm_eq_abs, coefficientRadialInputJets, Fin.cases_succ, Fin.cases_zero,
        L, ContinuousLinearMap.coe_fst', mul_assoc, mul_left_comm, mul_comm] using hb m r hr hm z hz v
    · obtain ⟨B, A, hB0, hA0, hb⟩ :=
        stateInverseProfileRadialJetSmoothDirections_material_bound
          hS hT hA hD hχ hε hB hE hloc hχloc n k hk
      refine ⟨B, A, hB0, hA0.le, fun r hr z hz v => ?_⟩
      obtain ⟨m, hm⟩ := radialPartition_exists_cell hP hr
      simpa only [Real.norm_eq_abs, coefficientRadialInputJets, Fin.cases_succ,
        L, ContinuousLinearMap.coe_fst', mul_assoc, mul_left_comm, mul_comm] using hb m r hr hm z hz v

end ContinuousFlexibility.Statements
