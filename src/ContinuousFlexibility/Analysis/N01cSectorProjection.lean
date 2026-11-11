import ContinuousFlexibility.Analysis.N01cStateSeminorms

/-!
# A norm-contracting sector projection preserving the nonlinear geometry

The profile uses the angular mean of each control circle and does not use
the left-chart component. Averaging the controls and setting the chart
component to zero therefore preserves the profile and height. This file
constructs that operation in any actual `IsCircleModel`, proves contraction
in every grading, and shows that the common state neighbourhood is
preserved. Thus a geometric property known on sector states extends to all
states whenever it depends only on the actual profile and height.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open Set MeasureTheory ContinuousFlexibility.Analysis
open scoped ContDiff ENNReal BigOperators

set_option backward.isDefEq.respectTransparency false

private theorem angleMeasure_univ_for_projection :
    angleMeasure univ = ENNReal.ofReal Real.pi := by
  rw [angleMeasure, Measure.restrict_apply_univ, Real.volume_Ioc, sub_zero]

private instance projection_angleMeasure_finite : IsFiniteMeasure angleMeasure :=
  ⟨by rw [angleMeasure_univ_for_projection]; exact ENNReal.ofReal_lt_top⟩

theorem angularMean_const (c : ℝ) : angularMean (fun _ => c) = c := by
  rw [angularMean, intervalIntegral.integral_const, sub_zero, smul_eq_mul]
  field_simp [Real.pi_ne_zero] <;> ring

/-- The constant function with value equal to the normalized angular mean
is the `L²` contraction onto the constant angular mode. -/
theorem eLpNorm_angularMean_const_le {f : ℝ → ℝ} (hf : MemLp f 2 angleMeasure) :
    eLpNorm (fun _ : ℝ => angularMean f) 2 angleMeasure ≤ eLpNorm f 2 angleMeasure := by
  have hc : MemLp (fun _ : ℝ => angularMean f) 2 angleMeasure := memLp_const _
  apply (ENNReal.toReal_le_toReal hc.eLpNorm_ne_top hf.eLpNorm_ne_top).mp
  have hconst (c : ℝ) :
      (eLpNorm (fun _ : ℝ => c) 2 angleMeasure).toReal = |c| * Real.sqrt Real.pi := by
    rw [eLpNorm_const' c (by norm_num) (by norm_num), ENNReal.toReal_mul,
      toReal_enorm, Real.norm_eq_abs, ENNReal.toReal_rpow,
      angleMeasure_univ_for_projection, ENNReal.toReal_ofReal Real.pi_pos.le]
    congr 1
    rw [Real.sqrt_eq_rpow]
    norm_num
  rw [hconst]
  calc
    |angularMean f| * Real.sqrt Real.pi ≤
        (((1 / Real.pi) * Real.sqrt Real.pi) *
          (eLpNorm f 2 angleMeasure).toReal) * Real.sqrt Real.pi :=
      mul_le_mul_of_nonneg_right (abs_angularMean_le_angleL2 hf) (Real.sqrt_nonneg _)
    _ = (eLpNorm f 2 angleMeasure).toReal := by
      have hsq : Real.sqrt Real.pi * Real.sqrt Real.pi = Real.pi :=
        Real.mul_self_sqrt Real.pi_pos.le
      calc
        _ = ((Real.sqrt Real.pi * Real.sqrt Real.pi) / Real.pi) *
            (eLpNorm f 2 angleMeasure).toReal := by ring
        _ = _ := by rw [hsq, div_self Real.pi_ne_zero, one_mul]

def circleMeanField (u : ℕ → ℝ → ℝ) : ℕ → ℝ → ℝ :=
  fun m _ => angularMean (u m)

theorem circleMeanField_iteratedDeriv (u : ℕ → ℝ → ℝ) (m b : ℕ) :
    iteratedDeriv b (circleMeanField u m) =
      (fun _ => if b = 0 then angularMean (u m) else 0) := by
  funext θ
  exact iteratedDeriv_const

theorem circleMeanField_jet_eLpNorm_le {T : MaterialData} {γ : ℝ}
    {u : ℕ → ℝ → ℝ} (hu : CircleMember T γ u) (m b : ℕ) :
    eLpNorm (iteratedDeriv b (circleMeanField u m)) 2 angleMeasure ≤
      eLpNorm (iteratedDeriv b (u m)) 2 angleMeasure := by
  by_cases hb : b = 0
  · subst b
    simpa only [iteratedDeriv_zero, circleMeanField] using
      eLpNorm_angularMean_const_le (hu.2.1 m 0)
  · rw [circleMeanField_iteratedDeriv]
    simp only [hb, if_false, eLpNorm_zero]
    exact zero_le

private theorem circleMeanField_energy_le {T : MaterialData} {γ : ℝ}
    {u : ℕ → ℝ → ℝ} (hu : CircleMember T γ u) (s : ℕ) :
    (∑' m : ℕ, ∑ j : CircleJetIndex s,
      ENNReal.ofReal ((T.M (T.sample m) ^ (j.val 1).val *
        T.H (T.sample m) ^ (-γ)) ^ 2) *
        eLpNorm (iteratedDeriv (j.val 0).val (circleMeanField u m)) 2 angleMeasure ^ 2) ≤
    (∑' m : ℕ, ∑ j : CircleJetIndex s,
      ENNReal.ofReal ((T.M (T.sample m) ^ (j.val 1).val *
        T.H (T.sample m) ^ (-γ)) ^ 2) *
        eLpNorm (iteratedDeriv (j.val 0).val (u m)) 2 angleMeasure ^ 2) := by
  apply ENNReal.tsum_le_tsum
  intro m
  apply Finset.sum_le_sum
  intro j _
  exact mul_le_mul_left' (pow_le_pow_left' (circleMeanField_jet_eLpNorm_le hu m _) 2) _

/-- Averaging preserves the full smooth weighted circle space, including
all the summability requirements in its definition. -/
theorem circleMember_circleMeanField {T : MaterialData} {γ : ℝ}
    {u : ℕ → ℝ → ℝ} (hu : CircleMember T γ u) :
    CircleMember T γ (circleMeanField u) := by
  refine ⟨fun m => ⟨contDiff_const, fun _ => rfl⟩, ?_, ?_⟩
  · intro m b
    rw [circleMeanField_iteratedDeriv]
    exact memLp_const _
  · intro s
    exact (circleMeanField_energy_le hu s).trans_lt (hu.2.2 s)

theorem circleNorm_circleMeanField_le {T : MaterialData} {γ : ℝ}
    {u : ℕ → ℝ → ℝ} (hu : CircleMember T γ u) (s : ℕ) :
    circleNorm T γ s (circleMeanField u) ≤ circleNorm T γ s u := by
  exact Real.sqrt_le_sqrt (ENNReal.toReal_mono (hu.2.2 s).ne
    (circleMeanField_energy_le hu s))

/-- Every realization contains the exact averaged field, and its actual
grading decreases at every order. -/
theorem exists_circleMeanProjection {T : MaterialData} {γ : ℝ}
    {M : CircleModelData} (hM : IsCircleModel T γ M) (u : M.Space) :
    ∃ v : M.Space, M.decode v = circleMeanField (M.decode u) ∧
      ∀ n : ℕ, M.grading n v ≤ M.grading n u := by
  have hdata := hM
  obtain ⟨_, _, _, hmember, hsurj, _, _, hnorm⟩ := hdata
  obtain ⟨v, hv⟩ := hsurj _ (circleMember_circleMeanField (hmember u))
  refine ⟨v, hv, fun n => ?_⟩
  apply (gradedSeminorm_le_iff (fun i => M.level i) M.bond n v
    (apply_nonneg (M.grading n) u)).mpr
  intro i hi
  rw [hnorm v i, hv]
  exact (circleNorm_circleMeanField_le (hmember u) i).trans
    (circleNorm_decode_le_grading hM u hi)

def circleMeanProjection {T : MaterialData} {γ : ℝ} {M : CircleModelData}
    (hM : IsCircleModel T γ M) (u : M.Space) : M.Space :=
  (exists_circleMeanProjection hM u).choose

theorem circleMeanProjection_decode {T : MaterialData} {γ : ℝ}
    {M : CircleModelData} (hM : IsCircleModel T γ M) (u : M.Space) :
    M.decode (circleMeanProjection hM u) = circleMeanField (M.decode u) :=
  (exists_circleMeanProjection hM u).choose_spec.1

theorem circleMeanProjection_grading_le {T : MaterialData} {γ : ℝ}
    {M : CircleModelData} (hM : IsCircleModel T γ M) (u : M.Space) (n : ℕ) :
    M.grading n (circleMeanProjection hM u) ≤ M.grading n u :=
  (exists_circleMeanProjection hM u).choose_spec.2 n

def stateSectorProjection {D : ReferenceData} {T : MaterialData}
    {S : PhysicalSpacesData} (hS : IsPhysicalSpaces D T S)
    (x : AnnularState S) : AnnularState S :=
  (x.1, (x.2.1, (circleMeanProjection (hS.2.1 (3 / 4 : ℝ)) x.2.2.1, 0)))

theorem stateSectorProjection_sector {D : ReferenceData} {T : MaterialData}
    {S : PhysicalSpacesData} (hS : IsPhysicalSpaces D T S) (x : AnnularState S) :
    stateSector S (stateSectorProjection hS x) := by
  constructor
  · intro m θ φ
    change (S.circle (3 / 4 : ℝ)).decode
        (circleMeanProjection (hS.2.1 (3 / 4 : ℝ)) x.2.2.1) m θ =
      (S.circle (3 / 4 : ℝ)).decode
        (circleMeanProjection (hS.2.1 (3 / 4 : ℝ)) x.2.2.1) m φ
    simp only [circleMeanProjection_decode, circleMeanField]
  · intro m θ
    change (S.circle (3 / 4 : ℝ)).decode 0 m (-θ) =
      -(S.circle (3 / 4 : ℝ)).decode 0 m θ
    simp only [map_zero, Pi.zero_apply, neg_zero]

theorem stateKappa_stateSectorProjection {D : ReferenceData} {T : MaterialData}
    {S : PhysicalSpacesData} (hS : IsPhysicalSpaces D T S)
    (x : AnnularState S) (m : ℕ) :
    stateKappa S (stateSectorProjection hS x) m = stateKappa S x m := by
  change angularMean ((S.circle (3 / 4 : ℝ)).decode
      (circleMeanProjection (hS.2.1 (3 / 4 : ℝ)) x.2.2.1) m) = _
  rw [circleMeanProjection_decode]
  exact angularMean_const _

theorem stateU_stateSectorProjection {D : ReferenceData} {T : MaterialData}
    {S : PhysicalSpacesData} (hS : IsPhysicalSpaces D T S) (x : AnnularState S) :
    stateU S (stateSectorProjection hS x) = stateU S x := rfl

theorem stateProfile_stateSectorProjection {D : ReferenceData} {T : MaterialData}
    {S : PhysicalSpacesData} (hS : IsPhysicalSpaces D T S)
    (C : NonlinearGeometryData S) (x : AnnularState S) :
    stateProfile D S C (stateSectorProjection hS x) = stateProfile D S C x := by
  funext r
  simpa only [stateProfile, stateKappa_stateSectorProjection]

theorem stateHeight_stateSectorProjection {D : ReferenceData} {T : MaterialData}
    {S : PhysicalSpacesData} (hS : IsPhysicalSpaces D T S)
    (C : NonlinearGeometryData S) (x : AnnularState S) (q : ℝ) :
    stateHeight D S C (stateSectorProjection hS x, q) = stateHeight D S C (x, q) := by
  funext p
  simp only [stateHeight, stateRadialHeight, stateProfile_stateSectorProjection,
    stateU_stateSectorProjection]

theorem originalCoefficients_stateSectorProjection {D : ReferenceData} {T : MaterialData}
    {S : PhysicalSpacesData} (hS : IsPhysicalSpaces D T S)
    (C : NonlinearGeometryData S) (x : AnnularState S) (q : ℝ) :
    originalCoefficients D S C (stateSectorProjection hS x, q) =
      originalCoefficients D S C (x, q) := by
  simp only [originalCoefficients, stateProfile_stateSectorProjection,
    stateHeight_stateSectorProjection]

theorem stateSectorProjection_displacement_grading_le
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} (hS : IsPhysicalSpaces D T S)
    (href : referenceStateConditions D S C) (x : AnnularState S) (n : ℕ) :
    stateGrading S n (stateSectorProjection hS x - C.referenceState) ≤
      stateGrading S n (x - C.referenceState) := by
  obtain ⟨_, _, _, hkappa, hchart, _⟩ := href
  rw [stateGrading_apply, stateGrading_apply]
  simp only [Prod.fst_sub, Prod.snd_sub, stateSectorProjection, hkappa, hchart,
    sub_zero, map_zero]
  have hk := circleMeanProjection_grading_le (hS.2.1 (3 / 4 : ℝ)) x.2.2.1 n
  have hc := apply_nonneg ((S.circle (3 / 4 : ℝ)).grading n) x.2.2.2
  linarith

/-- The projection preserves the exact same low-order radius; no new
smallness or order-dependent neighbourhood is introduced. -/
theorem stateSectorProjection_mem_neighborhood
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} (hS : IsPhysicalSpaces D T S)
    (href : referenceStateConditions D S C) {base : ℕ} {ε : ℝ}
    {z : AnnularState S × ℝ} (hz : z ∈ stateNeighborhood S C base ε) :
    (stateSectorProjection hS z.1, z.2) ∈ stateNeighborhood S C base ε :=
  ⟨(stateSectorProjection_displacement_grading_le hS href z.1 base).trans_lt hz.1, hz.2⟩

/-- Any property of the actual profile and height extends from sector
states to the entire common neighbourhood. This applies in particular to
the denominator and discriminant bounds of N01b. -/
theorem stateGeometry_property_of_sector
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} (hS : IsPhysicalSpaces D T S)
    (href : referenceStateConditions D S C) {base : ℕ} {ε : ℝ}
    (P : (ℝ → ℝ) → (PolarPoint → ℝ) → Prop)
    (hP : ∀ z ∈ stateNeighborhood S C base ε, stateSector S z.1 →
      P (stateProfile D S C z.1) (stateHeight D S C z)) :
    ∀ z ∈ stateNeighborhood S C base ε,
      P (stateProfile D S C z.1) (stateHeight D S C z) := by
  intro z hz
  have h := hP (stateSectorProjection hS z.1, z.2)
    (stateSectorProjection_mem_neighborhood hS href hz)
    (stateSectorProjection_sector hS z.1)
  simpa only [stateProfile_stateSectorProjection, stateHeight_stateSectorProjection] using h

end ContinuousFlexibility.Statements
