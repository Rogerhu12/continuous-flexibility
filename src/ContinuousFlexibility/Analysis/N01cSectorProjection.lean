module

public import ContinuousFlexibility.Analysis.N01cStateSeminorms
public import ContinuousFlexibility.Analysis.SolveCircleProjection

/-!
# A norm-contracting sector projection preserving the nonlinear geometry

The profile uses the angular mean of the control circle and is independent
of the chart component. The existing continuous angular-mean projection
therefore preserves profile and height and contracts the actual state
grading. Geometric properties proved on the sector extend to the entire
same parameter neighbourhood.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Statements

open Set MeasureTheory ContinuousFlexibility.Analysis
open scoped ContDiff ENNReal BigOperators

theorem angularMean_const (c : ℝ) : angularMean (fun _ => c) = c := by
  rw [angularMean, intervalIntegral.integral_const, sub_zero, smul_eq_mul]
  field_simp [Real.pi_ne_zero] <;> ring

private theorem paired_projection_displacement_le
    {H K : Type*} [AddCommGroup H] [Module ℝ H] [AddCommGroup K] [Module ℝ K]
    (p : Seminorm ℝ H) (q : Seminorm ℝ K) (P : K → K)
    (x y : (H × ℝ) × (ℝ × (K × K)))
    (hκ : y.2.2.1 = 0) (hθ : y.2.2.2 = 0)
    (hP : q (P x.2.2.1) ≤ q x.2.2.1) :
    (p (x.1.1 - y.1.1) + ‖x.1.2 - y.1.2‖) +
        (‖x.2.1 - y.2.1‖ +
          (q (P x.2.2.1 - y.2.2.1) + q (0 - y.2.2.2))) ≤
      (p (x.1.1 - y.1.1) + ‖x.1.2 - y.1.2‖) +
        (‖x.2.1 - y.2.1‖ +
          (q (x.2.2.1 - y.2.2.1) + q (x.2.2.2 - y.2.2.2))) := by
  simp only [hκ, hθ, sub_zero]
  exact add_le_add le_rfl (add_le_add le_rfl
    (add_le_add hP (q.map_zero'.trans_le (apply_nonneg q x.2.2.2))))

def stateSectorProjection {D : ReferenceData} {T : MaterialData}
    {S : PhysicalSpacesData} (hS : IsPhysicalSpaces D T S)
    (x : AnnularState S) : AnnularState S :=
  (x.1, (x.2.1, (circleAngularMeanProjection (hS.2.1 (3 / 4 : ℝ)) x.2.2.1, 0)))

theorem stateSectorProjection_sector {D : ReferenceData} {T : MaterialData}
    {S : PhysicalSpacesData} (hS : IsPhysicalSpaces D T S) (x : AnnularState S) :
    stateSector S (stateSectorProjection hS x) := by
  constructor
  · exact circleAngularMeanProjection_constant (hS.2.1 (3 / 4 : ℝ)) x.2.2.1
  · intro m θ
    change (S.circle (3 / 4 : ℝ)).decode 0 m (-θ) =
      -(S.circle (3 / 4 : ℝ)).decode 0 m θ
    simp only [map_zero, Pi.zero_apply, neg_zero]

theorem stateKappa_stateSectorProjection {D : ReferenceData} {T : MaterialData}
    {S : PhysicalSpacesData} (hS : IsPhysicalSpaces D T S)
    (x : AnnularState S) (m : ℕ) :
    stateKappa S (stateSectorProjection hS x) m = stateKappa S x m := by
  change angularMean ((S.circle (3 / 4 : ℝ)).decode
      (circleAngularMeanProjection (hS.2.1 (3 / 4 : ℝ)) x.2.2.1) m) = _
  have he :
      (S.circle (3 / 4 : ℝ)).decode
        (circleAngularMeanProjection (hS.2.1 (3 / 4 : ℝ)) x.2.2.1) m =
      (fun _ : ℝ => angularMean ((S.circle (3 / 4 : ℝ)).decode x.2.2.1 m)) :=
    funext (circleAngularMeanProjection_decode (hS.2.1 (3 / 4 : ℝ)) x.2.2.1 m)
  rw [he]
  exact angularMean_const _

theorem stateU_stateSectorProjection {D : ReferenceData} {T : MaterialData}
    {S : PhysicalSpacesData} (hS : IsPhysicalSpaces D T S) (x : AnnularState S) :
    stateU S (stateSectorProjection hS x) = stateU S x := rfl

theorem stateProfile_stateSectorProjection {D : ReferenceData} {T : MaterialData}
    {S : PhysicalSpacesData} (hS : IsPhysicalSpaces D T S)
    (C : NonlinearGeometryData S) (x : AnnularState S) :
    stateProfile D S C (stateSectorProjection hS x) = stateProfile D S C x := by
  funext r
  have hν : (stateSectorProjection hS x).2.1 = x.2.1 := rfl
  simp only [stateProfile, stateKappa_stateSectorProjection, hν]

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

set_option backward.isDefEq.respectTransparency true in
theorem stateSectorProjection_displacement_grading_le
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} (hS : IsPhysicalSpaces D T S)
    (href : referenceStateConditions D S C) (x : AnnularState S) (n : ℕ) :
    stateGrading S n (stateSectorProjection hS x - C.referenceState) ≤
      stateGrading S n (x - C.referenceState) := by
  have hkappa := href.2.2.2.1
  have hchart := href.2.2.2.2.1
  have hk : (S.circle (3 / 4 : ℝ)).grading n
      (circleAngularMeanProjection (hS.2.1 (3 / 4 : ℝ)) x.2.2.1) ≤
      (S.circle (3 / 4 : ℝ)).grading n x.2.2.1 :=
    circleAngularMeanLinear_grading_le (hS.2.1 (3 / 4 : ℝ)) n x.2.2.1
  have h := paired_projection_displacement_le
    ((S.height (3 / 4 : ℝ)).grading n) ((S.circle (3 / 4 : ℝ)).grading n)
    (circleAngularMeanProjection (hS.2.1 (3 / 4 : ℝ))) x C.referenceState hkappa hchart hk
  simpa only [stateGrading_apply, Prod.fst_sub, Prod.snd_sub, stateSectorProjection] using h

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
