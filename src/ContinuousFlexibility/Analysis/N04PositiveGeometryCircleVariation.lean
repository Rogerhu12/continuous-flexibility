import ContinuousFlexibility.Analysis.CircleSingleComponent
import ContinuousFlexibility.Analysis.N01ResidualCircleModel
import ContinuousFlexibility.Analysis.N01RootLabels

/-!
# A nonzero chart variation in every sector neighborhood

The circle model realizes the smooth periodic field `sin (2 * θ)` on
one selected component. Placing it in the chart slot gives a genuine
sector direction whose other state fields vanish. Positive multiples
arbitrarily close to zero lie in any positive sector neighborhood. Their
actual left root label moves `π / 4` by exactly the scalar multiple.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set ContinuousFlexibility.Statements CanonicalGeometry
open scoped ContDiff

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

private theorem sineDouble_circleMember (T : MaterialData) (γ : ℝ) (m : ℕ) :
    CircleMember T γ (circleSingleComponentField m (fun θ => Real.sin (2 * θ))) := by
  apply circleSingleComponentField_member T γ m _
    ((contDiff_const.mul contDiff_id).sin)
  intro θ
  change Real.sin (2 * (θ + Real.pi)) = Real.sin (2 * θ)
  rw [mul_add, Real.sin_add_two_pi]

/-- A circle element with exactly the prescribed single-component sine
field; surjectivity is the original exact circle-model certificate. -/
def n04PositiveGeometry_circleSine
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    (hS : IsPhysicalSpaces D T S) (m : ℕ) : CircleSpace S :=
  ((hS.2.1 (3 / 4 : ℝ)).2.2.2.2.1
    (circleSingleComponentField m (fun θ => Real.sin (2 * θ)))
    (sineDouble_circleMember T (3 / 4 : ℝ) m)).choose

theorem n04PositiveGeometry_circleSine_decode
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    (hS : IsPhysicalSpaces D T S) (m : ℕ) :
    (S.circle (3 / 4 : ℝ)).decode (n04PositiveGeometry_circleSine hS m) =
      circleSingleComponentField m (fun θ => Real.sin (2 * θ)) :=
  ((hS.2.1 (3 / 4 : ℝ)).2.2.2.2.1
    (circleSingleComponentField m (fun θ => Real.sin (2 * θ)))
    (sineDouble_circleMember T (3 / 4 : ℝ) m)).choose_spec

/-- The chart-only sine perturbation is an actual sector direction,
with zero height, scalar normalization and profile-control entries. -/
def n04PositiveGeometry_circleDirection
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    (hS : IsPhysicalSpaces D T S) (m : ℕ) : StateDirections S := by
  refine ⟨((0 : HeightPair S), 0, (0 : CircleSpace S),
    n04PositiveGeometry_circleSine hS m), ?_⟩
  change stateSector S
    ((0 : HeightPair S), 0, (0 : CircleSpace S), n04PositiveGeometry_circleSine hS m)
  constructor
  · intro k θ φ
    simp only [map_zero, Pi.zero_apply]
  · intro k θ
    rw [n04PositiveGeometry_circleSine_decode]
    by_cases hk : k = m <;>
      simp only [circleSingleComponentField, hk, ↓reduceIte, mul_neg, Real.sin_neg,
        neg_zero]

theorem n04PositiveGeometry_circleDirection_fields
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    (hS : IsPhysicalSpaces D T S) (m : ℕ) :
    (n04PositiveGeometry_circleDirection hS m).val.1 = 0 ∧
      (n04PositiveGeometry_circleDirection hS m).val.2.1 = 0 ∧
      (n04PositiveGeometry_circleDirection hS m).val.2.2.1 = 0 ∧
      (S.circle (3 / 4 : ℝ)).decode
        (n04PositiveGeometry_circleDirection hS m).val.2.2.2 =
        circleSingleComponentField m (fun θ => Real.sin (2 * θ)) :=
  ⟨rfl, rfl, rfl, n04PositiveGeometry_circleSine_decode hS m⟩

private theorem exists_positive_small_seminorm_multiple
    {E : Type*} [AddCommGroup E] [Module ℝ E]
    (p : Seminorm ℝ E) (v : E) {ε : ℝ} (hε : 0 < ε) :
    ∃ a : ℝ, 0 < a ∧ a < 1 ∧ p (a • v) < ε := by
  let N : ℝ := p v
  let a : ℝ := (min ε 1 / 2) / (N + 1)
  have hN : 0 ≤ N := apply_nonneg p v
  have hden : 0 < N + 1 := by linarith only [hN]
  have ha : 0 < a := div_pos (half_pos (lt_min hε zero_lt_one)) hden
  have heq : a * (N + 1) = min ε 1 / 2 := div_mul_cancel₀ _ hden.ne'
  have hεmin : min ε 1 ≤ ε := min_le_left _ _
  have h1min : min ε 1 ≤ 1 := min_le_right _ _
  refine ⟨a, ha, ?_, ?_⟩
  · nlinarith only [heq, mul_nonneg ha.le hN, h1min]
  · rw [map_smul_eq_mul, Real.norm_eq_abs, abs_of_pos ha]
    change a * N < ε
    nlinarith only [heq, ha, hεmin, hε]

/-- The nonzero chart direction is reachable in every positive
neighborhood, including those chosen after the normalization buffer. -/
theorem n04PositiveGeometry_circleDirection_small
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    (hS : IsPhysicalSpaces D T S) (m b : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∃ a : ℝ, 0 < a ∧ a < 1 ∧
      (a • n04PositiveGeometry_circleDirection hS m, (0 : ℝ)) ∈
        sectorNeighborhood S b ε ε := by
  let h := exists_positive_small_seminorm_multiple
    (sectorGrading S b) (n04PositiveGeometry_circleDirection hS m) hε
  exact ⟨h.choose, h.choose_spec.1, h.choose_spec.2.1, h.choose_spec.2.2,
    by simpa only [abs_zero] using hε⟩

private theorem real_seminorm_smul
    {E : Type*} [AddCommGroup E] [Module ℝ E]
    (p : Seminorm ℝ E) (a : ℝ) (v : E) : p (a • v) = |a| * p v := by
  rw [map_smul_eq_mul, Real.norm_eq_abs]

private theorem real_seminorm_smul_zero
    {E : Type*} [AddCommGroup E] [Module ℝ E]
    (p : Seminorm ℝ (E × ℝ)) (a : ℝ) (v : E) :
    p (a • v, 0) = |a| * p (v, 0) := by
  have hpair : (a • v, (0 : ℝ)) = a • (v, (0 : ℝ)) := by
    rw [Prod.smul_mk, smul_zero]
  exact (congrArg p hpair).trans (real_seminorm_smul p a (v, 0))

private theorem real_seminorm_nonneg_smul_zero
    {E : Type*} [AddCommGroup E] [Module ℝ E]
    (p : Seminorm ℝ (E × ℝ)) {a : ℝ} (ha : 0 ≤ a) (v : E) :
    p (a • v, 0) = a * p (v, 0) :=
  (real_seminorm_smul_zero p a v).trans
    (congrArg (fun t : ℝ => t * p (v, 0)) (abs_of_nonneg ha))

/-- The parameter grading is exactly homogeneous along a state line with
zero auxiliary scalar parameter. The calculation does not unfold the
physical grading. -/
theorem n04PositiveGeometry_parameterGrading_smul_zero
    (S : PhysicalSpacesData) (n : ℕ) (v : StateDirections S) (a : ℝ) :
    parameterGrading S n (a • v, 0) = |a| * parameterGrading S n (v, 0) :=
  real_seminorm_smul_zero (parameterGrading S n) a v

/-- The common positive amplitude cancels from every grading of the
chosen sine direction. -/
theorem n04PositiveGeometry_circleDirection_parameterGrading
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    (hS : IsPhysicalSpaces D T S) (m n : ℕ) {a : ℝ} (ha : 0 ≤ a) :
    parameterGrading S n (a • n04PositiveGeometry_circleDirection hS m, 0) =
      a * parameterGrading S n (n04PositiveGeometry_circleDirection hS m, 0) :=
  real_seminorm_nonneg_smul_zero (parameterGrading S n) ha
    (n04PositiveGeometry_circleDirection hS m)

/-- The actual left chart on this line, at every component and angle. -/
theorem n04PositiveGeometry_circleDirection_leftChart
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} (hS : IsPhysicalSpaces D T S)
    (href : referenceStateConditions D S C) (m : ℕ) (a : ℝ) (k : ℕ) (θ : ℝ) :
    stateLeftChart S
        (liftSectorParameter S C (a • n04PositiveGeometry_circleDirection hS m, 0)).1
        k θ = θ + a * (if k = m then Real.sin (2 * θ) else 0) := by
  rw [href.sector_leftChart]
  change θ + (S.circle (3 / 4 : ℝ)).decode
    (a • n04PositiveGeometry_circleSine hS m) k θ = _
  rw [map_smul, n04PositiveGeometry_circleSine_decode]
  simp only [Pi.smul_apply, smul_eq_mul, circleSingleComponentField]

/-- At the fixed test angle the displacement equals the scalar
coefficient, so every positive multiple gives a nonidentity root label. -/
theorem n04PositiveGeometry_circleDirection_rootLabel_test
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} (hS : IsPhysicalSpaces D T S)
    (href : referenceStateConditions D S C) (m : ℕ) (a : ℝ) :
    n01RootLabel S C
        (liftSectorParameter S C (a • n04PositiveGeometry_circleDirection hS m, 0))
        m false (Real.pi / 4) = Real.pi / 4 + a := by
  change stateLeftChart S
    (liftSectorParameter S C (a • n04PositiveGeometry_circleDirection hS m, 0)).1
    m (Real.pi / 4) = _
  rw [n04PositiveGeometry_circleDirection_leftChart hS href m a m]
  simp only [ite_true, show 2 * (Real.pi / 4) = Real.pi / 2 by ring,
    Real.sin_pi_div_two, mul_one]

private theorem inverse_at_image_of_deriv_pos
    {f : ℝ → ℝ} (hpos : ∀ θ, 0 < deriv f θ) {θ y : ℝ} (himage : f θ = y) :
    Function.invFun f y = θ :=
  (congrArg (Function.invFun f) himage.symm).trans
    (Function.leftInverse_invFun (strictMono_of_deriv_pos hpos).injective θ)

private theorem left_rootLabel_deriv_pos
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {base loss : ℕ} {ε : ℝ}
    (hN : N01Properties D T S C base loss ε)
    {z : AnnularState S × ℝ} (hz : z ∈ stateNeighborhood S C base ε)
    (hs : stateSector S z.1) (m : ℕ) (θ : ℝ) :
    0 < deriv (n01RootLabel S C z m false) θ :=
  lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1 / 2)
    (hN.2.2.2.2.2.2.2.1 z hz hs m θ).1

/-- At the displaced test angle the genuine inverse root label returns
the original angle. N01 supplies injectivity on the actual state
neighborhood, so no inverse certificate is added to the hypotheses. -/
theorem n04PositiveGeometry_circleDirection_inverseRootLabel_test
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {base loss : ℕ} {ε : ℝ}
    (hS : IsPhysicalSpaces D T S) (hN : N01Properties D T S C base loss ε)
    (m : ℕ) (a : ℝ)
    (hz : liftSectorParameter S C (a • n04PositiveGeometry_circleDirection hS m, 0) ∈
      stateNeighborhood S C base ε) :
    Function.invFun (n01RootLabel S C
        (liftSectorParameter S C (a • n04PositiveGeometry_circleDirection hS m, 0))
        m false) (Real.pi / 4 + a) = Real.pi / 4 := by
  exact inverse_at_image_of_deriv_pos
    (left_rootLabel_deriv_pos hN hz (hN.2.2.1.liftSectorParameter_sector
      (a • n04PositiveGeometry_circleDirection hS m, 0)) m)
    (n04PositiveGeometry_circleDirection_rootLabel_test hS hN.2.2.1 m a)

private theorem inverse_displacement_abs
    {f : ℝ → ℝ} {θ a : ℝ} (ha : 0 ≤ a)
    (hinverse : Function.invFun f (θ + a) = θ) :
    |Function.invFun f (θ + a) - (θ + a)| = a := by
  rw [hinverse, show θ - (θ + a) = -a by ring, abs_neg, abs_of_nonneg ha]

/-- The inverse angular displacement has exactly the same nonzero
amplitude as the original chart perturbation. -/
theorem n04PositiveGeometry_circleDirection_inverseRootLabel_displacement
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {base loss : ℕ} {ε : ℝ}
    (hS : IsPhysicalSpaces D T S) (hN : N01Properties D T S C base loss ε)
    (m : ℕ) {a : ℝ} (ha : 0 ≤ a)
    (hz : liftSectorParameter S C (a • n04PositiveGeometry_circleDirection hS m, 0) ∈
      stateNeighborhood S C base ε) :
    |Function.invFun (n01RootLabel S C
        (liftSectorParameter S C (a • n04PositiveGeometry_circleDirection hS m, 0))
        m false) (Real.pi / 4 + a) - (Real.pi / 4 + a)| = a := by
  exact inverse_displacement_abs ha
    (n04PositiveGeometry_circleDirection_inverseRootLabel_test hS hN m a hz)

/-- A nonidentity left root label occurs in every positive sector
neighborhood while all nonchart state directions remain zero. -/
theorem n04PositiveGeometry_exists_nontrivial_rootLabel
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} (hS : IsPhysicalSpaces D T S)
    (href : referenceStateConditions D S C) (m b : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∃ a : ℝ, 0 < a ∧ a < 1 ∧
      (a • n04PositiveGeometry_circleDirection hS m, (0 : ℝ)) ∈
        sectorNeighborhood S b ε ε ∧
      n01RootLabel S C
          (liftSectorParameter S C (a • n04PositiveGeometry_circleDirection hS m, 0))
          m false (Real.pi / 4) ≠ Real.pi / 4 := by
  let h := n04PositiveGeometry_circleDirection_small hS m b hε
  refine ⟨h.choose, h.choose_spec.1, h.choose_spec.2.1, h.choose_spec.2.2, ?_⟩
  rw [n04PositiveGeometry_circleDirection_rootLabel_test hS href m h.choose]
  exact ne_of_gt (lt_add_of_pos_right _ h.choose_spec.1)

end ContinuousFlexibility.Analysis
