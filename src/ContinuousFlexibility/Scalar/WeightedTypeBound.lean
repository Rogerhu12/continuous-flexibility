import ContinuousFlexibility.Scalar.WeightedGeometry

/-!
# The weighted type coefficient is uniformly bounded on the common ball

The type coefficient itself may grow at the flat endpoints.  Its product
with the actual perturbed profile is controlled by the quantitative lower
bound for `Q` and the positive inner radius.  The bound is valid on every
smaller ball or every higher input order for which the same geometry holds.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open Set

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}

theorem weighted_typeCoefficient_bound {a r w Q E : ℝ}
    (ha : 0 < a) (har : a ≤ r) (hw : 0 < w)
    (hQ : (7 / 8 : ℝ) * w ≤ Q) (hE : 1 + w ^ 2 ≤ E) :
    |w * ((1 + w ^ 2) / (r * Q))| ≤ (8 / (7 * a)) * E := by
  have hr : 0 < r := ha.trans_le har
  have hQpos : 0 < Q := lt_of_lt_of_le (mul_pos (by norm_num) hw) hQ
  have hratio : w / Q ≤ (8 / 7 : ℝ) := by
    apply (div_le_iff₀ hQpos).mpr
    nlinarith only [hQ]
  have hinverse : (1 : ℝ) / r ≤ 1 / a :=
    div_le_div_of_nonneg_left zero_le_one ha har
  have hfactor : 0 ≤ (8 / 7 : ℝ) * (1 / a) :=
    mul_nonneg (by norm_num) (div_nonneg zero_le_one ha.le)
  rw [abs_of_nonneg (mul_nonneg hw.le
    (div_nonneg (by positivity) (mul_nonneg hr.le hQpos.le)))]
  calc
    _ = (w / Q) * (1 / r) * (1 + w ^ 2) := by
      field_simp [hr.ne', hQpos.ne']
      <;> ring
    _ ≤ ((8 / 7 : ℝ) * (1 / a)) * E :=
      mul_le_mul (mul_le_mul hratio hinverse (div_nonneg zero_le_one hr.le) (by norm_num))
        hE (by positivity) hfactor
    _ = (8 / (7 * a)) * E := by
      field_simp [ha.ne']
      <;> ring

theorem scalarStateProfile_mul_typeB_le
    (hD : IsAccumulatingProfile D) {x : ScalarWeightedState S}
    (hg : ScalarStateGeometry D S x) {p : PolarPoint} (hp : p ∈ annularOpen D)
    {E : ℝ} (hE : 1 + scalarStateProfile D S x p.1 ^ 2 ≤ E) :
    |scalarStateProfile D S x p.1 * scalarStateTypeB D S x p| ≤
      (8 / (7 * D.a)) * E := by
  obtain ⟨_, _, _, _, _, _, _, _, _, hpositive⟩ := hg
  have hw := (hpositive p.1 hp.1).1
  have hQ := ((hpositive p.1 hp.1).2 p.2).2
  exact weighted_typeCoefficient_bound hD.choose_spec.1.1 hp.1.1.le hw hQ hE

/-- A uniform upper bound for the whole perturbed profile requires only a
bounded low-order ball.  Geometry supplies its positivity separately. -/
theorem scalarStateProfile_uniform_bound_on_ball
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T)
    (hS : IsPhysicalSpaces D T S) (v₀ : ScalarHeightSpace S)
    {base : ℕ} {ε : ℝ} (hbase : 4 ≤ base) (hε : ε ≤ 1) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ x ∈ scalarStateBall S v₀ base ε,
      ∀ r ∈ Ioo D.a D.b, |scalarStateProfile D S x r| ≤ M := by
  obtain ⟨M, hM, hMbound⟩ := referenceProfile_uniform_upper_bound hD
  obtain ⟨Cm, Cr, Ct, Ctt, hCm, _, _, _, hmean, _, _, _⟩ :=
    scalarHeight_low_jet_bounds hD hT hS
  refine ⟨(1 + Cm) * M, mul_nonneg (by linarith only [hCm]) hM, ?_⟩
  intro x hx r hr
  have hp : scalarHeightGrading S 4 x.1.1.1 ≤ 1 :=
    (scalarHeightGrading_monotone S hbase x.1.1.1).trans
      ((scalarStateBall_coordinate_bounds hx).1.le.trans hε)
  have hm : |angularMean (fun θ => (S.height scalarBeta).decode x.1.1.1 (r, θ))| ≤ Cm := by
    calc
      _ ≤ Cm * scalarHeightGrading S 4 x.1.1.1 := hmean _ _ hr
      _ ≤ Cm * 1 := mul_le_mul_of_nonneg_left hp hCm
      _ = Cm := mul_one _
  have hmadd :
      |1 + angularMean (fun θ => (S.height scalarBeta).decode x.1.1.1 (r, θ))| ≤ 1 + Cm := by
    calc
      _ ≤ |(1 : ℝ)| + |angularMean (fun θ => (S.height scalarBeta).decode x.1.1.1 (r, θ))| :=
        abs_add _ _
      _ ≤ 1 + Cm := by simpa only [abs_one] using add_le_add_left hm 1
  have hw : 0 < D.w r := hD.choose_spec.1.2.2.2.2.1 r hr
  rw [scalarStateProfile, abs_mul, abs_of_pos hw]
  calc
    _ ≤ D.w r * (1 + Cm) := mul_le_mul_of_nonneg_left hmadd hw.le
    _ ≤ M * (1 + Cm) :=
      mul_le_mul_of_nonneg_right (hMbound r hr) (by linarith only [hCm])
    _ = (1 + Cm) * M := mul_comm _ _

/-- This is the exact bounded-type clause in `IsWeightedS05`, on any common
state ball carrying the physical geometry. -/
theorem scalarStateTypeB_uniform_bound
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T)
    (hS : IsPhysicalSpaces D T S) (v₀ : ScalarHeightSpace S)
    {base : ℕ} {ε : ℝ} (hbase : 4 ≤ base) (hε : ε ≤ 1)
    (hg : ∀ x ∈ scalarStateBall S v₀ base ε, ScalarStateGeometry D S x) :
    ∃ C : ℝ, 0 < C ∧ ∀ x ∈ scalarStateBall S v₀ base ε,
      ∀ r ∈ Ioo D.a D.b, ∀ θ,
        |scalarStateProfile D S x r * scalarStateTypeB D S x (r, θ)| ≤ C := by
  obtain ⟨M, hM, hMbound⟩ := scalarStateProfile_uniform_bound_on_ball hD hT hS v₀ hbase hε
  have ha : 0 < D.a := hD.choose_spec.1.1
  refine ⟨(8 / (7 * D.a)) * (1 + M ^ 2), by positivity, ?_⟩
  intro x hx r hr θ
  have hwbound := abs_le.mp (hMbound x hx r hr)
  have hproduct : 0 ≤ (M - scalarStateProfile D S x r) * (M + scalarStateProfile D S x r) :=
    mul_nonneg (by linarith only [hwbound.2]) (by linarith only [hwbound.1])
  have hE : 1 + scalarStateProfile D S x r ^ 2 ≤ 1 + M ^ 2 := by
    nlinarith only [hproduct]
  exact scalarStateProfile_mul_typeB_le hD (hg x hx) ⟨hr, mem_univ _⟩ hE

theorem exists_scalarStateBall_geometry_and_typeB
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T)
    (hS : IsPhysicalSpaces D T S) (v₀ : ScalarHeightSpace S) :
    ∃ ε : ℝ, 0 < ε ∧ ε < 1 ∧
      (∀ x ∈ scalarStateBall S v₀ 4 ε, ScalarStateGeometry D S x) ∧
      ∃ C : ℝ, 0 < C ∧ ∀ x ∈ scalarStateBall S v₀ 4 ε,
        ∀ r ∈ Ioo D.a D.b, ∀ θ,
          |scalarStateProfile D S x r * scalarStateTypeB D S x (r, θ)| ≤ C := by
  obtain ⟨ε, hε, hεone, hg⟩ := exists_scalarStateBall_geometry hD hT hS v₀
  exact ⟨ε, hε, hεone, hg,
    scalarStateTypeB_uniform_bound hD hT hS v₀ le_rfl hεone.le hg⟩

end ContinuousFlexibility.Statements
