import ContinuousFlexibility.Analysis.N04RealizationLeadCurrentData
import ContinuousFlexibility.Analysis.N07aForwardCoefficients
import ContinuousFlexibility.Analysis.SectorParameterGeometry

/-!
# A uniform reciprocal bound from the source difference estimate

Only the value estimate at spatial order zero is used to select the
neighborhood.  Consequently its base and radius are independent of all
later spatial and parameter orders.  The material height absorbs the
fixed coefficient power before the neighborhood is selected.
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

/-- The sum grading on a rectangular sector neighborhood. -/
theorem n04SourceColumns_parameter_lt {S : PhysicalSpacesData} {b : ℕ} {ε : ℝ}
    {z : Parameter S} (hz : z ∈ sectorNeighborhood S b ε ε) :
    parameterGrading S b z < 2 * ε := by
  have heq : parameterGrading S b z = sectorGrading S b z.1 + |z.2| :=
    pairGrading_apply (E := StateDirections S) (F := ℝ)
      (sectorGrading S) realGrading b z
  rw [heq]
  linarith only [hz.1, hz.2]

/-- A relative error smaller than one half gives a genuine inverse bound. -/
theorem n04SourceColumns_half_reference_of_relative_error
    {a a₀ d r : ℝ} (ha₀ : 0 < a₀) (hi : a₀⁻¹ ≤ r)
    (hd : |a - a₀| ≤ d) (hsmall : d * r < 1 / 2) :
    a₀ / 2 ≤ a ∧ 0 < a ∧ a⁻¹ ≤ 2 * r := by
  have hd0 : 0 ≤ d := (abs_nonneg _).trans hd
  have hb : |a - a₀| * a₀⁻¹ < 1 / 2 :=
    (mul_le_mul hd hi (inv_pos.mpr ha₀).le hd0).trans_lt hsmall
  have hdiv : |a - a₀| / a₀ < 1 / 2 := by
    simpa only [div_eq_mul_inv] using hb
  have herr : |a - a₀| < a₀ / 2 := by
    have h := (div_lt_iff₀ ha₀).mp hdiv
    linarith
  have ha : a₀ / 2 ≤ a := by
    have h := (abs_lt.mp herr).1
    linarith
  refine ⟨ha, (half_pos ha₀).trans_le ha, ?_⟩
  calc
    a⁻¹ ≤ (a₀ / 2)⁻¹ := inv_anti₀ (half_pos ha₀) ha
    _ = 2 * a₀⁻¹ := by simp only [div_eq_mul_inv, mul_inv_rev, inv_inv]
    _ ≤ 2 * r := mul_le_mul_of_nonneg_left hi (by norm_num)

/-- A positive reference family with a material reciprocal bound stays
uniformly comparable to that reference on one smaller neighborhood. -/
theorem CurrentJetDataOn.sourceColumns_half_reference
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {cell : ℕ → ℕ} {base : ℕ} {ε : ℝ}
    {f : Parameter S → ℕ → PolarPoint → ℝ} {f₀ : ℕ → PolarPoint → ℝ}
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T)
    (hf : CurrentJetDataOn S T cell (fun _ => True) base ε f f₀)
    (hε : 0 < ε) (hpos : ∀ m q, q ∈ unitStrip → 0 < f₀ m q)
    (hinv : ∃ A : ℝ, 0 < A ∧ ∀ m q, q ∈ unitStrip →
      (f₀ m q)⁻¹ ≤ A * T.E0 (T.sample (cell m)) ^ A) :
    ∃ base' : ℕ, ∃ ε' A : ℝ, base ≤ base' ∧ 0 < ε' ∧ ε' ≤ ε ∧ 0 < A ∧
      ∀ z ∈ sectorNeighborhood S base' ε' ε', ∀ m q, q ∈ unitStrip →
        f₀ m q / 2 ≤ f z m q ∧ 0 < f z m q ∧
          (f z m q)⁻¹ ≤ 2 * A * T.E0 (T.sample (cell m)) ^ A := by
  have hv := hf.2.choose_spec.1
  let loss : ℕ := hv.choose
  have hv0 := hv.choose_spec 0
  let B : ℝ := hv0.choose
  have hB : 0 < B := hv0.choose_spec.1
  let A : ℝ := hinv.choose
  have hA : 0 < A := hinv.choose_spec.1
  have henv := n07a_materialSample_envelope_bound hD hT
    (by norm_num : 0 < (3 / 4 : ℝ)) (B + A)
  let N : ℝ := henv.choose
  have hN : 0 < N := henv.choose_spec.1
  let Q : ℝ := B * A * N
  have hQ : 0 < Q := mul_pos (mul_pos hB hA) hN
  let base' : ℕ := max base loss
  let δ : ℝ := (4 * Q)⁻¹
  have hδ : 0 < δ := inv_pos.mpr (mul_pos (by norm_num) hQ)
  let ε' : ℝ := min ε δ
  have hε' : 0 < ε' := lt_min hε hδ
  have hε'ε : ε' ≤ ε := min_le_left _ _
  have hε'δ : ε' ≤ δ := min_le_right _ _
  have hpmono : Monotone (parameterGrading S) :=
    tamePairGrading_monotone (sectorGrading_monotone S) (fun _ _ _ => le_rfl)
  refine ⟨base', ε', A, le_max_left _ _, hε', hε'ε, hA, ?_⟩
  intro z hz m q hq
  have hzU : z ∈ sectorNeighborhood S base ε ε :=
    sectorNeighborhood_mono S (le_max_left _ _) hε'ε hε'ε hz
  have hp : parameterGrading S base' z < 2 * ε' := n04SourceColumns_parameter_lt hz
  have hloss : parameterGrading S loss z ≤ parameterGrading S base' z :=
    hpmono (le_max_right _ _) z
  let M : ℝ := B * T.E0 (T.sample (cell m)) ^ B *
    T.H (T.sample (cell m)) ^ (3 / 4 : ℝ)
  have hsamp := hT.2.1 _
    (materialSample_mem_radialCore hT hD.choose_spec.2.1 (cell m))
  have hM : 0 ≤ M := mul_nonneg
    (mul_nonneg hB.le (Real.rpow_nonneg hsamp.2.2.1.le _))
    (Real.rpow_nonneg hsamp.2.1.le _)
  have hdiff : |f z m q - f₀ m q| ≤ M * parameterGrading S base' z := by
    have h := hv0.choose_spec.2 z hzU m trivial (⟨q, hq⟩ : unitStrip) 0 0 le_rfl
    have h' : |f z m q - f₀ m q| ≤ M * parameterGrading S loss z := by
      simp only [spaces_mixedDerivative_zero, Nat.zero_add] at h
      exact h
    exact h'.trans (mul_le_mul_of_nonneg_left hloss hM)
  have hprod : M * (A * T.E0 (T.sample (cell m)) ^ A) ≤ Q := by
    calc
      _ = B * A * (T.H (T.sample (cell m)) ^ (3 / 4 : ℝ) *
          T.E0 (T.sample (cell m)) ^ (B + A)) := by
        dsimp only [M]
        rw [Real.rpow_add hsamp.2.2.1 B A]
        ring
      _ ≤ B * A * N := mul_le_mul_of_nonneg_left
        (henv.choose_spec.2 (cell m)) (mul_nonneg hB.le hA.le)
      _ = Q := rfl
  have hsmall : (M * parameterGrading S base' z) *
      (A * T.E0 (T.sample (cell m)) ^ A) < 1 / 2 := by
    calc
      _ = (M * (A * T.E0 (T.sample (cell m)) ^ A)) *
          parameterGrading S base' z := by ring
      _ ≤ Q * parameterGrading S base' z :=
        mul_le_mul_of_nonneg_right hprod (apply_nonneg _ _)
      _ < Q * (2 * ε') := mul_lt_mul_of_pos_left hp hQ
      _ ≤ Q * (2 * δ) := mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left hε'δ (by norm_num)) hQ.le
      _ = 1 / 2 := by dsimp only [δ]; field_simp [hQ.ne']; ring
  have hh := n04SourceColumns_half_reference_of_relative_error
    (hpos m q hq) (hinv.choose_spec.2 m q hq) hdiff hsmall
  exact ⟨hh.1, hh.2.1, by simpa only [mul_assoc] using hh.2.2⟩

end ContinuousFlexibility.Analysis
