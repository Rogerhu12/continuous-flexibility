import ContinuousFlexibility.Analysis.N04RealizationLeadCurrentData
import ContinuousFlexibility.Analysis.N07aCurrentPrincipalBounds
import ContinuousFlexibility.Analysis.SectorParameterGeometry

/-!
# A reciprocal neighborhood chosen from the value difference

The order-zero value estimate and the reference reciprocal envelope
choose the neighborhood once. The material sample envelope absorbs the
product of their polynomial costs, before any higher order is selected.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set ContinuousFlexibility.Statements CanonicalGeometry

theorem n04PrincipalNegative_inverse_of_relative_error
    {a a₀ d r : ℝ} (ha₀ : a₀ ≠ 0) (hi : |a₀⁻¹| ≤ r)
    (hd : |a - a₀| ≤ d) (hsmall : d * r < 1 / 2) :
    |a₀| / 2 ≤ |a| ∧ a ≠ 0 ∧ |a⁻¹| ≤ 2 * r := by
  have ha₀pos : 0 < |a₀| := abs_pos.mpr ha₀
  have hi' : |a₀|⁻¹ ≤ r := by simpa only [abs_inv] using hi
  have hd0 : 0 ≤ d := (abs_nonneg _).trans hd
  have hb : |a - a₀| * |a₀|⁻¹ < 1 / 2 :=
    (mul_le_mul hd hi' (inv_pos.mpr ha₀pos).le hd0).trans_lt hsmall
  have hdiv : |a - a₀| / |a₀| < 1 / 2 := by
    simpa only [div_eq_mul_inv] using hb
  have herr : |a - a₀| < |a₀| / 2 := by
    have hh := (div_lt_iff₀ ha₀pos).mp hdiv
    linarith
  have htri : |a₀| ≤ |a - a₀| + |a| := by
    have hh := abs_add_le (a₀ - a) a
    rw [sub_add_cancel, abs_sub_comm] at hh
    exact hh
  have ha : |a₀| / 2 ≤ |a| := by linarith
  refine ⟨ha, abs_pos.mp ((half_pos ha₀pos).trans_le ha), ?_⟩
  calc
    |a⁻¹| = |a|⁻¹ := abs_inv _
    _ ≤ (|a₀| / 2)⁻¹ := inv_anti₀ (half_pos ha₀pos) ha
    _ = 2 * |a₀|⁻¹ := by simp only [div_eq_mul_inv, mul_inv_rev, inv_inv]
    _ ≤ 2 * r := mul_le_mul_of_nonneg_left hi' (by norm_num)

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

/-- One value estimate produces a common nonvanishing neighborhood and
a uniform reciprocal envelope, independent of subsequent jet orders. -/
theorem CurrentJetDataOn.n04PrincipalNegative_inverse_neighborhood
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {cell : ℕ → ℕ} {P : ℕ → Prop} {base : ℕ} {ε : ℝ}
    {f : Parameter S → ℕ → PolarPoint → ℝ} {f₀ : ℕ → PolarPoint → ℝ}
    (h : CurrentJetDataOn S T cell P base ε f f₀)
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T)
    (hE : ∀ m, 1 ≤ T.E0 (T.sample (cell m))) (hε : 0 < ε)
    (href : ∃ R : ℝ, 0 < R ∧ ∀ m, P m → ∀ q ∈ unitStrip,
      f₀ m q ≠ 0 ∧ |(f₀ m q)⁻¹| ≤ R * T.E0 (T.sample (cell m)) ^ R) :
    ∃ base' : ℕ, base ≤ base' ∧ ∃ ε' : ℝ, 0 < ε' ∧ ε' ≤ ε ∧ ε' ≤ 1 / 2 ∧
      ∃ B : ℝ, 0 < B ∧ ∀ z ∈ sectorNeighborhood S base' ε' ε',
        ∀ m, P m → ∀ q ∈ unitStrip,
          |f₀ m q| / 2 ≤ |f z m q| ∧ f z m q ≠ 0 ∧
            |(f z m q)⁻¹| ≤ B * T.E0 (T.sample (cell m)) ^ B := by
  have hvalue := h.2.choose_spec.1
  let loss : ℕ := hvalue.choose
  have hv := hvalue.choose_spec 0
  let C : ℝ := hv.choose
  have hC : 0 < C := hv.choose_spec.1
  let R : ℝ := href.choose
  have hR : 0 < R := href.choose_spec.1
  have henv := n07a_materialSample_envelope_bound hD hT
    (by norm_num : 0 < (3 / 4 : ℝ)) (C + R)
  let N : ℝ := henv.choose
  have hN : 0 < N := henv.choose_spec.1
  let Q : ℝ := C * R * N
  have hQ : 0 < Q := mul_pos (mul_pos hC hR) hN
  let base' : ℕ := max base loss
  let δ : ℝ := (4 * Q)⁻¹
  have hδ : 0 < δ := inv_pos.mpr (mul_pos (by norm_num) hQ)
  let ε' : ℝ := min ε (min (1 / 2) δ)
  have hε' : 0 < ε' := lt_min hε (lt_min (by norm_num) hδ)
  have hε'ε : ε' ≤ ε := min_le_left _ _
  have hε'half : ε' ≤ 1 / 2 := (min_le_right _ _).trans (min_le_left _ _)
  have hε'δ : ε' ≤ δ := (min_le_right _ _).trans (min_le_right _ _)
  let B : ℝ := 2 * R + 1
  have hB : 0 < B := by dsimp only [B]; linarith
  have hRB : R ≤ B := by dsimp only [B]; linarith
  have h2RB : 2 * R ≤ B := by dsimp only [B]; linarith
  have hmono : Monotone (parameterGrading S) := n07aParameterGrading_monotone S
  refine ⟨base', le_max_left _ _, ε', hε', hε'ε, hε'half, B, hB, ?_⟩
  intro z hz m hm q hq
  have hzU : z ∈ sectorNeighborhood S base ε ε :=
    sectorNeighborhood_mono S (le_max_left _ _) hε'ε hε'ε hz
  have hp : parameterGrading S base' z < 2 * ε' := by
    rw [show parameterGrading S base' z = sectorGrading S base' z.1 + |z.2| from
      pairGrading_apply (E := StateDirections S) (F := ℝ)
        (sectorGrading S) realGrading base' z]
    linarith only [hz.1, hz.2]
  have hsmall : parameterGrading S loss z < (2 * Q)⁻¹ := by
    calc
      _ ≤ parameterGrading S base' z := hmono (le_max_right _ _) z
      _ < 2 * ε' := hp
      _ ≤ 2 * δ := mul_le_mul_of_nonneg_left hε'δ (by norm_num)
      _ = (2 * Q)⁻¹ := by dsimp only [δ]; field_simp [hQ.ne']; ring
  have hepos : 0 < T.E0 (T.sample (cell m)) := zero_lt_one.trans_le (hE m)
  let M : ℝ := C * T.E0 (T.sample (cell m)) ^ C *
    T.H (T.sample (cell m)) ^ (3 / 4 : ℝ)
  let r : ℝ := R * T.E0 (T.sample (cell m)) ^ R
  have hprod : M * r ≤ Q := by
    calc
      _ = C * R * (T.H (T.sample (cell m)) ^ (3 / 4 : ℝ) *
          T.E0 (T.sample (cell m)) ^ (C + R)) := by
        dsimp only [M, r]
        rw [Real.rpow_add hepos]
        ring
      _ ≤ C * R * N := mul_le_mul_of_nonneg_left (henv.choose_spec.2 (cell m))
        (mul_nonneg hC.le hR.le)
      _ = Q := rfl
  have hdiff : |f z m q - f₀ m q| ≤ M * parameterGrading S loss z := by
    have hh := hv.choose_spec.2 z hzU m hm ⟨q, hq⟩ 0 0 (by omega)
    simp only [spaces_mixedDerivative_zero, Nat.zero_add] at hh
    exact hh
  have hrelative : (M * parameterGrading S loss z) * r < 1 / 2 := by
    calc
      _ = (M * r) * parameterGrading S loss z := by ring
      _ ≤ Q * parameterGrading S loss z :=
        mul_le_mul_of_nonneg_right hprod (apply_nonneg _ _)
      _ < Q * (2 * Q)⁻¹ := mul_lt_mul_of_pos_left hsmall hQ
      _ = 1 / 2 := by field_simp [hQ.ne']
  have hh := n04PrincipalNegative_inverse_of_relative_error
    (href.choose_spec.2 m hm q hq).1 (href.choose_spec.2 m hm q hq).2 hdiff hrelative
  refine ⟨hh.1, hh.2.1, hh.2.2.trans ?_⟩
  have hcoef : (2 * R) * T.E0 (T.sample (cell m)) ^ R ≤
      B * T.E0 (T.sample (cell m)) ^ B := mul_le_mul h2RB
    (Real.rpow_le_rpow_of_exponent_le (hE m) hRB)
    (Real.rpow_nonneg hepos.le _) hB.le
  simpa only [r, mul_assoc] using hcoef

end ContinuousFlexibility.Analysis
