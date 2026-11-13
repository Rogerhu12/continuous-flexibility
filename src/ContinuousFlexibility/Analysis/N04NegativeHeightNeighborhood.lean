import ContinuousFlexibility.Analysis.N04NegativeHeightCurrentData
import ContinuousFlexibility.Analysis.CanonicalStateInterpolation

/-!
# One uniform neighborhood for normalized negative height factors

The sampled material height absorbs the coefficient envelope at order
zero. Thus a single finite seminorm and a positive radius make an actual
current difference uniformly small on all selected pieces.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set ContinuousFlexibility.Statements CanonicalGeometry

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

theorem n04NegativeHeight_parameterInterpolation
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    (hS : IsPhysicalSpaces D T S) : HasInterpolation (parameterGrading S) := by
  have hr : Monotone realGrading := fun _ _ _ _ => le_rfl
  have hsector : HasInterpolation (sectorGrading S) := by
    obtain ⟨b, l, hb⟩ := coordinate_hasInterpolation_stateGrading hS
    refine ⟨b, l, fun a b c ha hab hbc => ?_⟩
    obtain ⟨A, hA, hbound⟩ := hb a b c ha hab hbc
    exact ⟨A, hA, fun z => hbound z.val⟩
  exact coordinate_hasInterpolation_pair (sectorGrading_monotone S) hr
    hsector coordinate_hasInterpolation_realGrading

variable {S : PhysicalSpacesData} {T : MaterialData} {D : ReferenceData}
  {cell : ℕ → ℕ} {P : ℕ → Prop} {base : ℕ} {ε : ℝ}
  {f : Parameter S → ℕ → PolarPoint → ℝ} {f₀ : ℕ → PolarPoint → ℝ}

/-- The state neighborhood is selected before the piece and spatial point. -/
theorem CurrentJetDataOn.height_small_difference
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T)
    (hε : 0 < ε) (hE : ∀ m, 1 ≤ T.E0 (T.sample (cell m)))
    (h : CurrentJetDataOn S T cell P base ε f f₀)
    {δ : ℝ} (hδ : 0 < δ) :
    ∃ b' : ℕ, ∃ ε' : ℝ, base ≤ b' ∧ 0 < ε' ∧ ε' ≤ ε ∧
      CurrentJetDataOn S T cell P b' ε' f f₀ ∧
        ∀ z ∈ sectorNeighborhood S b' ε' ε', ∀ m, P m → ∀ q ∈ unitStrip,
          |f z m q - f₀ m q| ≤ δ := by
  have hv := h.2.choose_spec.1
  obtain ⟨B, hB, hbound⟩ := hv.choose_spec 0
  obtain ⟨C, hC, hsample⟩ := material_sample_height_coefficient_power_bounded
    hD hT cell B (by norm_num : (0 : ℝ) < 3 / 4)
  let b' : ℕ := max base hv.choose
  let ε' : ℝ := min ε (δ / (2 * (B * C)))
  have hb : base ≤ b' := le_max_left _ _
  have hBC : 0 < B * C := mul_pos hB hC
  have hden : 0 < 2 * (B * C) := mul_pos (by norm_num) hBC
  have he : 0 < ε' := lt_min hε (div_pos hδ hden)
  have hele : ε' ≤ ε := min_le_left _ _
  have hH (m : ℕ) : 0 ≤ T.H (T.sample (cell m)) :=
    (hT.2.1 _ (materialSample_mem_interval hD hT (cell m))).2.1.le
  have hsub : sectorNeighborhood S b' ε' ε' ⊆ sectorNeighborhood S base ε ε :=
    sectorNeighborhood_mono S hb hele hele
  refine ⟨b', ε', hb, he, hele, h.mono (fun _ hm => hm) hb hele
    (fun m => zero_le_one.trans (hE m)) hH, ?_⟩
  intro z hz m hm q hq
  have hgrade : parameterGrading S hv.choose z ≤ 2 * ε' := by
    have hmono := tamePairGrading_monotone (sectorGrading_monotone S)
      (fun _ _ _ => le_rfl : Monotone realGrading)
    apply (hmono (le_max_right base hv.choose) z).trans
    change sectorGrading S b' z.1 + ‖z.2‖ ≤ 2 * ε'
    rw [Real.norm_eq_abs]
    linarith [hz.1, hz.2]
  have hcost : B * T.E0 (T.sample (cell m)) ^ B *
      T.H (T.sample (cell m)) ^ (3 / 4 : ℝ) ≤ B * C := by
    calc
      _ = B * (T.H (T.sample (cell m)) ^ (3 / 4 : ℝ) *
        T.E0 (T.sample (cell m)) ^ B) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (hsample m) hB.le
  have hv' := hbound z (hsub hz) m hm ⟨q, hq⟩ 0 0 (by omega)
  simp only [mixedDerivative, iteratedDeriv_zero, zero_add] at hv'
  calc
    _ ≤ B * T.E0 (T.sample (cell m)) ^ B * T.H (T.sample (cell m)) ^ (3 / 4 : ℝ) *
        parameterGrading S hv.choose z := hv'
    _ ≤ (B * C) * (2 * ε') :=
      mul_le_mul hcost hgrade (apply_nonneg _ _) hBC.le
    _ = (2 * (B * C)) * ε' := by ring
    _ ≤ (2 * (B * C)) * (δ / (2 * (B * C))) :=
      mul_le_mul_of_nonneg_left (min_le_right ε _) hden.le
    _ = δ := mul_div_cancel₀ δ hden.ne'

/-- A normalized field with reference value one has one fixed compact
range on a smaller neighborhood. -/
theorem CurrentJetDataOn.height_range_one
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T)
    (hε : 0 < ε) (hE : ∀ m, 1 ≤ T.E0 (T.sample (cell m)))
    (h : CurrentJetDataOn S T cell P base ε f f₀)
    (h₀ : ∀ m, P m → ∀ q ∈ unitStrip, f₀ m q = 1) :
    ∃ b' : ℕ, ∃ ε' : ℝ, base ≤ b' ∧ 0 < ε' ∧ ε' ≤ ε ∧
      CurrentJetDataOn S T cell P b' ε' f f₀ ∧
        ∀ z ∈ sectorNeighborhood S b' ε' ε', ∀ m, P m → ∀ q ∈ unitStrip,
          f z m q ∈ Icc (1 / 2 : ℝ) (3 / 2 : ℝ) := by
  obtain ⟨b', ε', hb, he, hele, hdata, hsmall⟩ :=
    h.height_small_difference hD hT hε hE (by norm_num : (0 : ℝ) < 1 / 2)
  refine ⟨b', ε', hb, he, hele, hdata, fun z hz m hm q hq => ?_⟩
  have hs := hsmall z hz m hm q hq
  rw [h₀ m hm q hq, abs_le] at hs
  exact ⟨by linarith [hs.1], by linarith [hs.2]⟩

end ContinuousFlexibility.Analysis
