import ContinuousFlexibility.Analysis.N04NegativeHeightCurrentData
import ContinuousFlexibility.Analysis.N04NegativeHeightParameterInterpolation

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

/-- The real coordinate is the only norm conversion needed in the
sector bound. Keep the state seminorm opaque throughout the conversion. -/
private theorem height_parameterGrading_apply (S : PhysicalSpacesData)
    (n : ℕ) (z : Parameter S) :
    parameterGrading S n z = sectorGrading S n z.1 + |z.2| :=
  (pairGrading_apply (sectorGrading S) realGrading n z).trans
    (congrArg (fun t : ℝ => sectorGrading S n z.1 + t)
      ((congrFun (coe_normSeminorm ℝ ℝ) z.2).trans (Real.norm_eq_abs z.2)))

private theorem height_parameterGrading_le_radius
    {S : PhysicalSpacesData} {low high : ℕ} {ε : ℝ} {z : Parameter S}
    (horder : low ≤ high) (hz : z ∈ sectorNeighborhood S high ε ε) :
    parameterGrading S low z ≤ 2 * ε :=
  (sectorPairGrading_monotone S horder z).trans
    ((height_parameterGrading_apply S high z).trans_le
      ((add_le_add hz.1.le hz.2.le).trans_eq (two_mul ε).symm))

/-- Reading the zeroth mixed derivative does not simplify the full
state grading or its selected derivative tower. -/
private theorem height_zero_order_value (p : ℕ → ℝ) (loss : ℕ)
    (B : ℝ) (f : PolarPoint → ℝ) (q : PolarPoint)
    (h : |mixedDerivative 0 0 f q| ≤ B * p (0 + loss)) :
    |f q| ≤ B * p loss :=
  ((congrArg abs (congrFun (spaces_mixedDerivative_zero f) q)).symm.trans_le h).trans_eq
    (congrArg (fun n => B * p n) (Nat.zero_add loss))

private theorem height_sampleCost_reorder (B E H : ℝ) :
    B * E * H = B * (H * E) := by ring

private theorem height_small_radius_bound {K ε δ : ℝ}
    (hK : 0 < K) (hε : ε ≤ δ / (2 * K)) : K * (2 * ε) ≤ δ := by
  have hden : 0 < 2 * K := mul_pos (by norm_num) hK
  calc
    _ = (2 * K) * ε := by ring
    _ ≤ (2 * K) * (δ / (2 * K)) := mul_le_mul_of_nonneg_left hε hden.le
    _ = δ := mul_div_cancel₀ δ hden.ne'

private theorem height_range_one_scalar {x y : ℝ} (hy : y = 1)
    (h : |x - y| ≤ (1 / 2 : ℝ)) : x ∈ Icc (1 / 2 : ℝ) (3 / 2 : ℝ) := by
  rw [hy, abs_le] at h
  exact ⟨by linarith only [h.1], by linarith only [h.2]⟩

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
  have hvalue := h.2.choose_spec.1
  let loss : ℕ := hvalue.choose
  have hzero := hvalue.choose_spec 0
  let B : ℝ := hzero.choose
  have hB : 0 < B := hzero.choose_spec.1
  have hbound := hzero.choose_spec.2
  have hmaterial := material_sample_height_coefficient_power_bounded
    hD hT cell B (by norm_num : (0 : ℝ) < 3 / 4)
  let C : ℝ := hmaterial.choose
  have hC : 0 < C := hmaterial.choose_spec.1
  have hsample := hmaterial.choose_spec.2
  let b' : ℕ := max base loss
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
  have hgrade : parameterGrading S loss z ≤ 2 * ε' :=
    height_parameterGrading_le_radius (le_max_right base loss) hz
  have hcost : B * T.E0 (T.sample (cell m)) ^ B *
      T.H (T.sample (cell m)) ^ (3 / 4 : ℝ) ≤ B * C :=
    (height_sampleCost_reorder B (T.E0 (T.sample (cell m)) ^ B)
      (T.H (T.sample (cell m)) ^ (3 / 4 : ℝ))).trans_le
        (mul_le_mul_of_nonneg_left (hsample m) hB.le)
  have hv' := height_zero_order_value (fun n => parameterGrading S n z) loss
    (B * T.E0 (T.sample (cell m)) ^ B * T.H (T.sample (cell m)) ^ (3 / 4 : ℝ))
    (fun y => f z m y - f₀ m y) q (hbound z (hsub hz) m hm ⟨q, hq⟩ 0 0 le_rfl)
  calc
    _ ≤ B * T.E0 (T.sample (cell m)) ^ B * T.H (T.sample (cell m)) ^ (3 / 4 : ℝ) *
        parameterGrading S loss z := hv'
    _ ≤ (B * C) * (2 * ε') :=
      mul_le_mul hcost hgrade (apply_nonneg _ _) hBC.le
    _ ≤ δ := height_small_radius_bound hBC (min_le_right ε _)

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
  have hsmall := CurrentJetDataOn.height_small_difference
    (S := S) (T := T) (cell := cell) (P := P) (base := base) (ε := ε)
    (f := f) (f₀ := f₀) hD hT hε hE h (by norm_num : (0 : ℝ) < 1 / 2)
  let b' : ℕ := hsmall.choose
  let ε' : ℝ := hsmall.choose_spec.choose
  have hd := hsmall.choose_spec.choose_spec
  exact ⟨b', ε', hd.1, hd.2.1, hd.2.2.1, hd.2.2.2.1,
    fun z hz m hm q hq =>
      height_range_one_scalar (h₀ m hm q hq) (hd.2.2.2.2 z hz m hm q hq)⟩

end ContinuousFlexibility.Analysis
