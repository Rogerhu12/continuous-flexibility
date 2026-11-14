module

public import ContinuousFlexibility.Analysis.N04SourceColumnsFullProductBounds
public import ContinuousFlexibility.Analysis.N04SourceColumnsReferenceProduct
public import ContinuousFlexibility.Analysis.N04SourceColumnsCollector
public import ContinuousFlexibility.Analysis.N04SourceColumnsLinear
public import ContinuousFlexibility.Analysis.N07aInverseChartDisplacement

/-!
# Multiplication in the current source interface

The parameter neighborhood is shrunk once to the fixed interpolation
base. The full current product has the correct height gain at every
positive parameter order. Its first derivative then recovers the exact
reference difference, including the vanishing value estimate.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set ContinuousFlexibility.Statements CanonicalGeometry
open scoped ContDiff BigOperators

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

/-- Specialize the height weight without simplifying any chosen
coefficient or loss in a full-family estimate. -/
private theorem n04SourceColumns_positiveHeight_elim
    {k : ℕ} (hk : 0 < k) {A H W x : ℝ}
    (h : x ≤ A * parameterHeightWeight H k * W) :
    x ≤ A * H * W := by
  simpa only [parameterHeightWeight, if_neg (Nat.ne_of_gt hk)] using h

variable {D : ReferenceData} {S : PhysicalSpacesData} {T : MaterialData} {cell : ℕ → ℕ}
  {base : ℕ} {ε : ℝ}
  {f g : Parameter S → ℕ → PolarPoint → ℝ} {f₀ g₀ : ℕ → PolarPoint → ℝ}

/-- Scalar multiplication of two interface families. Neither the loss
nor the new neighborhood depends on a piece or on a derivative order. -/
theorem CurrentJetDataOn.sourceColumns_mul
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T) (hε : 0 < ε)
    (hE : ∀ m, 1 ≤ T.E0 (T.sample (cell m)))
    (hI : HasInterpolation (parameterGrading S))
    (hf : CurrentJetDataOn S T cell (fun _ => True) base ε f f₀)
    (hg : CurrentJetDataOn S T cell (fun _ => True) base ε g g₀)
    (hf₀ : N04SourceReferenceData T cell f₀) (hg₀ : N04SourceReferenceData T cell g₀) :
    ∃ (base' : ℕ) (ε' : ℝ), base ≤ base' ∧ 0 < ε' ∧ ε' ≤ ε ∧
      CurrentJetDataOn S T cell (fun _ => True) base' ε'
        (fun z m q => f z m q * g z m q) (fun m q => f₀ m q * g₀ m q) := by
  let U := sectorNeighborhood S base ε ε
  have hU : IsOpen U := isOpen_sectorNeighborhood S base ε ε
  have hΩ : IsOpen unitStrip := isOpen_Ioo.prod isOpen_univ
  have hp : Monotone (parameterGrading S) :=
    tamePairGrading_monotone (sectorGrading_monotone S) (fun _ _ _ => le_rfl)
  let E : ℕ → ℝ := fun m => T.E0 (T.sample (cell m))
  let H : ℕ → ℝ := fun m => T.H (T.sample (cell m)) ^ (3 / 4 : ℝ)
  have hH₀ (m : ℕ) : 0 ≤ T.H (T.sample (cell m)) :=
    (hT.2.1 _ (materialSample_mem_interval hD hT (cell m))).2.1.le
  have hHb := material_sample_height_coefficient_power_bounded hD hT cell 0
    (by norm_num : (0 : ℝ) < 3 / 4)
  let CH : ℝ := hHb.choose
  have hH (m : ℕ) : 0 ≤ H m ∧ H m ≤ CH := by
    refine ⟨Real.rpow_nonneg (hH₀ m) _, ?_⟩
    simpa only [H, CH, Real.rpow_zero, mul_one] using hHb.choose_spec.2 m
  let FF : Fin 2 → ℕ → Parameter S → PolarPoint → ℝ :=
    Fin.cases (fun m z => f z m) (fun _ m z => g z m)
  let RR : ∀ i m, MixedJetRegularity U unitStrip (FF i m) :=
    Fin.cases (fun m => hf.sourceColumns_regularity hf₀ m)
      (fun _ m => hg.sourceColumns_regularity hg₀ m)
  have hFF₀ : FF 0 = (fun m z => f z m) := rfl
  have hFF₁ : FF 1 = (fun m z => g z m) := rfl
  have hprod (m : ℕ) (z : Parameter S) :
      (fun y => ∏ i, FF i m z y) = (fun y => f z m y * g z m y) := by
    funext y
    simp only [Fin.prod_univ_two, hFF₀, hFF₁]
  have hF := hf.sourceColumns_fullTower hD hT hf₀ hE
  have hG := hg.sourceColumns_fullTower hD hT hg₀ hE
  let L : ℕ → ℕ := fun k => max (hF k).choose (hG k).choose
  have hbound : ∀ k s : ℕ, ∃ B : ℝ, 0 < B ∧
      ∀ i m q (hq : q ∈ unitStrip) a b, a + b ≤ s →
      ∀ z ∈ U, ∀ v : Fin k → Parameter S,
        |((RR i m).parameter a b q hq).D k z v| ≤
          B * E m ^ B * parameterHeightWeight (H m) k *
            oneHighVariationWeight (parameterGrading S) base (s + L k) z v := by
    intro k s
    have hsF := (hF k).choose_spec s
    have hsG := (hG k).choose_spec s
    let B : ℝ := max hsF.choose hsG.choose
    refine ⟨B, lt_max_of_lt_left hsF.choose_spec.1, ?_⟩
    intro i
    refine Fin.cases ?_ (fun _ => ?_) i
    · intro m q hq a b hab z hz v
      exact n04SourceColumns_cost_raise hsF.choose_spec.1 (le_max_left _ _) (hE m)
        (parameterHeightWeight_nonneg (hH m).1 k) (oneHighVariationWeight_nonneg _ _ _ _ _)
        (oneHighVariationWeight_mono hp le_rfl
          (Nat.add_le_add_left (le_max_left _ _) s) z v)
        (hsF.choose_spec.2 m q hq a b hab
          ((RR 0 m).parameter a b q hq) z hz v)
    · intro m q hq a b hab z hz v
      exact n04SourceColumns_cost_raise hsG.choose_spec.1 (le_max_right _ _) (hE m)
        (parameterHeightWeight_nonneg (hH m).1 k) (oneHighVariationWeight_nonneg _ _ _ _ _)
        (oneHighVariationWeight_mono hp le_rfl
          (Nat.add_le_add_left (le_max_right _ _) s) z v)
        (hsG.choose_spec.2 m q hq a b hab
          ((hg.sourceColumns_regularity hg₀ m).parameter a b q hq) z hz v)
  have hb := n04SourceColumns_fullProduct_oneHigh (parameterGrading S) hp hI base L
    hU hΩ E H CH hE hH FF RR hbound
  let base' : ℕ := hb.choose
  let ε' : ℝ := min ε (1 / 2)
  have hbase : base ≤ base' := hb.choose_spec.1
  have hε' : 0 < ε' := lt_min hε (by norm_num)
  have hεε : ε' ≤ ε := min_le_left _ _
  have hhalf : ε' ≤ 1 / 2 := min_le_right _ _
  have hsub : sectorNeighborhood S base' ε' ε' ⊆ U :=
    sectorNeighborhood_mono S hbase hεε hεε
  have hU' : IsOpen (sectorNeighborhood S base' ε' ε') :=
    isOpen_sectorNeighborhood S base' ε' ε'
  let RP : ∀ m, MixedJetRegularity U unitStrip (fun z q => f z m q * g z m q) :=
    fun m => (hf.sourceColumns_regularity hf₀ m).mul
      (hg.sourceColumns_regularity hg₀ m) hU hΩ
  let RP' : ∀ m, MixedJetRegularity (sectorNeighborhood S base' ε' ε') unitStrip
      (fun z q => f z m q * g z m q) := fun m =>
    { spatial := fun z hz => (RP m).spatial z (hsub hz)
      parameter := fun i j q hq => ((RP m).parameter i j q hq).restrict hU' hsub }
  have hlow (z : Parameter S) (hz : z ∈ sectorNeighborhood S base' ε' ε') :
      parameterGrading S base' z ≤ 1 := by
    have hh := n07a_parameterGrading_lt_twice_radius (le_rfl : base' ≤ base') hz
    exact hh.le.trans (by linarith)
  refine ⟨base', ε', hbase, hε', hεε,
    n04SourceColumns_data_of_positive_towers hε' hE hH₀ RP' ?_ ?_ ?_ hlow ?_⟩
  · intro z hz m q hq
    exact congrArg₂ (· * ·) ((hf.1 z (hsub hz) m trivial).2 q hq)
      ((hg.1 z (hsub hz) m trivial).2 q hq)
  · intro m
    exact (hf₀.1 m).1.mul (hg₀.1 m).1
  · intro m q hq
    exact congrArg₂ (· * ·) (hf.sourceColumns_zero_eq hε m q hq)
      (hg.sourceColumns_zero_eq hε m q hq)
  · intro k hk
    have ht := hb.choose_spec.2 k
    refine ⟨ht.choose, fun s => ⟨(ht.choose_spec s).choose,
      (ht.choose_spec s).choose_spec.1, ?_⟩⟩
    intro m q hq i j hij z hz v
    let J := ((RP m).parameter i j q hq).congr (fun y _ =>
      congrArg (fun F : PolarPoint → ℝ => mixedDerivative i j F q) (hprod m y).symm)
    have hj := (ht.choose_spec s).choose_spec.2 m q hq i j hij J z (hsub hz) (hlow z hz) v
    have hj' : |((RP m).parameter i j q hq).D k z v| ≤
        (ht.choose_spec s).choose * T.E0 (T.sample (cell m)) ^ (ht.choose_spec s).choose *
          T.H (T.sample (cell m)) ^ (3 / 4 : ℝ) *
            oneHighVariationWeight (parameterGrading S) base' (s + ht.choose) z v := by
      exact n04SourceColumns_positiveHeight_elim hk hj
    exact hj'

/-- A fixed spatial reference multiplier is a special case of the
same multiplication theorem; it contributes no parameter derivatives. -/
theorem CurrentJetDataOn.sourceColumns_fixedMul
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T) (hε : 0 < ε)
    (hE : ∀ m, 1 ≤ T.E0 (T.sample (cell m)))
    (hI : HasInterpolation (parameterGrading S))
    (hf : CurrentJetDataOn S T cell (fun _ => True) base ε f f₀)
    (hf₀ : N04SourceReferenceData T cell f₀) (hg₀ : N04SourceReferenceData T cell g₀) :
    ∃ (base' : ℕ) (ε' : ℝ), base ≤ base' ∧ 0 < ε' ∧ ε' ≤ ε ∧
      CurrentJetDataOn S T cell (fun _ => True) base' ε'
        (fun z m q => f z m q * g₀ m q) (fun m q => f₀ m q * g₀ m q) := by
  have hg := hg₀.sourceColumns_static (S := S) (base := base) (ε := ε)
    (fun m => zero_le_one.trans (hE m))
    (fun m => (hT.2.1 _ (materialSample_mem_interval hD hT (cell m))).2.1.le)
  exact hf.sourceColumns_mul hD hT hε hE hI hg hf₀ hg₀

end ContinuousFlexibility.Analysis
