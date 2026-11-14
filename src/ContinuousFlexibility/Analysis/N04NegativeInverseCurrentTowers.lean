module

public import ContinuousFlexibility.Analysis.N04NegativeInverseCurrentRegularity

/-! Uniform selected current estimates with the reference present only at order zero. -/

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

variable {S : PhysicalSpacesData} {T : MaterialData} {cell : ℕ → ℕ}
  {P : ℕ → Prop} {base : ℕ} {ε : ℝ}
  {f : Parameter S → ℕ → PolarPoint → ℝ} {f₀ : ℕ → PolarPoint → ℝ}

/-- Keep the concrete parameter grading opaque while simplifying a zero jet. -/
private theorem n04NegativeInverse_zeroTower_of_value
    {X : Type*} [TopologicalSpace X] [AddCommGroup X] [Module ℝ X]
    [IsTopologicalAddGroup X] [ContinuousSMul ℝ X]
    {U : Set X} {g : X → ℝ} (J : SmoothDirections U g)
    (p : ℕ → Seminorm ℝ X) (base high : ℕ) (B E H : ℝ)
    {z : X} (hz : z ∈ U) (v : Fin 0 → X)
    (h : |g z| ≤ B * E ^ B * (1 + p high z)) :
    |J.D 0 z v| ≤ B * E ^ B * parameterHeightWeight H 0 *
      oneHighVariationWeight p base high z v := by
  simpa only [smoothDirections_D_zero_apply J hz v, parameterHeightWeight,
    ite_true, mul_one, oneHighVariationWeight, Finset.univ_eq_empty,
    Finset.prod_empty, Finset.sum_empty, add_zero] using h

private theorem n04NegativeInverse_positiveHeight_bound
    {k : ℕ} (hk : k ≠ 0) {A H W x : ℝ} (h : x ≤ A * H * W) :
    x ≤ A * parameterHeightWeight H k * W := by
  simpa only [parameterHeightWeight, if_neg hk] using h

/-- Including the unweighted reference at order zero gives the full
current tower. Positive parameter orders retain the full height factor. -/
theorem CurrentJetDataOn.negativeInverse_fullTower
    {D : ReferenceData} (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T)
    (h : CurrentJetDataOn S T cell P base ε f f₀)
    (h₀ : ∀ m, P m → ContDiffOn ℝ ∞ (f₀ m) unitStrip)
    (href : ∀ s : ℕ, ∃ B : ℝ, 0 < B ∧ ∀ m, P m →
      ∀ q ∈ unitStrip, ∀ i j : ℕ, i + j ≤ s →
        |mixedDerivative i j (f₀ m) q| ≤ B * T.E0 (T.sample (cell m)) ^ B)
    (hE : ∀ m, 1 ≤ T.E0 (T.sample (cell m))) :
    ∀ k : ℕ, ∃ loss : ℕ, ∀ s : ℕ, ∃ B : ℝ, 0 < B ∧
      ∀ m (hm : P m) q (hq : q ∈ unitStrip) i j, i + j ≤ s →
      ∀ J : SmoothDirections (sectorNeighborhood S base ε ε)
        (fun z => mixedDerivative i j (f z m) q),
      ∀ z ∈ sectorNeighborhood S base ε ε, ∀ v : Fin k → Parameter S,
        |J.D k z v| ≤ B * T.E0 (T.sample (cell m)) ^ B *
          parameterHeightWeight (T.H (T.sample (cell m)) ^ (3 / 4 : ℝ)) k *
            oneHighVariationWeight (parameterGrading S) base (s + loss) z v := by
  intro k
  by_cases hk : k = 0
  · subst k
    have hheight := material_sample_height_coefficient_power_bounded hD hT cell 0
      (by norm_num : (0 : ℝ) < 3 / 4)
    let CH : ℝ := hheight.choose
    have hCH : 0 < CH := hheight.choose_spec.1
    have hheight' (m : ℕ) : T.H (T.sample (cell m)) ^ (3 / 4 : ℝ) ≤ CH := by
      simpa only [CH, Real.rpow_zero, mul_one] using hheight.choose_spec.2 m
    have hv := h.2.choose_spec.1
    refine ⟨hv.choose, fun s => ?_⟩
    have hd := hv.choose_spec s
    have hr := href s
    have hc := n04Realization_referenceAndDifferenceEnvelope hr.choose_spec.1.le
      hd.choose_spec.1.le hCH.le
    refine ⟨hc.choose, hc.choose_spec.1, ?_⟩
    intro m hm q hq i j hij J z hz v
    have he : mixedDerivative i j (f z m) q =
        mixedDerivative i j (fun y => f z m y - f₀ m y) q +
          mixedDerivative i j (f₀ m) q := by
      rw [mixedDerivative_sub_of_contDiffOn (isOpen_Ioo.prod isOpen_univ)
        (h.1 z hz m hm).1 (h₀ m hm) i j hq]
      exact (sub_add_cancel _ _).symm
    have hb := hc.choose_spec.2 (T.E0 (T.sample (cell m)))
      (T.H (T.sample (cell m)) ^ (3 / 4 : ℝ))
      (parameterGrading S (s + hv.choose) z) _ _ (hE m) (hheight' m) (apply_nonneg _ _)
      (hr.choose_spec.2 m hm q hq i j hij)
      (hd.choose_spec.2 z hz m hm ⟨q, hq⟩ i j hij)
    exact n04NegativeInverse_zeroTower_of_value J (parameterGrading S) base
      (s + hv.choose) hc.choose (T.E0 (T.sample (cell m)))
      (T.H (T.sample (cell m)) ^ (3 / 4 : ℝ)) hz v ((congrArg abs he).trans_le hb)
  · have ht := h.negativeInverse_positiveTower h₀ k (Nat.pos_of_ne_zero hk)
    refine ⟨ht.choose, fun s => ⟨(ht.choose_spec s).choose,
      (ht.choose_spec s).choose_spec.1, ?_⟩⟩
    intro m hm q hq i j hij J z hz v
    exact n04NegativeInverse_positiveHeight_bound hk
      ((ht.choose_spec s).choose_spec.2 m hm q hq i j hij J z hz v)


end ContinuousFlexibility.Analysis

/-- info: 'ContinuousFlexibility.Analysis.CurrentJetDataOn.negativeInverse_fullTower' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ContinuousFlexibility.Analysis.CurrentJetDataOn.negativeInverse_fullTower
