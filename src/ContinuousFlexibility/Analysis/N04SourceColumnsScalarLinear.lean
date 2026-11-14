module

public import ContinuousFlexibility.Analysis.N04SourceColumnsAdd

/-! Fixed scalars and subtraction in the source interfaces. -/

@[expose] public section

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

variable {S : PhysicalSpacesData} {T : MaterialData} {cell : ℕ → ℕ}
  {base : ℕ} {ε : ℝ}
  {f g : Parameter S → ℕ → PolarPoint → ℝ} {f₀ g₀ : ℕ → PolarPoint → ℝ}

theorem N04SourceReferenceData.sourceColumns_constMul
    (hf : N04SourceReferenceData T cell f₀)
    (hE : ∀ m, 1 ≤ T.E0 (T.sample (cell m)))
    (c : ℕ → ℝ) (hc : ∃ A : ℝ, 0 < A ∧ ∀ m,
      |c m| ≤ A * T.E0 (T.sample (cell m)) ^ A) :
    N04SourceReferenceData T cell (fun m q => c m * f₀ m q) := by
  refine ⟨fun m => ⟨contDiffOn_const.mul (hf.1 m).1,
    fun q hq => congrArg (fun t => c m * t) ((hf.1 m).2 q hq)⟩, ?_⟩
  intro s
  have hs := hf.2 s
  have hp := coefficientEnvelope_pack (hc.choose * hs.choose) (hc.choose + hs.choose)
  refine ⟨hp.choose, hp.choose_spec.1, ?_⟩
  intro m q hq i j hij
  rw [mixedDerivative_const_mul, abs_mul]
  calc
    _ ≤ (hc.choose * T.E0 (T.sample (cell m)) ^ hc.choose) *
        (hs.choose * T.E0 (T.sample (cell m)) ^ hs.choose) :=
      mul_le_mul (hc.choose_spec.2 m) (hs.choose_spec.2 m q hq i j hij)
        (abs_nonneg _) (mul_nonneg hc.choose_spec.1.le
          (Real.rpow_nonneg (zero_le_one.trans (hE m)) _))
    _ = hc.choose * hs.choose * T.E0 (T.sample (cell m)) ^ (hc.choose + hs.choose) := by
      rw [Real.rpow_add (zero_lt_one.trans_le (hE m))]
      ring
    _ ≤ _ := hp.choose_spec.2 _ (hE m)

theorem n04SourceColumns_negative_one_envelope
    (hE : ∀ m, 1 ≤ T.E0 (T.sample (cell m))) :
    ∃ A : ℝ, 0 < A ∧ ∀ m, |(-1 : ℝ)| ≤ A * T.E0 (T.sample (cell m)) ^ A :=
  ⟨1, zero_lt_one, fun m => by
    simpa only [abs_neg, abs_one, one_mul, Real.rpow_one] using hE m⟩

theorem N04SourceReferenceData.sourceColumns_neg
    (hf : N04SourceReferenceData T cell f₀)
    (hE : ∀ m, 1 ≤ T.E0 (T.sample (cell m))) :
    N04SourceReferenceData T cell (fun m q => -f₀ m q) :=
  (hf.sourceColumns_constMul hE (fun _ => -1)
    (n04SourceColumns_negative_one_envelope hE)).sourceColumns_congr
      (fun _ _ _ => neg_one_mul _)

theorem N04SourceReferenceData.sourceColumns_sub
    (hf : N04SourceReferenceData T cell f₀) (hg : N04SourceReferenceData T cell g₀)
    (hE : ∀ m, 1 ≤ T.E0 (T.sample (cell m))) :
    N04SourceReferenceData T cell (fun m q => f₀ m q - g₀ m q) :=
  (hf.sourceColumns_add (hg.sourceColumns_neg hE) hE).sourceColumns_congr
    (fun _ _ _ => (sub_eq_add_neg _ _).symm)

theorem CurrentJetDataOn.sourceColumns_neg
    (hf : CurrentJetDataOn S T cell (fun _ => True) base ε f f₀)
    (hE : ∀ m, 1 ≤ T.E0 (T.sample (cell m)))
    (hH : ∀ m, 0 ≤ T.H (T.sample (cell m))) :
    CurrentJetDataOn S T cell (fun _ => True) base ε
      (fun z m q => -f z m q) (fun m q => -f₀ m q) :=
  (hf.sourceColumns_constMul hE hH (fun _ => -1)
    (n04SourceColumns_negative_one_envelope hE)).sourceColumns_congr
      (fun _ _ _ _ _ => neg_one_mul _) (fun _ _ _ => neg_one_mul _)

theorem CurrentJetDataOn.sourceColumns_sub
    (hf : CurrentJetDataOn S T cell (fun _ => True) base ε f f₀)
    (hg : CurrentJetDataOn S T cell (fun _ => True) base ε g g₀)
    (hf₀ : N04SourceReferenceData T cell f₀) (hg₀ : N04SourceReferenceData T cell g₀)
    (hE : ∀ m, 1 ≤ T.E0 (T.sample (cell m)))
    (hH : ∀ m, 0 ≤ T.H (T.sample (cell m))) :
    CurrentJetDataOn S T cell (fun _ => True) base ε
      (fun z m q => f z m q - g z m q) (fun m q => f₀ m q - g₀ m q) :=
  (hf.sourceColumns_add (hg.sourceColumns_neg hE hH) hf₀
    (hg₀.sourceColumns_neg hE) hE hH).sourceColumns_congr
      (fun _ _ _ _ _ => (sub_eq_add_neg _ _).symm)
      (fun _ _ _ => (sub_eq_add_neg _ _).symm)

/-- A spatially constant family is controlled by its coefficient alone. -/
theorem n04SourceColumns_reference_const
    (hE : ∀ m, 1 ≤ T.E0 (T.sample (cell m)))
    (c : ℕ → ℝ) (hc : ∃ A : ℝ, 0 < A ∧ ∀ m,
      |c m| ≤ A * T.E0 (T.sample (cell m)) ^ A) :
    N04SourceReferenceData T cell (fun m _ => c m) := by
  refine ⟨fun _ => ⟨contDiffOn_const, fun _ _ => rfl⟩,
    fun _ => ⟨hc.choose, hc.choose_spec.1, ?_⟩⟩
  intro m q hq i j hij
  by_cases hi : i = 0
  · subst i
    by_cases hj : j = 0
    · subst j
      rw [spaces_mixedDerivative_zero]
      exact hc.choose_spec.2 m
    · simp only [mixedDerivative, iteratedDeriv_zero,
        iteratedDeriv_const, if_neg hj, ite_true, ite_self, abs_zero]
      exact mul_nonneg hc.choose_spec.1.le (Real.rpow_nonneg (zero_le_one.trans (hE m)) _)
  · simp only [mixedDerivative, iteratedDeriv_const, if_neg hi, ite_true, ite_self, abs_zero]
    exact mul_nonneg hc.choose_spec.1.le (Real.rpow_nonneg (zero_le_one.trans (hE m)) _)

theorem n04SourceColumns_reference_one
    (hE : ∀ m, 1 ≤ T.E0 (T.sample (cell m))) :
    N04SourceReferenceData T cell (fun _ _ => (1 : ℝ)) :=
  n04SourceColumns_reference_const hE (fun _ => 1)
    ⟨1, zero_lt_one, fun m => by simpa only [abs_one, one_mul, Real.rpow_one] using hE m⟩

end ContinuousFlexibility.Analysis
