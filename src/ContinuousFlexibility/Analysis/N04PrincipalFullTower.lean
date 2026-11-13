import ContinuousFlexibility.Analysis.N04PrincipalDataTowers
import ContinuousFlexibility.Analysis.MaterialEnvelopeNormalization

/-!
# Full current towers from a weighted difference and reference bounds

The reference contributes only to parameter order zero. A uniform bound
for the sampled height weight allows the full family to be used as an
unweighted factor; its difference tower retains the height weight.
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

theorem CurrentJetDataOn.n04Principal_fullWeighted
    {S : PhysicalSpacesData} {T : MaterialData} {cell : ℕ → ℕ}
    {P : ℕ → Prop} {base : ℕ} {ε : ℝ}
    {f : Parameter S → ℕ → PolarPoint → ℝ} {f₀ : ℕ → PolarPoint → ℝ}
    (h : CurrentJetDataOn S T cell P base ε f f₀)
    (href : ∀ m, P m → ContDiffOn ℝ ∞ (f₀ m) unitStrip)
    (hrefb : ∀ s : ℕ, ∃ B : ℝ, 0 < B ∧ ∀ m, P m →
      ∀ (q : unitStrip) (a b : ℕ), a + b ≤ s →
        |mixedDerivative a b (f₀ m) q.val| ≤ B * T.E0 (T.sample (cell m)) ^ B)
    (hE : ∀ m, 1 ≤ T.E0 (T.sample (cell m)))
    (hH : ∀ m, 0 ≤ T.H (T.sample (cell m)))
    {RH : ℝ} (hRH : 0 ≤ RH)
    (hheight : ∀ m, T.H (T.sample (cell m)) ^ (3 / 4 : ℝ) ≤ RH) :
    N04PrincipalWeightedTowerBounds (parameterGrading S) base
      (fun m : {m : ℕ // P m} => T.E0 (T.sample (cell m.val))) (fun _ => 1)
      (fun m => h.n04Principal_familyRegularity href m.val m.property) := by
  intro k
  have hd := h.2.choose_spec.2 k
  refine ⟨hd.choose, fun s => ?_⟩
  let Bd : ℝ := (hd.choose_spec s).choose
  let Br : ℝ := (hrefb s).choose
  have hBd : 0 < Bd := (hd.choose_spec s).choose_spec.1
  have hBr : 0 < Br := (hrefb s).choose_spec.1
  let A : ℝ := max Bd Br
  let C : ℝ := Bd * RH + Br
  have hpack := coefficientEnvelope_pack C A
  refine ⟨hpack.choose, hpack.choose_spec.1, ?_⟩
  intro m a b hab q hq z hz _ v
  let E : ℝ := T.E0 (T.sample (cell m.val))
  let W : ℝ := T.H (T.sample (cell m.val)) ^ (3 / 4 : ℝ)
  let O : ℝ := oneHighVariationWeight (parameterGrading S) base (s + hd.choose) z v
  have hE0 : 0 ≤ E := zero_le_one.trans (hE m.val)
  have hEA : 0 ≤ E ^ A := Real.rpow_nonneg hE0 _
  have hO : 0 ≤ O := oneHighVariationWeight_nonneg _ _ _ _ _
  have hdcost : Bd * E ^ Bd * W ≤ Bd * E ^ A * RH :=
    mul_le_mul
      (mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_exponent_le (hE m.val) (le_max_left _ _)) hBd.le)
      (hheight m.val) (Real.rpow_nonneg (hH m.val) _)
      (mul_nonneg hBd.le hEA)
  have hrcost : Br * E ^ Br ≤ Br * E ^ A :=
    mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le (hE m.val) (le_max_right _ _)) hBr.le
  let Jf := (h.n04Principal_familyRegularity href m.val m.property).parameter a b q hq
  let Jd := h.2.choose m.val m.property a b ⟨q, hq⟩
  have hdiff : ‖Jd.D k z v‖ ≤ Bd * E ^ A * RH * O :=
    (Real.norm_eq_abs _).trans_le
      (((hd.choose_spec s).choose_spec.2 z hz v m.val m.property ⟨q, hq⟩ a b hab).trans
        (mul_le_mul_of_nonneg_right hdcost hO))
  have hfull : ‖Jf.D k z v‖ ≤ C * E ^ A * O := by
    by_cases hk : k = 0
    · subst k
      have hO1 : 1 ≤ O := by
        dsimp only [O]
        simp only [oneHighVariationWeight, Finset.univ_eq_empty,
          Finset.prod_empty, Finset.sum_empty, mul_one, add_zero]
        exact le_add_of_nonneg_right (apply_nonneg _ _)
      have hreference : |mixedDerivative a b (f₀ m.val) q| ≤ Br * E ^ A * O :=
        ((hrefb s).choose_spec.2 m.val m.property ⟨q, hq⟩ a b hab).trans
          (hrcost.trans (le_mul_of_one_le_right (mul_nonneg hBr.le hEA) hO1))
      rw [smoothDirections_D_zero_apply Jf hz v]
      rw [smoothDirections_D_zero_apply Jd hz v] at hdiff
      have heq := mixedDerivative_sub_of_contDiffOn
        (isOpen_Ioo.prod isOpen_univ) (h.1 z hz m.val m.property).1 (href m.val m.property) a b hq
      have hsum : mixedDerivative a b (f z m.val) q =
          mixedDerivative a b (fun y => f z m.val y - f₀ m.val y) q +
            mixedDerivative a b (f₀ m.val) q := by rw [heq]; ring
      rw [hsum]
      calc
        _ ≤ ‖mixedDerivative a b (fun y => f z m.val y - f₀ m.val y) q‖ +
            ‖mixedDerivative a b (f₀ m.val) q‖ := norm_add_le _ _
        _ ≤ Bd * E ^ A * RH * O + Br * E ^ A * O :=
          add_le_add hdiff ((Real.norm_eq_abs _).trans_le hreference)
        _ = C * E ^ A * O := by dsimp only [C]; ring
    · let K := Jd.congr (fun y hy => mixedDerivative_sub_of_contDiffOn
        (isOpen_Ioo.prod isOpen_univ) (h.1 y hy m.val m.property).1 (href m.val m.property) a b hq)
      have heq : Jd.D k z v = Jf.D k z v :=
        smoothDirections_D_sub_constant Jf K (Nat.pos_of_ne_zero hk) hz v
      rw [← heq]
      exact hdiff.trans (by
        have hh := mul_le_mul_of_nonneg_right
          (show Bd * RH ≤ C from le_add_of_nonneg_right hBr.le)
          (mul_nonneg hEA hO)
        convert hh using 1 <;> ring)
  have hp := mul_le_mul_of_nonneg_right (hpack.choose_spec.2 E (hE m.val)) hO
  simpa only [mul_one] using hfull.trans hp

end ContinuousFlexibility.Analysis
