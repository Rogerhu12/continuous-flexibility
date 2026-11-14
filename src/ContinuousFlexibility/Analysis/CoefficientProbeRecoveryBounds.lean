module

public import ContinuousFlexibility.Analysis.CoefficientProbeRecoveredCoefficients
public import ContinuousFlexibility.Analysis.CoefficientProbeNumeratorBounds

/-!
# Linear mixed bounds for the recovered coefficient correction

On a fixed compact radial set, the four actual source-error fields control
the recovered mixed and angular coefficient differences. Forming the
numerators costs no derivatives and true sine removal costs at most two
angular derivatives. The same finite constant is chosen before the source
fields, the original coefficients, the state and the error majorant.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set
open ContinuousFlexibility.Statements
open scoped ContDiff BigOperators

set_option backward.isDefEq.respectTransparency false

theorem coefficientProbeRecoveredCoefficients_difference_fields
    (A : SymmetricCoefficients) (cross square : PolarPoint → ℝ) :
    (fun p => (coefficientProbeRecoveredCoefficients A cross square).b p - A.b p) =
        (fun p => (1 / 4 : ℝ) * coefficientProbeSineQuotient false cross p) ∧
      (fun p => (coefficientProbeRecoveredCoefficients A cross square).c p - A.c p) =
        (fun p => -(1 / 8 : ℝ) * coefficientProbeSineQuotient true square p) := by
  constructor <;> funext p <;> dsimp only [coefficientProbeRecoveredCoefficients] <;> ring

/-- The two differences are bounded linearly in the original four source
fields. All constants precede those fields; the derivative loss is two. -/
theorem exists_coefficientProbeRecovery_mixed_constant
    {χ : ℝ → ℝ} (hχ : ContDiff ℝ ∞ χ) {K : Set ℝ} (hK : IsCompact K)
    (a b : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {D : ReferenceData},
      ∀ (A : SymmetricCoefficients) (Er Ec Erc Ecc : PolarPoint → ℝ),
      CoefficientProbeFieldRegularity D Er → CoefficientProbeFieldRegularity D Ec →
      CoefficientProbeFieldRegularity D Erc → CoefficientProbeFieldRegularity D Ecc →
      ∀ {J : Set ℝ}, IsOpen J →
      (∀ r ∈ J, coefficientErrorCrossNumerator χ Er Ec Erc (r, 0) = 0 ∧
        coefficientErrorCrossNumerator χ Er Ec Erc (r, Real.pi / 2) = 0) →
      (∀ r ∈ J, coefficientErrorSquareNumerator χ Ec Ecc (r, 0) = 0 ∧
        coefficientErrorSquareNumerator χ Ec Ecc (r, Real.pi / 2) = 0) →
      ∀ p : PolarPoint, p.1 ∈ J → p.1 ∈ K → ∀ M : ℝ, 0 ≤ M →
      (∀ i j : ℕ, i + j ≤ a + b + 2 → ∀ θ : ℝ,
        |mixedDerivative i j Er (p.1, θ)| ≤ M ∧
        |mixedDerivative i j Ec (p.1, θ)| ≤ M ∧
        |mixedDerivative i j Erc (p.1, θ)| ≤ M ∧
        |mixedDerivative i j Ecc (p.1, θ)| ≤ M) →
      let R := coefficientProbeRecoveredCoefficients A
        (coefficientErrorCrossNumerator χ Er Ec Erc)
        (coefficientErrorSquareNumerator χ Ec Ecc)
      |mixedDerivative a b (fun q => R.b q - A.b q) p| +
        |mixedDerivative a b (fun q => R.c q - A.c q) p| ≤ C * M := by
  classical
  choose N hN hbound using fun i j => exists_coefficientProbe_numerator_constant hχ hK i j
  let s := a + b + 2
  let Nall : ℝ := ∑ i ∈ Finset.range (s + 1), ∑ j ∈ Finset.range (s + 1), N i j
  have hNall : 0 ≤ Nall :=
    Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => hN i j
  have hNle (i j : ℕ) (hij : i + j ≤ s) : N i j ≤ Nall := by
    have hi : i ∈ Finset.range (s + 1) := Finset.mem_range.mpr (by omega)
    have hj : j ∈ Finset.range (s + 1) := Finset.mem_range.mpr (by omega)
    calc
      N i j ≤ ∑ k ∈ Finset.range (s + 1), N i k :=
        Finset.single_le_sum (fun k _ => hN i k) hj
      _ ≤ Nall := Finset.single_le_sum
        (fun k _ => Finset.sum_nonneg fun l _ => hN k l) hi
  obtain ⟨Cx, hCx, hxbound⟩ := exists_coefficientProbeSineQuotient_mixed_constant false a b
  obtain ⟨Cy, hCy, hybound⟩ := exists_coefficientProbeSineQuotient_mixed_constant true a b
  refine ⟨((1 / 4 : ℝ) * Cx + (1 / 8 : ℝ) * Cy) * Nall, by positivity, ?_⟩
  intro D A Er Ec Erc Ecc hEr hEc hErc hEcc J hJ hxzero hyzero p hpJ hpK M hM hsource
  let X := coefficientErrorCrossNumerator χ Er Ec Erc
  let Y := coefficientErrorSquareNumerator χ Ec Ecc
  have hX : CoefficientProbeFieldRegularity D X :=
    coefficientErrorCrossNumerator_fieldRegularity hχ hEr hEc hErc
  have hY : CoefficientProbeFieldRegularity D Y :=
    coefficientErrorSquareNumerator_fieldRegularity hχ hEc hEcc
  have hnum (i j : ℕ) (hij : i + j ≤ s) (θ : ℝ) :
      |mixedDerivative i j X (p.1, θ)| + |mixedDerivative i j Y (p.1, θ)| ≤ Nall * M := by
    have hh := hbound i j Er Ec Erc Ecc hEr.1 hEc.1 hErc.1 hEcc.1
      (p.1, θ) hpK M hM (fun k l hkl => hsource k l (hkl.trans hij) θ)
    exact hh.trans (mul_le_mul_of_nonneg_right (hNle i j hij) hM)
  have hqx : |mixedDerivative a b (coefficientProbeSineQuotient false X) p| ≤
      Cx * (Nall * M) := by
    apply hxbound hX hJ hxzero hpJ (mul_nonneg hNall hM)
    intro i j hij θ
    change i + j ≤ a + b + 1 at hij
    have hh := hnum i j (by dsimp only [s]; omega) θ
    exact (le_add_of_nonneg_right (abs_nonneg _)).trans hh
  have hqy : |mixedDerivative a b (coefficientProbeSineQuotient true Y) p| ≤
      Cy * (Nall * M) := by
    apply hybound hY hJ hyzero hpJ (mul_nonneg hNall hM)
    intro i j hij θ
    change i + j ≤ a + b + 2 at hij
    have hh := hnum i j hij θ
    exact (le_add_of_nonneg_left (abs_nonneg _)).trans hh
  have he := coefficientProbeRecoveredCoefficients_difference_fields A X Y
  change |mixedDerivative a b
      (fun q => (coefficientProbeRecoveredCoefficients A X Y).b q - A.b q) p| +
      |mixedDerivative a b
        (fun q => (coefficientProbeRecoveredCoefficients A X Y).c q - A.c q) p| ≤ _
  rw [he.1, he.2, spaces_mixedDerivative_const_mul, spaces_mixedDerivative_const_mul,
    abs_mul, abs_mul]
  simp only [abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 4),
    abs_of_nonpos (by norm_num : -(1 / 8 : ℝ) ≤ 0), neg_neg]
  calc
    _ ≤ (1 / 4 : ℝ) * (Cx * (Nall * M)) + (1 / 8 : ℝ) * (Cy * (Nall * M)) :=
      add_le_add (mul_le_mul_of_nonneg_left hqx (by norm_num))
        (mul_le_mul_of_nonneg_left hqy (by norm_num))
    _ = ((1 / 4 : ℝ) * Cx + (1 / 8 : ℝ) * Cy) * Nall * M := by ring

end ContinuousFlexibility.Analysis
