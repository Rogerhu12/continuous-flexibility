module

public import ContinuousFlexibility.Analysis.CoefficientProbeFieldRegularity

/-!
# Fixed finite constants for the actual probe numerators

The two multipliers are fixed smooth periodic functions. On a compact
radial set one constant controls both genuine numerator jets, linearly
in the four source-error jets of orders no higher than the output order.
The constant is selected before the source fields and their bound, so
substitution of N03's actual error estimate preserves its common loss.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set
open ContinuousFlexibility.Statements
open scoped ContDiff

set_option backward.isDefEq.respectTransparency false

/-- Forming the actual cross and square numerators introduces no
derivative loss and no nonlinear power of the source-error bound. -/
theorem exists_coefficientProbe_numerator_constant
    {χ : ℝ → ℝ} (hχ : ContDiff ℝ ∞ χ) {K : Set ℝ} (hK : IsCompact K)
    (a b : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ Er Ec Erc Ecc : PolarPoint → ℝ,
      ContDiff ℝ ∞ Er → ContDiff ℝ ∞ Ec → ContDiff ℝ ∞ Erc → ContDiff ℝ ∞ Ecc →
      ∀ p : PolarPoint, p.1 ∈ K → ∀ M : ℝ, 0 ≤ M →
        (∀ i j : ℕ, i + j ≤ a + b →
          |mixedDerivative i j Er p| ≤ M ∧ |mixedDerivative i j Ec p| ≤ M ∧
            |mixedDerivative i j Erc p| ≤ M ∧ |mixedDerivative i j Ecc p| ≤ M) →
        |mixedDerivative a b (coefficientErrorCrossNumerator χ Er Ec Erc) p| +
            |mixedDerivative a b (coefficientErrorSquareNumerator χ Ec Ecc) p| ≤ C * M := by
  have hr := contDiff_radialLinearProbe hχ
  have hc := contDiff_radialCosineProbe hχ
  obtain ⟨Cr, hCr, hradial⟩ := exists_local_mixedMultiplier_constant
    hK hr (radialLinearProbe_periodic χ) a b
  obtain ⟨Cc, hCc, hcosine⟩ := exists_local_mixedMultiplier_constant
    hK hc (radialCosineProbe_periodic χ) a b
  refine ⟨2 + Cr + 3 * Cc, by positivity, ?_⟩
  intro Er Ec Erc Ecc hEr hEc hErc hEcc p hp M hM herror
  have hREc := hradial univ isOpen_univ Ec hEc.contDiffOn p (mem_univ _) hp M hM
    (fun i j hij => (herror i j hij).2.1)
  have hCEr := hcosine univ isOpen_univ Er hEr.contDiffOn p (mem_univ _) hp M hM
    (fun i j hij => (herror i j hij).1)
  have hCEc := hcosine univ isOpen_univ Ec hEc.contDiffOn p (mem_univ _) hp M hM
    (fun i j hij => (herror i j hij).2.1)
  have hrc := (herror a b le_rfl).2.2.1
  have hcc := (herror a b le_rfl).2.2.2
  have hcrossEq : mixedDerivative a b (coefficientErrorCrossNumerator χ Er Ec Erc) p =
      mixedDerivative a b Erc p -
        mixedDerivative a b (fun q => radialLinearProbe χ q * Ec q) p -
          mixedDerivative a b (fun q => radialCosineProbe χ q * Er q) p := by
    change mixedDerivative a b
      (fun q => Erc q - radialLinearProbe χ q * Ec q - radialCosineProbe χ q * Er q) p = _
    rw [mixedDerivative_sub_of_contDiffOn
      (f := fun q => Erc q - radialLinearProbe χ q * Ec q)
      (g := fun q => radialCosineProbe χ q * Er q) isOpen_univ
      (hErc.sub (hr.mul hEc)).contDiffOn (hc.mul hEr).contDiffOn a b (mem_univ p),
      mixedDerivative_sub_of_contDiffOn (f := Erc)
        (g := fun q => radialLinearProbe χ q * Ec q) isOpen_univ hErc.contDiffOn
        (hr.mul hEc).contDiffOn a b (mem_univ p)]
  have hsquareEq : mixedDerivative a b (coefficientErrorSquareNumerator χ Ec Ecc) p =
      mixedDerivative a b Ecc p -
        2 * mixedDerivative a b (fun q => radialCosineProbe χ q * Ec q) p := by
    have he : coefficientErrorSquareNumerator χ Ec Ecc =
        (fun q => Ecc q - 2 * (radialCosineProbe χ q * Ec q)) := by
      funext q
      dsimp only [coefficientErrorSquareNumerator]
      ring
    rw [he, mixedDerivative_sub_of_contDiffOn (f := Ecc)
      (g := fun q => 2 * (radialCosineProbe χ q * Ec q)) isOpen_univ hEcc.contDiffOn
      (contDiff_const.mul (hc.mul hEc)).contDiffOn a b (mem_univ p),
      spaces_mixedDerivative_const_mul]
  have hcross : |mixedDerivative a b (coefficientErrorCrossNumerator χ Er Ec Erc) p| ≤
      M + Cr * M + Cc * M := by
    rw [hcrossEq]
    calc
      _ ≤ |mixedDerivative a b Erc p -
            mixedDerivative a b (fun q => radialLinearProbe χ q * Ec q) p| +
              |mixedDerivative a b (fun q => radialCosineProbe χ q * Er q) p| := abs_sub _ _
      _ ≤ (|mixedDerivative a b Erc p| +
            |mixedDerivative a b (fun q => radialLinearProbe χ q * Ec q) p|) +
              |mixedDerivative a b (fun q => radialCosineProbe χ q * Er q) p| :=
                add_le_add (abs_sub _ _) (le_refl _)
      _ ≤ M + Cr * M + Cc * M := add_le_add (add_le_add hrc hREc) hCEr
  have hsquare : |mixedDerivative a b (coefficientErrorSquareNumerator χ Ec Ecc) p| ≤
      M + 2 * (Cc * M) := by
    rw [hsquareEq]
    calc
      _ ≤ |mixedDerivative a b Ecc p| +
          |2 * mixedDerivative a b (fun q => radialCosineProbe χ q * Ec q) p| := abs_sub _ _
      _ = |mixedDerivative a b Ecc p| +
          2 * |mixedDerivative a b (fun q => radialCosineProbe χ q * Ec q) p| := by
            rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
      _ ≤ M + 2 * (Cc * M) :=
        add_le_add hcc (mul_le_mul_of_nonneg_left hCEc (by norm_num))
  calc
    _ ≤ (M + Cr * M + Cc * M) + (M + 2 * (Cc * M)) := add_le_add hcross hsquare
    _ = (2 + Cr + 3 * Cc) * M := by ring

end ContinuousFlexibility.Analysis
