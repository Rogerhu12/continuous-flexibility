import ContinuousFlexibility.Analysis.RootCoefficientDivision
import ContinuousFlexibility.Analysis.RootShiftMixedJets
import ContinuousFlexibility.Analysis.CylinderMixedJetNorms
import ContinuousFlexibility.Analysis.OneSidedOrdinaryJets

/-!
# Actual coefficient division on the root axis

At radial coordinate zero every point in the Taylor integral is the
same root point. The qualitative strip supplies the actual smooth
factorization, but its width contributes no inverse power to the bound.
Only one additional numerator derivative and the planar factor `2^n`
are needed, at every angle and for either root orientation.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set
open ContinuousFlexibility.Statements
open scoped ContDiff

theorem norm_iteratedFDeriv_smoothRadialFactor_root_le
    {F G : PolarPoint → ℝ} (hF : ContDiff ℝ ∞ F) (hG : ContDiff ℝ ∞ G)
    (hfactor : ∀ p : PolarPoint, F p = p.1 * G p) (n : ℕ) (θ : ℝ) :
    ‖iteratedFDeriv ℝ n G (0, θ)‖ ≤
      (2 : ℝ) ^ n * ‖iteratedFDeriv ℝ (n + 1) F (0, θ)‖ := by
  apply norm_iteratedFDeriv_le_of_mixedDerivative isOpen_univ hG.contDiffOn
    n (mem_univ _) (norm_nonneg _)
  intro a b hab
  rw [Real.norm_eq_abs]
  apply abs_mixedDerivative_smoothRadialFactor_le hF hG hfactor a b
  intro t _ht
  have hindex : (a + 1) + b = n + 1 := by omega
  have h := abs_mixedDerivative_le_norm_iteratedFDeriv isOpen_univ hF.contDiffOn
    (a + 1) b (p := (0, θ)) (mem_univ _)
  rw [hindex] at h
  simpa only [mul_zero] using h

/-- Both fields are the actual root coefficient fields. The extension
is used only to justify their ordinary jets at the interior root. -/
theorem norm_iteratedFDeriv_rootCoefficientRadialFactor_root_le
    {wref g w : ℝ → ℝ} {z : PolarPoint → ℝ}
    (hwref : ContDiff ℝ ∞ wref) (hg : ContDiff ℝ ∞ g)
    (hw : ContDiff ℝ ∞ w) (hz : ContDiff ℝ ∞ z)
    {r σ R : ℝ} (hR : 0 < R)
    (hstrip : RootCoefficientStripConditions wref g w z r σ R)
    (n : ℕ) (θ : ℝ) :
    ‖iteratedFDeriv ℝ n (rootCoefficientRadialFactor wref g w z r σ) (0, θ)‖ ≤
      (2 : ℝ) ^ n *
        ‖iteratedFDeriv ℝ (n + 1) (rootCoefficientDiscriminant w z r σ) (0, θ)‖ := by
  obtain ⟨F, G, hF, hG, hfactor, hFeq, hGeq⟩ :=
    exists_rootCoefficient_factor_extension hwref hg hw hz hR hstrip
  have hp : (0, θ) ∈ Ioo (-R) R ×ˢ (univ : Set ℝ) :=
    ⟨⟨by linarith, hR⟩, mem_univ _⟩
  have hFjet := iteratedFDeriv_eqOn_of_isOpen
    (isOpen_Ioo.prod isOpen_univ) hFeq (n + 1) hp
  have hGjet := iteratedFDeriv_eqOn_of_isOpen
    (isOpen_Ioo.prod isOpen_univ) hGeq n hp
  rw [← hGjet, ← hFjet]
  exact norm_iteratedFDeriv_smoothRadialFactor_root_le hF hG hfactor n θ

/-- Physical mixed numerator jets at the same turning circle suffice.
Neither the reference-cell size nor the chosen strip enters the cost. -/
theorem norm_iteratedFDeriv_rootCoefficientRadialFactor_root_le_of_physical_mixed
    {wref g w : ℝ → ℝ} {z : PolarPoint → ℝ}
    (hwref : ContDiff ℝ ∞ wref) (hg : ContDiff ℝ ∞ g)
    (hw : ContDiff ℝ ∞ w) (hz : ContDiff ℝ ∞ z)
    {r σ R : ℝ} (hσ : σ = 1 ∨ σ = -1) (hR : 0 < R)
    (hstrip : RootCoefficientStripConditions wref g w z r σ R)
    (n : ℕ) (θ : ℝ) {M : ℝ} (hM : 0 ≤ M)
    (hbound : ∀ a b : ℕ, a + b = n + 1 →
      |mixedDerivative a b
        (fun p => polarLinearB w z p ^ 2 - polarLinearA w z p * polarCorrectedC w z p)
        (r, θ)| ≤ M) :
    ‖iteratedFDeriv ℝ n (rootCoefficientRadialFactor wref g w z r σ) (0, θ)‖ ≤
      (2 : ℝ) ^ n * M := by
  obtain ⟨F, G, hF, hG, hfactor, hFeq, hGeq⟩ :=
    exists_rootCoefficient_factor_extension hwref hg hw hz hR hstrip
  have hp : (0, θ) ∈ Ioo (-R) R ×ˢ (univ : Set ℝ) :=
    ⟨⟨by linarith, hR⟩, mem_univ _⟩
  rw [← iteratedFDeriv_eqOn_of_isOpen (isOpen_Ioo.prod isOpen_univ) hGeq n hp]
  apply norm_iteratedFDeriv_le_of_mixedDerivative isOpen_univ hG.contDiffOn
    n (mem_univ _) hM
  intro a b hab
  rw [Real.norm_eq_abs]
  apply abs_mixedDerivative_smoothRadialFactor_le hF hG hfactor a b
  intro t _ht
  change |mixedDerivative (a + 1) b F (t * 0, θ)| ≤ M
  rw [mul_zero, mixedDerivative_eqOn_of_isOpen
    (isOpen_Ioo.prod isOpen_univ) hFeq (a + 1) b hp]
  have hshift := abs_mixedDerivative_rootProfileShift (r := r)
    (fun p => polarLinearB w z p ^ 2 - polarLinearA w z p * polarCorrectedC w z p)
    hσ (a + 1) b (0, θ)
  have hpt : rootProfileShift r σ (0, θ) = (r, θ) := by
    simp only [rootProfileShift, mul_zero, add_zero]
  rw [hpt] at hshift
  have hfun : rootCoefficientDiscriminant w z r σ = fun q =>
      polarLinearB w z (rootProfileShift r σ q) ^ 2 -
        polarLinearA w z (rootProfileShift r σ q) *
          polarCorrectedC w z (rootProfileShift r σ q) := by
    funext q
    simp only [rootCoefficientDiscriminant]
  rw [hfun]
  exact hshift.trans_le (hbound (a + 1) b (by omega))

end ContinuousFlexibility.Analysis
