module

public import ContinuousFlexibility.Radial.ProfileScalarWeightedOffset
public import ContinuousFlexibility.Radial.R11bRegularModeData
public import ContinuousFlexibility.Radial.R11bModeForcingBounds
public import ContinuousFlexibility.Radial.R11bRemainderEnergy
public import ContinuousFlexibility.Radial.R11bAngularFrequencyEstimate

/-!
# Uniform finite energy bounds for all actual normal modes

The zero mode retains its left-tail constant and the critical positive
mode retains the true border column. The scalar estimate is summed over
an arbitrary finite selection, with constants independent of that selection.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Radial

open Set MeasureTheory Real
open scoped BigOperators ContDiff
open ContinuousFlexibility.Statements ContinuousFlexibility.Analysis

set_option backward.isDefEq.respectTransparency false

theorem r11b_finite_mean_coefficient_sq_le (J : Finset ℕ) (a : ℝ) :
    (∑ n ∈ J, (if n = 0 then a else 0) ^ 2) ≤ a ^ 2 := by
  classical
  by_cases h0 : 0 ∈ J
  · simp [ite_pow, h0]
  · simpa [ite_pow, h0] using sq_nonneg a

theorem r11b_mode_derivative_bounds {D : ReferenceData}
    (hD : IsAccumulatingProfile D) (hborder : RadialTrueBorder D)
    (M₀ M₁ : ℝ)
    (hmodes : ∀ j : ℕ, 2 ≤ j → Even j →
      ∃ H : RadialModePair D →L[ℝ] RadialModePair D, ModeInverseProperties D j H)
    (hmatched : ∃ H : RadialModePair D →L[ℝ] RadialModePair D,
      ∃ Mdata : RadialMatchingData D, ActualMatchedRepresentation D H Mdata) :
    ∃ L : ℝ, 0 ≤ L ∧ ∀ γ : ℝ, 0 < γ → |γ| ≤ 1 →
      ∀ G : RadialSource → RadialUnknown,
      ReferenceInverseProperties D γ M₀ M₁ G →
      ∃ A : ℝ, 0 < A ∧ ∀ (F : RadialSource) (d : PolarPoint → ℝ),
      SourceMember D γ M₀ F → WeakAngularDerivative D F.1 d →
      SourceDerivativeMember D γ M₀ d →
      ∃ c : ℕ → ℝ → ℝ,
        (∀ n, ContDiffOn ℝ 1 (c n) (radialCore D)) ∧
        (∀ n, c n =ᵐ[volume.restrict (radialCore D)]
          evenFourierCoefficient (G F).1 n) ∧
        (∀ n, Summable (fun m =>
          exp (-2 * (M₁ + L) * radialQ (D.cellIndex m) + 2 * γ * radialS (D.cellIndex m)) *
            profileScalarCellSquare D (deriv (c n)) m)) ∧
        ∀ J : Finset ℕ,
          (∑ n ∈ J, ∑' m,
            exp (-2 * (M₁ + L) * radialQ (D.cellIndex m) + 2 * γ * radialS (D.cellIndex m)) *
              profileScalarCellSquare D (deriv (c n)) m) ≤
            A * (sourceNormSquare D γ M₀ F + sourceNormSquare D γ M₀ (d, 0)) := by
  classical
  obtain ⟨H, Mdata, hMatch⟩ := hmatched
  obtain ⟨L, hL, hscalar⟩ :=
    profile_scalar_weighted_caccioppoli_with_left_offset hD hborder M₀ M₁
  have hgeom : RadialProfileGeometry D := hD.choose_spec.1
  have hab : D.a < D.b := hgeom.2.1
  refine ⟨L, hL, ?_⟩
  intro γ hγ hγabs G hG
  obtain ⟨K, hK, hmode⟩ := hscalar γ hγabs
  obtain ⟨Cg, hCg, hGbound⟩ := hG.2.2.2
  obtain ⟨Cf, hCf, hfrequency⟩ :=
    r11b_reference_inverse_finite_frequency_bound hD hborder hγ hG hmodes
  let WF : ℕ → ℝ := fun k => exp (2 * M₀ * radialQ k + 2 * γ * radialS k)
  let WU : ℕ → ℝ := fun k => exp (-2 * M₁ * radialQ k + 2 * γ * radialS k)
  let WN : ℕ → ℝ := fun k => exp (-2 * (M₁ + L) * radialQ k + 2 * γ * radialS k)
  let Bcol : ℝ := ∑' m, WF (D.cellIndex m) *
    profileScalarCellSquare D (referenceColumn D) m
  have hBcol : 0 ≤ Bcol := tsum_nonneg fun m =>
    mul_nonneg (exp_pos _).le (profileScalarCellSquare_nonneg D _ m)
  let A : ℝ := K * (2 + 2 * Cg ^ 2 * Bcol + 2 * Cg ^ 2 + Cf ^ 2)
  have hA : 0 < A := by dsimp only [A]; positivity
  refine ⟨A, hA, ?_⟩
  intro F d hF hder hd
  let SF : ℝ := sourceNormSquare D γ M₀ F
  let SD : ℝ := sourceNormSquare D γ M₀ (d, 0)
  have hSF : 0 ≤ SF := r11b_sourceNormSquare_nonneg hab.le γ M₀ F
  have hSD : 0 ≤ SD := r11b_sourceNormSquare_nonneg hab.le γ M₀ (d, 0)
  have hSFH : SF ≤ SF + SD := le_add_of_nonneg_right hSD
  obtain ⟨a, hU, hUNorm⟩ := hGbound F hF
  let NU : ℝ := outputNormSquare D γ M₁ a (G F)
  have hN : NU ≤ Cg ^ 2 * SF := hUNorm
  have hcell0 : 0 ≤ ∑' m, outputCellSquare D γ M₁
      (outputRemainder D a (G F)) m := tsum_nonneg fun m =>
    mul_nonneg (exp_pos _).le (r11b_referenceCellSquare_nonneg hab.le m _)
  have haN : a ^ 2 ≤ NU := by
    dsimp only [NU, outputNormSquare]
    nlinarith only [hcell0, sq_nonneg (G F).2]
  have hnuN : (G F).2 ^ 2 ≤ NU := by
    dsimp only [NU, outputNormSquare]
    nlinarith only [hcell0, sq_nonneg a]
  have huLp : MemLp (G F).1 2 (radialPhysicalMeasure D) :=
    r11b_output_memLp hD hborder hγ ⟨a, hU⟩
  have hfLp : MemLp F.1 2 (radialPhysicalMeasure D) :=
    r11b_source_memLp hD hγ hF
  let r₀ : ℝ := (D.a + D.b) / 2
  have hr₀ : r₀ ∈ radialCore D := ⟨by dsimp only [r₀]; linarith,
    by dsimp only [r₀]; linarith⟩
  obtain ⟨c, q, hcEq, hc, hcLp, hflux, hrem⟩ :=
    r11b_exists_evenModeData hD hborder hγ (hG.1 F hF) r₀ hr₀
  let a₀ : ℕ → ℝ := fun n => if n = 0 then a else 0
  let v : ℕ → ℝ → ℝ := fun n r => c n r - a₀ n * D.chiLeft r
  let f : ℕ → ℝ → ℝ := r11bEvenModeForcing D (G F) F
  let EF : ℕ → ℝ := fun n => ∑' m, WF (D.cellIndex m) *
    profileScalarCellSquare D (f n) m
  let EU : ℕ → ℝ := fun n => ∑' m, WU (D.cellIndex m) *
    profileScalarCellSquare D (v n) m
  let EN : ℕ → ℝ := fun n => ∑' m, WN (D.cellIndex m) *
    profileScalarCellSquare D (deriv (c n)) m
  obtain ⟨hsF, hsumF⟩ := r11b_evenModeForcing_source_bound hD hborder hMatch hF (G F)
  have hfreq : ∀ J : Finset ℕ, (∀ n ∈ J, 0 < n) →
      (∑ n ∈ J, ((2 * n : ℕ) : ℝ) ^ 2 *
        r11bWeightedModeSquare D γ M₁ (G F).1 (2 * n)) ≤ Cf ^ 2 * (SF + SD) :=
    hfrequency F d hF hder hd
  obtain ⟨hsU, hsumU⟩ :=
    r11b_remainder_mode_energy_bound hab.le huLp hU v (hrem a) hfreq
  have hnormal (n : ℕ) :
      Summable (fun m => WN (D.cellIndex m) *
        profileScalarCellSquare D (deriv (c n)) m) ∧
      EN n ≤ K * (EF n + (1 + ((2 * n : ℕ) : ℝ) ^ 2) * EU n + a₀ n ^ 2) := by
    apply hmode ((2 * n : ℕ) : ℝ) (a₀ n) (c n) (f n) r₀ (q n)
    · intro hj
      by_cases hn : n = 0
      · subst n
        norm_num at hj
      · simp only [a₀, if_neg hn]
    · exact hc n
    · exact hcLp n
    · exact r11b_evenModeForcing_memLp hgeom hborder (G F) hfLp n
    · exact hr₀
    · intro r hr
      have he :
          (fun t => f n t + c n t * (((2 * n : ℕ) : ℝ) ^ 2 * deriv D.w t / t)) =
          (fun t => f n t + ((2 * n : ℕ) : ℝ) ^ 2 * (deriv D.w t / t) * c n t) := by
        funext t
        simp only [div_eq_mul_inv]
        ring
      rw [← he]
      exact hflux n r hr
    · exact hsF n
    · exact hsU n
  refine ⟨c, hc, hcEq, fun n => (hnormal n).1, ?_⟩
  intro J
  have hsumA : (∑ n ∈ J, a₀ n ^ 2) ≤ a ^ 2 :=
    r11b_finite_mean_coefficient_sq_le J a
  have hforce : (∑ n ∈ J, EF n) ≤ 2 * (SF + (G F).2 ^ 2 * Bcol) :=
    hsumF J
  have hremEnergy :
      (∑ n ∈ J, (1 + ((2 * n : ℕ) : ℝ) ^ 2) * EU n) ≤
        NU + Cf ^ 2 * (SF + SD) := hsumU J
  have hnu : (G F).2 ^ 2 ≤ Cg ^ 2 * (SF + SD) :=
    (hnuN.trans hN).trans (mul_le_mul_of_nonneg_left hSFH (sq_nonneg Cg))
  have ha : a ^ 2 ≤ Cg ^ 2 * (SF + SD) :=
    (haN.trans hN).trans (mul_le_mul_of_nonneg_left hSFH (sq_nonneg Cg))
  have hNH : NU ≤ Cg ^ 2 * (SF + SD) :=
    hN.trans (mul_le_mul_of_nonneg_left hSFH (sq_nonneg Cg))
  change (∑ n ∈ J, EN n) ≤ A * (SF + SD)
  calc
    _ ≤ ∑ n ∈ J, K * (EF n + (1 + ((2 * n : ℕ) : ℝ) ^ 2) * EU n + a₀ n ^ 2) :=
      Finset.sum_le_sum fun n _ => (hnormal n).2
    _ = K * ((∑ n ∈ J, EF n) +
        (∑ n ∈ J, (1 + ((2 * n : ℕ) : ℝ) ^ 2) * EU n) +
        ∑ n ∈ J, a₀ n ^ 2) := by
      rw [← Finset.mul_sum, Finset.sum_add_distrib, Finset.sum_add_distrib]
    _ ≤ K * (2 * (SF + (G F).2 ^ 2 * Bcol) +
        (NU + Cf ^ 2 * (SF + SD)) + a ^ 2) :=
      mul_le_mul_of_nonneg_left
        (add_le_add (add_le_add hforce hremEnergy) hsumA) hK.le
    _ ≤ K * (2 * ((SF + SD) + (Cg ^ 2 * (SF + SD)) * Bcol) +
        (Cg ^ 2 * (SF + SD) + Cf ^ 2 * (SF + SD)) + Cg ^ 2 * (SF + SD)) :=
      mul_le_mul_of_nonneg_left
        (add_le_add
          (add_le_add
            (mul_le_mul_of_nonneg_left
              (add_le_add hSFH (mul_le_mul_of_nonneg_right hnu hBcol)) (by norm_num))
            (add_le_add hNH le_rfl)) ha) hK.le
    _ = A * (SF + SD) := by dsimp only [A]; ring

end ContinuousFlexibility.Radial
