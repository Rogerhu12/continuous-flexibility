import ContinuousFlexibility.Radial.R11bEvenWeightedBessel
import ContinuousFlexibility.Radial.R11bEvenModeRegularity
import ContinuousFlexibility.Radial.R11bRadialCorrections
import ContinuousFlexibility.Radial.ProfileScalarSquareAlgebra

/-!
# Weighted source bounds for the actual even-mode forcing

The column occurs only in mode one. Its finite coefficient-square sum is
bounded by the single physical scalar row, independently of the number of
modes. The coefficient part is controlled by actual weighted cell Bessel.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open Set MeasureTheory Real
open scoped BigOperators
open ContinuousFlexibility.Statements ContinuousFlexibility.Analysis

theorem r11b_finite_critical_coefficient_sq_le (J : Finset ℕ) (c : ℝ) :
    (∑ n ∈ J, (if n = 1 then c else 0) ^ 2) ≤ c ^ 2 := by
  by_cases h1 : 1 ∈ J
  · have he : (∑ n ∈ J, (if n = 1 then c else 0) ^ 2) = c ^ 2 := by
      calc
        _ = (if (1 : ℕ) = 1 then c else 0) ^ 2 :=
          Finset.sum_eq_single 1
            (fun n _ hn => by simp only [if_neg hn, zero_pow (by decide : (2 : ℕ) ≠ 0)])
            (fun hn => (hn h1).elim)
        _ = c ^ 2 := by rw [if_pos rfl]
    exact he.le
  · calc
      _ = 0 := by
        apply Finset.sum_eq_zero
        intro n hn
        have hn1 : n ≠ 1 := by
          intro heq
          subst n
          exact h1 hn
        simp only [if_neg hn1, zero_pow (by decide : (2 : ℕ) ≠ 0)]
      _ ≤ c ^ 2 := sq_nonneg c

theorem r11b_scalar_column_forcing_weighted {D : ReferenceData}
    (w : ℕ → ℝ) (hw : ∀ n, 0 ≤ w n) (f g : ℝ → ℝ) (c : ℝ)
    (hflocal : ∀ m, MemLp (fun r => D.localizer m r * f r) 2
      (volume.restrict (radialCore D)))
    (hglocal : ∀ m, MemLp (fun r => D.localizer m r * g r) 2
      (volume.restrict (radialCore D)))
    (hf : Summable (fun m => w (D.cellIndex m) * profileScalarCellSquare D f m))
    (hg : Summable (fun m => w (D.cellIndex m) * profileScalarCellSquare D g m)) :
    Summable (fun m => w (D.cellIndex m) *
      profileScalarCellSquare D (fun r => f r - c * g r) m) ∧
      (∑' m, w (D.cellIndex m) *
        profileScalarCellSquare D (fun r => f r - c * g r) m) ≤
        2 * ((∑' m, w (D.cellIndex m) * profileScalarCellSquare D f m) +
          c ^ 2 * ∑' m, w (D.cellIndex m) * profileScalarCellSquare D g m) := by
  obtain ⟨hcs, hceq⟩ := profile_scalar_weighted_const_mul w c hg
  have hclocal (m : ℕ) :
      MemLp (fun r => D.localizer m r * (c * g r)) 2
        (volume.restrict (radialCore D)) := by
    apply MemLp.ae_eq _ ((hglocal m).const_mul c)
    exact Filter.Eventually.of_forall fun r => by ring
  obtain ⟨hs, hbound⟩ := profile_scalar_weighted_sub w hw hflocal hclocal hf hcs
  refine ⟨hs, ?_⟩
  rwa [hceq] at hbound

theorem r11b_evenModeForcing_source_bound {D : ReferenceData}
    (hD : IsAccumulatingProfile D) (hborder : RadialTrueBorder D)
    {G : RadialModePair D →L[ℝ] RadialModePair D} {Mdata : RadialMatchingData D}
    (hMatch : ActualMatchedRepresentation D G Mdata)
    {γ M : ℝ} {F : RadialSource} (hF : SourceMember D γ M F) (U : RadialUnknown) :
    (∀ n, Summable (fun m =>
      exp (2 * M * radialQ (D.cellIndex m) + 2 * γ * radialS (D.cellIndex m)) *
        profileScalarCellSquare D (r11bEvenModeForcing D U F n) m)) ∧
      ∀ J : Finset ℕ,
        (∑ n ∈ J, ∑' m,
          exp (2 * M * radialQ (D.cellIndex m) + 2 * γ * radialS (D.cellIndex m)) *
            profileScalarCellSquare D (r11bEvenModeForcing D U F n) m) ≤
          2 * (sourceNormSquare D γ M F + U.2 ^ 2 *
            ∑' m, exp
              (2 * M * radialQ (D.cellIndex m) + 2 * γ * radialS (D.cellIndex m)) *
                profileScalarCellSquare D (referenceColumn D) m) := by
  let w : ℕ → ℝ := fun k => exp (2 * M * radialQ k + 2 * γ * radialS k)
  have hw (k : ℕ) : 0 ≤ w k := (exp_pos _).le
  have hgeom : RadialProfileGeometry D := hD.choose_spec.1
  have hpart : RadialPartition D := hD.choose_spec.2.1
  obtain ⟨hfs, hfbound⟩ := r11b_source_evenCoefficient_bounds hgeom.2.1.le hF
  have hgs : Summable (fun m => w (D.cellIndex m) *
      profileScalarCellSquare D (referenceColumn D) m) :=
    r11b_referenceColumn_scalar_source_summable hD hborder hMatch γ M
  have hgLp : MemLp (referenceColumn D) 2 (volume.restrict (radialCore D)) :=
    interval_memLp_of_continuous (r11b_continuous_referenceColumn hgeom hborder)
  have hglocal (m : ℕ) :
      MemLp (fun r => D.localizer m r * referenceColumn D r) 2
        (volume.restrict (radialCore D)) :=
    profile_memLp_localizer_mul hpart hgLp m
  have hsingle (n : ℕ) :
      Summable (fun m => w (D.cellIndex m) *
        profileScalarCellSquare D (r11bEvenModeForcing D U F n) m) ∧
        (∑' m, w (D.cellIndex m) *
          profileScalarCellSquare D (r11bEvenModeForcing D U F n) m) ≤
          2 * ((∑' m, w (D.cellIndex m) *
            profileScalarCellSquare D (evenFourierCoefficient F.1 n) m) +
            (if n = 1 then U.2 else 0) ^ 2 *
              ∑' m, w (D.cellIndex m) * profileScalarCellSquare D (referenceColumn D) m) :=
    r11b_scalar_column_forcing_weighted w hw (evenFourierCoefficient F.1 n)
      (referenceColumn D) (if n = 1 then U.2 else 0)
      (fun m => r11b_evenCoefficient_localized_memLp hF.1 n m) hglocal (hfs n) hgs
  have hB : 0 ≤ ∑' m, w (D.cellIndex m) *
      profileScalarCellSquare D (referenceColumn D) m :=
    tsum_nonneg fun m => mul_nonneg (hw _) (profileScalarCellSquare_nonneg D _ m)
  refine ⟨fun n => (hsingle n).1, fun J => ?_⟩
  calc
    (∑ n ∈ J, ∑' m, w (D.cellIndex m) *
        profileScalarCellSquare D (r11bEvenModeForcing D U F n) m) ≤
        ∑ n ∈ J, 2 * ((∑' m, w (D.cellIndex m) *
          profileScalarCellSquare D (evenFourierCoefficient F.1 n) m) +
          (if n = 1 then U.2 else 0) ^ 2 *
            ∑' m, w (D.cellIndex m) * profileScalarCellSquare D (referenceColumn D) m) :=
      Finset.sum_le_sum fun n _ => (hsingle n).2
    _ = 2 * ((∑ n ∈ J, ∑' m, w (D.cellIndex m) *
          profileScalarCellSquare D (evenFourierCoefficient F.1 n) m) +
        (∑ n ∈ J, (if n = 1 then U.2 else 0) ^ 2) *
          ∑' m, w (D.cellIndex m) * profileScalarCellSquare D (referenceColumn D) m) := by
      simp only [mul_add, Finset.mul_sum, Finset.sum_mul, Finset.sum_add_distrib]
    _ ≤ 2 * (sourceNormSquare D γ M F + U.2 ^ 2 *
        ∑' m, w (D.cellIndex m) * profileScalarCellSquare D (referenceColumn D) m) :=
      mul_le_mul_of_nonneg_left
        (add_le_add (hfbound J)
          (mul_le_mul_of_nonneg_right (r11b_finite_critical_coefficient_sq_le J U.2) hB))
        (by norm_num)

end ContinuousFlexibility.Radial
