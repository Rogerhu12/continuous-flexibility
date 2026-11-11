import ContinuousFlexibility.Radial.R11bWeightedModeSquares
import ContinuousFlexibility.Radial.R11bFourierCoefficients
import ContinuousFlexibility.Radial.R11bRemainderModes
import ContinuousFlexibility.Radial.ProfileScalarSquareAlgebra

/-!
# The full finite modal energy of an output remainder

The mean is controlled by ordinary weighted Bessel. Positive frequencies
also receive the actual inverse's angular frequency bound. A.e. choices of
the radial representatives preserve every scalar cell square.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open Set MeasureTheory Real
open scoped BigOperators
open ContinuousFlexibility.Statements

set_option backward.isDefEq.respectTransparency false

theorem r11b_remainder_mode_energy_bound {D : ReferenceData} (hab : D.a ≤ D.b)
    {γ M a : ℝ} {U : RadialUnknown}
    (hu : MemLp U.1 2 (radialPhysicalMeasure D))
    (hU : OutputRealization D γ M a U)
    (v : ℕ → ℝ → ℝ)
    (hv : ∀ n, v n =ᵐ[volume.restrict (radialCore D)]
      evenFourierCoefficient (outputRemainder D a U) n)
    {B : ℝ}
    (hfreq : ∀ J : Finset ℕ, (∀ n ∈ J, 0 < n) →
      (∑ n ∈ J, ((2 * n : ℕ) : ℝ) ^ 2 *
        r11bWeightedModeSquare D γ M U.1 (2 * n)) ≤ B) :
    (∀ n, Summable (fun m =>
      exp (-2 * M * radialQ (D.cellIndex m) + 2 * γ * radialS (D.cellIndex m)) *
        profileScalarCellSquare D (v n) m)) ∧
      ∀ J : Finset ℕ,
        (∑ n ∈ J, (1 + ((2 * n : ℕ) : ℝ) ^ 2) *
          (∑' m,
            exp (-2 * M * radialQ (D.cellIndex m) + 2 * γ * radialS (D.cellIndex m)) *
              profileScalarCellSquare D (v n) m)) ≤ outputNormSquare D γ M a U + B := by
  let w : ℕ → ℝ := fun k => exp (-2 * M * radialQ k + 2 * γ * radialS k)
  let E : ℕ → ℝ := fun n =>
    ∑' m, w (D.cellIndex m) * profileScalarCellSquare D (v n) m
  let E₀ : ℕ → ℝ := fun n =>
    ∑' m, w (D.cellIndex m) *
      profileScalarCellSquare D (evenFourierCoefficient (outputRemainder D a U) n) m
  have hE (n : ℕ) : E n = E₀ n :=
    profile_scalar_weighted_tsum_congr_ae w (hv n)
  have horth (i j : ℕ) :
      angularPairing (evenCosineBasis i) (evenCosineBasis j) = if i = j then 1 else 0 :=
    angularPairing_evenCosineBasis i j
  refine ⟨?_, ?_⟩
  · intro n
    change Summable (fun m => w (D.cellIndex m) * profileScalarCellSquare D (v n) m)
    apply (profile_scalar_weighted_summable_congr_ae w (hv n)).mpr
    have h := (r11b_output_weighted_finite_bessel hab ({n} : Finset ℕ)
      evenCosineBasis hU (fun i _ => evenCosineBasis_memLp_interval i)
      (fun i _ j _ => horth i j)).1 n (Finset.mem_singleton_self n)
    simpa only [w, profileScalarCellSquare, evenFourierCoefficient] using h
  · intro J
    have hb := (r11b_output_weighted_finite_bessel hab J evenCosineBasis hU
      (fun i _ => evenCosineBasis_memLp_interval i) (fun i _ j _ => horth i j)).2
    change (∑ n ∈ J, E₀ n) ≤ outputNormSquare D γ M a U at hb
    have hpos (n : ℕ) (hn : 0 < n) :
        E₀ n = r11bWeightedModeSquare D γ M U.1 (2 * n) := by
      have hcoef : evenFourierCoefficient (outputRemainder D a U) n
          =ᵐ[volume.restrict (radialCore D)] referenceMode U.1 (2 * n) := by
        rw [evenFourierCoefficient_eq_referenceMode (outputRemainder D a U) (by omega)]
        exact r11b_referenceMode_outputRemainder_ae hu a (2 * n) (by omega)
      exact profile_scalar_weighted_tsum_congr_ae w hcoef
    let Jp : Finset ℕ := J.filter (fun n => 0 < n)
    have hJp (n : ℕ) (hn : n ∈ Jp) : 0 < n := (Finset.mem_filter.mp hn).2
    have hfilter :
        (∑ n ∈ J, ((2 * n : ℕ) : ℝ) ^ 2 * E₀ n) =
          ∑ n ∈ Jp, ((2 * n : ℕ) : ℝ) ^ 2 * E₀ n := by
      dsimp only [Jp]
      rw [Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro n _
      by_cases hn : 0 < n
      · simp only [hn, ite_true]
      · have hn0 : n = 0 := Nat.eq_zero_of_not_pos hn
        subst n
        simp
    have hfb : (∑ n ∈ J, ((2 * n : ℕ) : ℝ) ^ 2 * E₀ n) ≤ B := by
      rw [hfilter]
      calc
        _ = ∑ n ∈ Jp, ((2 * n : ℕ) : ℝ) ^ 2 *
            r11bWeightedModeSquare D γ M U.1 (2 * n) := by
          apply Finset.sum_congr rfl
          intro n hn
          rw [hpos n (hJp n hn)]
        _ ≤ B := hfreq Jp hJp
    change (∑ n ∈ J, (1 + ((2 * n : ℕ) : ℝ) ^ 2) * E n) ≤ _
    calc
      _ = ∑ n ∈ J, (1 + ((2 * n : ℕ) : ℝ) ^ 2) * E₀ n := by
        apply Finset.sum_congr rfl
        intro n _
        rw [hE n]
      _ = (∑ n ∈ J, E₀ n) + ∑ n ∈ J, ((2 * n : ℕ) : ℝ) ^ 2 * E₀ n := by
        simp_rw [add_mul, one_mul]
        rw [Finset.sum_add_distrib]
      _ ≤ outputNormSquare D γ M a U + B := add_le_add hb hfb

end ContinuousFlexibility.Radial
