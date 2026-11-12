import ContinuousFlexibility.Analysis.N06MorseRootCollar
import ContinuousFlexibility.Analysis.N06RootSpeedJets

/-!
# Uniform finite jets of the actual Morse reference root speed

The two-sided collar and the positive divided profile come from the same
realized physical profile. This file discharges all primitive inputs of
the speed estimate, including reciprocal radius, height, and divided
derivative bounds. The resulting constants are selected before any root.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Real
open ContinuousFlexibility.Statements ContinuousFlexibility.Radial
open scoped ContDiff

set_option backward.isDefEq.respectTransparency false

private theorem n06_abs_iteratedDeriv_unit_shift
    (w : ℝ → ℝ) (r ι : ℝ) (hι : ι = 1 ∨ ι = -1) (k : ℕ) (t : ℝ) :
    |iteratedDeriv k (fun x => w (r + ι * x)) t| =
      |iteratedDeriv k w (r + ι * t)| := by
  rcases hι with rfl | rfl
  · simp only [one_mul, iteratedDeriv_comp_const_add]
  · simp only [neg_one_mul, ← sub_eq_add_neg, iteratedDeriv_comp_const_sub,
      smul_eq_mul, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul]

/-- The actual factored speed at both roots of every realized Morse
model has a uniform polynomial bound through order two and a polynomial
positive lower bound, on an explicitly inverse-polynomial two-sided collar. -/
theorem n06_morseRealization_referenceRootSpeed_bounds
    {T : MorseChainData} {σ : ℕ → ℝ} {D : ReferenceData} {C : ℕ → ℝ}
    (hreal : MorseChainRealization T σ D C) (hσ : ∀ n, 1 ≤ σ n ∧ σ n ≤ 2) :
    ∃ c A K P : ℝ, 0 < c ∧ 0 < A ∧ 1 ≤ K ∧ 0 < P ∧
      ∀ (side : Bool) (n : ℕ), T.index ≤ n → ∀ right : Bool,
        let r := T.radius side n
          (n06MorseOuterRoot (morseChainA T n) (morseChainB T n) right)
        let ι := n06MorseRootOrientation right
        let δ := c * radialE n ^ (-A)
        0 < δ ∧ δ ≤ 1 ∧
          ∃ g : ℝ → ℝ, ContDiff ℝ ∞ g ∧
            g 0 = |deriv (deriv D.w) r| ∧
            (∀ t : ℝ, -deriv D.w (r + ι * t) = t * g t) ∧
            ∀ t ∈ Icc (-δ) δ,
              δ ≤ g t ∧ δ ≤ D.w (r + ι * t) ∧ D.a / 2 ≤ r + ι * t ∧
                ContDiffAt ℝ ∞ (referenceRootSpeedFactor D.w g r ι) t ∧
                0 < referenceRootSpeedFactor D.w g r ι t ∧
                N06ScalarJetTwoBound (referenceRootSpeedFactor D.w g r ι) t
                  (K * radialE n ^ P) ∧
                (referenceRootSpeedFactor D.w g r ι t)⁻¹ ≤ K * radialE n ^ P := by
  obtain ⟨M, c, A, hM, hc, hA, hcollar⟩ :=
    n06_morseRealization_root_division_collar hreal hσ
  let B₀ : ℝ := max 1 (max M (max (D.b + 1) (max (2 / D.a) c⁻¹)))
  have hB₀ : 1 ≤ B₀ := le_max_left _ _
  have hB₀0 : 0 ≤ B₀ := zero_le_one.trans hB₀
  have hMB : M ≤ B₀ := (le_max_left _ _).trans (le_max_right _ _)
  have hbB : D.b + 1 ≤ B₀ :=
    ((le_max_left _ _).trans (le_max_right _ _)).trans (le_max_right _ _)
  have haB : 2 / D.a ≤ B₀ :=
    (((le_max_left _ _).trans (le_max_right _ _)).trans
      (le_max_right _ _)).trans (le_max_right _ _)
  have hcB : c⁻¹ ≤ B₀ :=
    (((le_max_right _ _).trans (le_max_right _ _)).trans
      (le_max_right _ _)).trans (le_max_right _ _)
  let K : ℝ := (36 * (48 : ℝ) ^ 5) * B₀ ^ 40
  let P : ℝ := A * 40
  have hK : 1 ≤ K := by
    have hp : 1 ≤ B₀ ^ 40 := one_le_pow₀ hB₀
    dsimp only [K]
    nlinarith
  have hP : 0 < P := mul_pos hA (by norm_num)
  refine ⟨c, A, K, P, hc, hA, hK, hP, ?_⟩
  intro side n hn right
  let r := T.radius side n
    (n06MorseOuterRoot (morseChainA T n) (morseChainB T n) right)
  let ι := n06MorseRootOrientation right
  let δ := c * radialE n ^ (-A)
  let B : ℝ := B₀ * radialE n ^ A
  have hE : 1 ≤ radialE n := one_le_exp_iff.mpr (radialQ_nonneg n)
  have hEp : 0 < radialE n := zero_lt_one.trans_le hE
  have hEA : 1 ≤ radialE n ^ A := Real.one_le_rpow hE hA.le
  have hB₀B : B₀ ≤ B := le_mul_of_one_le_right hB₀0 hEA
  have hB : 1 ≤ B := hB₀.trans hB₀B
  have hδinv : δ⁻¹ ≤ B := by
    calc
      δ⁻¹ = c⁻¹ * radialE n ^ A := by
        dsimp only [δ]
        rw [mul_inv_rev, Real.rpow_neg hEp.le, inv_inv]
        ring
      _ ≤ B₀ * radialE n ^ A :=
        mul_le_mul_of_nonneg_right hcB (Real.rpow_nonneg hEp.le A)
  have hcost : (36 * (48 : ℝ) ^ 5) * B ^ 40 = K * radialE n ^ P := by
    dsimp only [B, K, P]
    rw [mul_pow, ← Real.rpow_mul_natCast hEp.le A 40]
    norm_num only [Nat.cast_ofNat]
    ring
  obtain ⟨hδ, hδ1, hδa, g, hg, hg0, hfactor, hgb⟩ := hcollar side n hn right
  have hr := (n06_morseRealization_root_profile_data hreal hσ side hn right).1
  have hι := n06_morseRootOrientation_unit right
  have hιabs : |ι| = 1 := by
    rcases hι with h | h <;> change ι = _ at h <;> rw [h] <;> norm_num
  refine ⟨hδ, hδ1, g, hg, hg0, hfactor, ?_⟩
  intro t ht
  obtain ⟨hgt, hwt, hrt, hgjet, hwjet⟩ := hgb t ht
  have hgp : 0 < g t := hδ.trans_le hgt
  have hwp : 0 < D.w (r + ι * t) := hδ.trans_le hwt
  have hrp : 0 < r + ι * t := (half_pos hreal.geometry.1).trans_le hrt
  have hrtB : |r + ι * t| ≤ B := by
    have ht1 : |t| ≤ 1 := (abs_le.mpr ht).trans hδ1
    have hshift : ι * t ≤ 1 := by
      calc
        ι * t ≤ |ι * t| := le_abs_self _
        _ = |t| := by rw [abs_mul, hιabs, one_mul]
        _ ≤ 1 := ht1
    rw [abs_of_pos hrp]
    exact (show r + ι * t ≤ D.b + 1 by linarith only [hr.2, hshift]).trans
      (hbB.trans hB₀B)
  have hri : (r + ι * t)⁻¹ ≤ B := by
    calc
      (r + ι * t)⁻¹ ≤ (D.a / 2)⁻¹ := inv_anti₀ (half_pos hreal.geometry.1) hrt
      _ = 2 / D.a := inv_div _ _
      _ ≤ B := haB.trans hB₀B
  have hwi : (D.w (r + ι * t))⁻¹ ≤ B :=
    (inv_anti₀ hδ hwt).trans hδinv
  have hgi : (g t)⁻¹ ≤ B := (inv_anti₀ hδ hgt).trans hδinv
  have hWjet : N06ScalarJetTwoBound (fun x => D.w (r + ι * x)) t B := by
    apply n06_scalarJetTwoBound_iff.mpr
    intro k hk
    rw [n06_abs_iteratedDeriv_unit_shift D.w r ι hι]
    exact (hwjet k (by omega)).trans (hMB.trans hB₀B)
  have hGjet := hgjet.mono (hMB.trans hB₀B)
  obtain ⟨hcs, hcp, hcjet, hci⟩ := n06_referenceRootSpeedFactor_twoJet
    hreal.geometry.2.2.1.1 hg r ι t B hι hB hrp hwp hgp hrtB hri hWjet hwi hGjet hgi
  rw [hcost] at hcjet hci
  exact ⟨hgt, hwt, hrt, hcs, hcp, hcjet, hci⟩

end ContinuousFlexibility.Analysis
