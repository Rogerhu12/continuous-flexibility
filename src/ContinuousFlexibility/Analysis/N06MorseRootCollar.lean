import ContinuousFlexibility.Analysis.N06ReferenceRootDivision
import ContinuousFlexibility.Analysis.N06MorseJoinFloor
import ContinuousFlexibility.Radial.ScaleSlowVariation

/-!
# Polynomial collars of the actual reference turning roots

The orientation points into the original negative component. The divided
profile is the genuine smooth division of `-w'`, and its value at the root
is the absolute value of the actual physical curvature. A single compact
bound for the ordinary profile jets and the previously proved curvature
lower bound select an explicit inverse-polynomial collar on both sides.
No root-coordinate or endpoint-jet estimate is an input.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Real
open ContinuousFlexibility.Statements ContinuousFlexibility.Radial
open scoped ContDiff

set_option backward.isDefEq.respectTransparency false

def n06MorseRootOrientation (right : Bool) : ℝ := if right then -1 else 1

theorem n06_morseRootOrientation_unit (right : Bool) :
    n06MorseRootOrientation right = 1 ∨ n06MorseRootOrientation right = -1 := by
  cases right
  · exact Or.inl rfl
  · exact Or.inr rfl

/-- The same realized roots have zero first derivative, the correct
oriented curvature, and the original coefficient-power height floor. -/
theorem n06_morseRealization_root_profile_data
    {T : MorseChainData} {σ : ℕ → ℝ} {D : ReferenceData} {C : ℕ → ℝ}
    (hreal : MorseChainRealization T σ D C) (hσ : ∀ n, 1 ≤ σ n ∧ σ n ≤ 2)
    (side : Bool) {n : ℕ} (hn : T.index ≤ n) (right : Bool) :
    let x := n06MorseOuterRoot (morseChainA T n) (morseChainB T n) right
    let r := T.radius side n x
    r ∈ radialCore D ∧ deriv D.w r = 0 ∧
      -n06MorseRootOrientation right * deriv (deriv D.w) r =
        |deriv (deriv D.w) r| ∧
      (C 0)⁻¹ * radialE n ^ (-C 0) ≤ D.w r := by
  let x := n06MorseOuterRoot (morseChainA T n) (morseChainB T n) right
  let r := T.radius side n x
  let ι := n06MorseRootOrientation right
  have hp := hreal.retained_data side n hn
  have hx : morseRho (morseChainA T n) (morseChainB T n) x = 0 :=
    n06_morseOuterRoot_zero hp.1 hp.2.1 right
  have hxi := n06_morseRealization_root_mem_Ioo hreal side hn hx
  have hxc : x ∈ Icc (T.leftX side n) (T.rightX side n) := ⟨hxi.1.le, hxi.2.le⟩
  have hr : r ∈ radialCore D := hreal.radius_mem_core side n hn x hxc
  have hv : 0 < deriv (T.radius side n) x := hreal.derivative_positive side n hn x hxc
  have hz : deriv D.w r = 0 := by
    have he := morseRealization_profile_deriv_scaled hreal side hn hxc
    rw [hx, neg_zero, zero_mul, mul_zero] at he
    exact (mul_eq_zero.mp he).resolve_right hv.ne'
  have hρ : 0 < ι * deriv (morseRho (morseChainA T n) (morseChainB T n)) x := by
    cases right with
    | false =>
        simpa only [ι, x, n06MorseRootOrientation, n06MorseOuterRoot,
          Bool.false_eq_true, ↓reduceIte, one_mul] using
          morseRho_deriv_left_turn_pos hp.1 hp.2.1
    | true =>
        simpa only [ι, x, n06MorseRootOrientation, n06MorseOuterRoot,
          ↓reduceIte, neg_one_mul] using
          neg_pos.mpr (morseRho_deriv_right_turn_neg hp.1 hp.2.1)
  have hcurv : 0 < -ι * deriv (deriv D.w) r := by
    rw [n06_morseRealization_profile_second_deriv_at_root hreal side hn hx]
    have he : -ι * (-morseChainAmplitude T σ n *
        deriv (morseRho (morseChainA T n) (morseChainB T n)) x * r /
          deriv (T.radius side n) x ^ 2) =
        morseChainAmplitude T σ n *
          (ι * deriv (morseRho (morseChainA T n) (morseChainB T n)) x) * r /
            deriv (T.radius side n) x ^ 2 := by ring
    rw [he]
    exact div_pos (mul_pos (mul_pos (morseChainAmplitude_pos T σ hσ n) hρ)
      (hreal.geometry.1.trans hr.1)) (sq_pos_of_pos hv)
  have hιabs : |ι| = 1 := by
    rcases n06_morseRootOrientation_unit right with h | h <;>
      change ι = _ at h <;> rw [h] <;> norm_num
  have habs : -ι * deriv (deriv D.w) r = |deriv (deriv D.w) r| := by
    calc
      -ι * deriv (deriv D.w) r = |-ι * deriv (deriv D.w) r| :=
        (abs_of_pos hcurv).symm
      _ = |deriv (deriv D.w) r| := by rw [abs_mul, abs_neg, hιabs, one_mul]
  obtain ⟨m, hm, hrm⟩ := hreal.2.2.2.2.2.2.2.2.1 side n hn r
    (morseRealization_model_subset_block hreal side hn ⟨x, hxc, rfl⟩)
  refine ⟨hr, hz, habs, ?_⟩
  simpa only [hm] using n06_accumulatingProfile_cell_lower hreal.accumulating m hrm

private theorem n06_profile_four_jets_bounded
    {w : ℝ → ℝ} (hw : ContDiff ℝ ∞ w) (a b : ℝ) :
    ∃ M : ℝ, 1 ≤ M ∧ ∀ k : ℕ, k ≤ 4 → ∀ r ∈ Icc a b,
      |iteratedDeriv k w r| ≤ M := by
  let f : ℝ → Fin 5 → ℝ := fun r i => iteratedDeriv i.val w r
  have hf : Continuous f := continuous_pi fun i =>
    hw.continuous_iteratedDeriv i.val (by simp)
  obtain ⟨M₀, hM₀⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (hf.continuousOn : ContinuousOn f (Icc a b))
  refine ⟨max 1 M₀, le_max_left _ _, ?_⟩
  intro k hk r hr
  have hnorm := norm_le_pi_norm (f r) (⟨k, by omega⟩ : Fin 5)
  have hb : |iteratedDeriv k w r| ≤ ‖f r‖ := by
    simpa only [f, Real.norm_eq_abs] using hnorm
  exact hb.trans ((hM₀ r hr).trans (le_max_right _ _))

/-- A true two-sided collar of every actual Morse root, with one
coefficient-power width chosen before the root and model index. On it the
same divided profile and physical height have that width as a lower bound,
and their ordinary jets come from the original profile, through order four.
This is the raw physical input for the Airy speed and endpoint primitives. -/
theorem n06_morseRealization_root_division_collar
    {T : MorseChainData} {σ : ℕ → ℝ} {D : ReferenceData} {C : ℕ → ℝ}
    (hreal : MorseChainRealization T σ D C) (hσ : ∀ n, 1 ≤ σ n ∧ σ n ≤ 2) :
    ∃ M c A : ℝ, 1 ≤ M ∧ 0 < c ∧ 0 < A ∧
      ∀ (side : Bool) (n : ℕ), T.index ≤ n → ∀ right : Bool,
        let r := T.radius side n
          (n06MorseOuterRoot (morseChainA T n) (morseChainB T n) right)
        let ι := n06MorseRootOrientation right
        let δ := c * radialE n ^ (-A)
        0 < δ ∧ δ ≤ 1 ∧ δ ≤ D.a / 2 ∧
          ∃ g : ℝ → ℝ, ContDiff ℝ ∞ g ∧
            g 0 = |deriv (deriv D.w) r| ∧
            (∀ t : ℝ, -deriv D.w (r + ι * t) = t * g t) ∧
            ∀ t ∈ Icc (-δ) δ,
              δ ≤ g t ∧ δ ≤ D.w (r + ι * t) ∧ D.a / 2 ≤ r + ι * t ∧
                N06ScalarJetTwoBound g t M ∧
                ∀ k : ℕ, k ≤ 4 → |iteratedDeriv k D.w (r + ι * t)| ≤ M := by
  have hw : ContDiff ℝ ∞ D.w := hreal.geometry.2.2.1.1
  obtain ⟨M, hM, hjet⟩ := n06_profile_four_jets_bounded hw (D.a - 1) (D.b + 1)
  obtain ⟨croot, hcroot, hroot⟩ := n06_morseRealization_root_curvature_lower hreal hσ
  have hMp : 0 < M := zero_lt_one.trans_le hM
  have ha : 0 < D.a := hreal.geometry.1
  have hC : 0 < C 0 := hreal.constants_pos 0
  let A : ℝ := max 12 (C 0)
  let c : ℝ := min 1 (min (D.a / 2)
    (min (croot / (2 * M)) ((C 0)⁻¹ / (2 * M))))
  have hc : 0 < c := lt_min zero_lt_one (lt_min (half_pos ha)
    (lt_min (div_pos hcroot (mul_pos (by norm_num) hMp))
      (div_pos (inv_pos.mpr hC) (mul_pos (by norm_num) hMp))))
  have hc1 : c ≤ 1 := min_le_left _ _
  have hca : c ≤ D.a / 2 := (min_le_right _ _).trans (min_le_left _ _)
  have hcr : c ≤ croot / (2 * M) :=
    ((min_le_right _ _).trans (min_le_right _ _)).trans (min_le_left _ _)
  have hcw : c ≤ (C 0)⁻¹ / (2 * M) :=
    ((min_le_right _ _).trans (min_le_right _ _)).trans (min_le_right _ _)
  have hcMr : 2 * M * c ≤ croot := by
    have h := (le_div_iff₀ (mul_pos (by norm_num : (0 : ℝ) < 2) hMp)).mp hcr
    nlinarith only [h]
  have hcMw : 2 * M * c ≤ (C 0)⁻¹ := by
    have h := (le_div_iff₀ (mul_pos (by norm_num : (0 : ℝ) < 2) hMp)).mp hcw
    nlinarith only [h]
  have hA : 0 < A := (by norm_num : (0 : ℝ) < 12).trans_le (le_max_left _ _)
  refine ⟨M, c, A, hM, hc, hA, ?_⟩
  intro side n hn right
  let x := n06MorseOuterRoot (morseChainA T n) (morseChainB T n) right
  let r := T.radius side n x
  let ι := n06MorseRootOrientation right
  let p : ℝ := radialE n ^ (-A)
  let δ : ℝ := c * p
  have hE : 1 ≤ radialE n := one_le_exp_iff.mpr (radialQ_nonneg n)
  have hp : 0 < p := Real.rpow_pos_of_pos (zero_lt_one.trans_le hE) _
  have hp1 : p ≤ 1 := by
    simpa only [Real.rpow_zero] using
      Real.rpow_le_rpow_of_exponent_le hE (neg_nonpos.mpr hA.le)
  have hδ : 0 < δ := mul_pos hc hp
  have hδc : δ ≤ c := by simpa only [mul_one] using mul_le_mul_of_nonneg_left hp1 hc.le
  have hδ1 : δ ≤ 1 := hδc.trans hc1
  have hδa : δ ≤ D.a / 2 := hδc.trans hca
  have hp12 : p ≤ radialE n ^ (-12 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le hE (neg_le_neg (le_max_left _ _))
  have hpC : p ≤ radialE n ^ (-C 0) :=
    Real.rpow_le_rpow_of_exponent_le hE (neg_le_neg (le_max_right _ _))
  obtain ⟨hr, hz, hsign, hw0⟩ := n06_morseRealization_root_profile_data hreal hσ side hn right
  have hxzero := n06_morseOuterRoot_zero (hreal.retained_data side n hn).1
    (hreal.retained_data side n hn).2.1 right
  have hcurv : croot * radialE n ^ (-12 : ℝ) ≤ |deriv (deriv D.w) r| :=
    hroot side n hn x hxzero
  have hlocal (k : ℕ) (hk : k ≤ 4) (y : ℝ) (hy : y ∈ Icc (r - 1) (r + 1)) :
      |iteratedDeriv k D.w y| ≤ M :=
    hjet k hk y ⟨by linarith only [hr.1, hy.1], by linarith only [hr.2, hy.2]⟩
  obtain ⟨g, hg, hg0, hfactor, hgb⟩ := n06_exists_reference_root_division
    hw r ι (n06_morseRootOrientation_unit right) hz
  have hgabs : g 0 = |deriv (deriv D.w) r| := hg0.trans hsign
  have hδg : 2 * M * δ ≤ g 0 := by
    calc
      2 * M * δ = (2 * M * c) * p := by dsimp only [δ]; ring
      _ ≤ croot * p := mul_le_mul_of_nonneg_right hcMr hp.le
      _ ≤ croot * radialE n ^ (-12 : ℝ) := mul_le_mul_of_nonneg_left hp12 hcroot.le
      _ ≤ g 0 := by rw [hgabs]; exact hcurv
  have hδw : 2 * M * δ ≤ D.w r := by
    calc
      2 * M * δ = (2 * M * c) * p := by dsimp only [δ]; ring
      _ ≤ (C 0)⁻¹ * p := mul_le_mul_of_nonneg_right hcMw hp.le
      _ ≤ (C 0)⁻¹ * radialE n ^ (-C 0) :=
        mul_le_mul_of_nonneg_left hpC (inv_nonneg.mpr hC.le)
      _ ≤ D.w r := hw0
  refine ⟨hδ, hδ1, hδa, g, hg, hgabs, hfactor, ?_⟩
  intro t ht
  have ht1 : t ∈ Icc (-1 : ℝ) 1 :=
    ⟨(neg_le_neg hδ1).trans ht.1, ht.2.trans hδ1⟩
  have htδ : |t| ≤ δ := abs_le.mpr ht
  obtain ⟨hgjet, hgdiff, hwdiff⟩ := hgb M hM hlocal t ht1
  have hvariation : M * |t| ≤ M * δ := mul_le_mul_of_nonneg_left htδ hMp.le
  have hMδ : δ ≤ M * δ := by
    simpa only [one_mul] using mul_le_mul_of_nonneg_right hM hδ.le
  have hιabs : |ι| = 1 := by
    rcases n06_morseRootOrientation_unit right with h | h <;>
      change ι = _ at h <;> rw [h] <;> norm_num
  have hshift : |ι * t| ≤ δ := by simpa only [abs_mul, hιabs, one_mul] using htδ
  have hshift' := abs_le.mp hshift
  refine ⟨?_, ?_, ?_, hgjet, ?_⟩
  · have h := (abs_le.mp (hgdiff.trans hvariation)).1
    linarith only [hδg, hMδ, h]
  · have h := (abs_le.mp (hwdiff.trans hvariation)).1
    linarith only [hδw, hMδ, h]
  · linarith only [hr.1, hδa, hshift'.1]
  · intro k hk
    exact hlocal k hk _ ⟨by linarith only [hshift'.1, hδ1],
      by linarith only [hshift'.2, hδ1]⟩

end ContinuousFlexibility.Analysis
