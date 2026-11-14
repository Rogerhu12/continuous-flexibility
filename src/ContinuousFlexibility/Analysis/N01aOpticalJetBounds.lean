module

public import ContinuousFlexibility.Analysis.N01aOpticalSupport
public import ContinuousFlexibility.Analysis.WeightedJetComposition

/-!
# Finite jet bounds for the actual interior control

The fixed cutoff contributes a constant depending only on the requested
derivative order. All dependence on the optical profile is displayed
through a finite bound for its actual radicand jets and the cutoff scale.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Statements

open Set Filter MeasureTheory
open scoped ContDiff Topology BigOperators

theorem n01aOpticalCutoff_finiteJet_bound (s : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ k ≤ s, ∀ x : ℝ, |iteratedDeriv k n01aOpticalCutoff x| ≤ C := by
  induction s with
  | zero =>
      obtain ⟨C, hC, hbound⟩ := n01aOpticalCutoff_jet_bound 0
      refine ⟨C, hC, fun k hk x => ?_⟩
      have hk0 : k = 0 := Nat.eq_zero_of_le_zero hk
      simpa only [hk0] using hbound x
  | succ s ih =>
      obtain ⟨A, hA, ha⟩ := ih
      obtain ⟨B, hB, hb⟩ := n01aOpticalCutoff_jet_bound (s + 1)
      refine ⟨A + B, add_pos hA hB, fun k hk x => ?_⟩
      by_cases hks : k ≤ s
      · exact (ha k hks x).trans (le_add_of_nonneg_right hB.le)
      · have heq : k = s + 1 := by omega
        subst k
        exact (hb x).trans (le_add_of_nonneg_left hA.le)

theorem n01aOpticalCutoff_composition_jet_bound {q : ℝ → ℝ} {U : Set ℝ}
    (hU : IsOpen U) (hq : ContDiffOn ℝ ∞ q U) {r : ℝ} (hr : r ∈ U)
    {δ K C : ℝ} (hδ : 0 < δ) (hK : 0 ≤ K) (s : ℕ)
    (hcutoff : ∀ k ≤ s, ∀ x : ℝ, |iteratedDeriv k n01aOpticalCutoff x| ≤ C)
    (hjets : ∀ k, 1 ≤ k → k ≤ s → |iteratedDeriv k q r| ≤ K) :
    |iteratedDeriv s (fun x => n01aOpticalCutoff (q x / δ)) r| ≤
      (s.factorial : ℝ) * C * (1 + K / δ) ^ s := by
  have hD : 1 ≤ 1 + K / δ := le_add_of_nonneg_right (div_nonneg hK hδ.le)
  have houter : ∀ k ≤ s,
      ‖iteratedFDeriv ℝ k n01aOpticalCutoff (q r / δ)‖ ≤ C * (1 : ℝ) ^ (s - k) := by
    intro k hk
    simpa only [norm_iteratedFDeriv_eq_norm_iteratedDeriv, Real.norm_eq_abs,
      one_pow, mul_one] using hcutoff k hk (q r / δ)
  have hinner : ∀ k, 1 ≤ k → k ≤ s →
      ‖iteratedFDeriv ℝ k (fun x => q x / δ) r‖ ≤
        (1 : ℝ) * ((1 + K / δ) / 1) ^ k := by
    intro k hk hks
    rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv, Real.norm_eq_abs,
      iteratedDeriv_div_const, abs_div, abs_of_pos hδ, div_one, one_mul]
    calc
      |iteratedDeriv k q r| / δ ≤ K / δ := div_le_div_of_nonneg_right (hjets k hk hks) hδ.le
      _ ≤ 1 + K / δ := le_add_of_nonneg_left zero_le_one
      _ ≤ (1 + K / δ) ^ k := le_self_pow₀ hD (by omega)
  have hcomp := Analysis.norm_iteratedFDeriv_comp_le_weighted hU (hq.div_const δ)
    contDiff_n01aOpticalCutoff hr zero_lt_one s houter hinner
  simpa only [norm_iteratedFDeriv_eq_norm_iteratedDeriv, Real.norm_eq_abs,
    Function.comp_def] using hcomp

/-- A single finite radicand-jet bound controls the actual extended control
at every point of the line, including both endpoints and the exterior. -/
theorem n01aOpticalRawControl_finiteJet_bound (s : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ {w : ℝ → ℝ} {l h δ K β : ℝ},
      0 < l → 0 < δ → 0 ≤ K → 0 ≤ β → h ≤ β → ContDiff ℝ ∞ w →
      (∀ r ∈ Icc l h, 0 < w r) → deriv w l = 0 → deriv w h = 0 →
      (∀ k ≤ s, ∀ r ∈ Icc l h, |iteratedDeriv k (n01aOpticalRadicand w) r| ≤ K) →
      ∀ r : ℝ, |iteratedDeriv s (n01aOpticalRawControl w l h δ) r| ≤
        C * (1 + β) * (1 + K / δ) ^ s := by
  classical
  obtain ⟨F, hF, hcutoff⟩ := n01aOpticalCutoff_finiteJet_bound s
  let A : ℝ := ∑ k ∈ Finset.range (s + 1), (s.choose k : ℝ)
  have hA : 0 ≤ A := Finset.sum_nonneg fun k hk => Nat.cast_nonneg _
  let C : ℝ := (A + 1) * (s.factorial : ℝ) * F
  have hfactorial : 0 < (s.factorial : ℝ) := Nat.cast_pos.mpr (Nat.factorial_pos s)
  have hC : 0 < C := mul_pos (mul_pos (by linarith) hfactorial) hF
  refine ⟨C, hC, ?_⟩
  intro w l h δ K β hl hδ hK hβ hhβ hw hpos hrootL hrootR hjets r
  have hD : 1 ≤ 1 + K / δ := le_add_of_nonneg_right (div_nonneg hK hδ.le)
  by_cases hr : r ∈ Ioo l h
  · have hq : ContDiffOn ℝ ∞ (n01aOpticalRadicand w) (Ioo l h) :=
      fun x hx => (contDiffAt_n01aOpticalRadicand hw
        (hl.trans hx.1).ne' (hpos x (Ioo_subset_Icc_self hx)).ne').contDiffWithinAt
    have hg : ContDiffAt ℝ ∞
        (fun x => n01aOpticalCutoff (n01aOpticalRadicand w x / δ)) r :=
      contDiff_n01aOpticalCutoff.contDiffAt.comp r
        (((hq r hr).contDiffAt (isOpen_Ioo.mem_nhds hr)).div_const δ)
    let B : ℝ := (s.factorial : ℝ) * F * (1 + K / δ) ^ s
    have hB : 0 ≤ B := mul_nonneg (mul_nonneg hfactorial.le hF.le)
      (pow_nonneg (zero_le_one.trans hD) _)
    have hgBound : ∀ k ≤ s,
        |iteratedDeriv k (fun x => n01aOpticalCutoff (n01aOpticalRadicand w x / δ)) r| ≤ B := by
      intro k hk
      have hkBound := n01aOpticalCutoff_composition_jet_bound isOpen_Ioo hq hr hδ hK k
        (fun j hj x => hcutoff j (hj.trans hk) x)
        (fun j hj hjk => hjets j (hjk.trans hk) r (Ioo_subset_Icc_self hr))
      have hfac : (k.factorial : ℝ) ≤ (s.factorial : ℝ) :=
        Nat.cast_le.mpr (Nat.factorial_le hk)
      exact hkBound.trans (mul_le_mul
        (mul_le_mul_of_nonneg_right hfac hF.le) (pow_le_pow_right₀ hD hk)
        (pow_nonneg (zero_le_one.trans hD) _)
        (mul_nonneg hfactorial.le hF.le))
    have hidBound : ∀ k : ℕ, |iteratedDeriv k (fun x : ℝ => x) r| ≤ 1 + β := by
      intro k
      rw [iteratedDeriv_fun_id]
      split_ifs
      · rw [abs_of_pos (hl.trans hr.1)]
        linarith [hr.2.trans_le hhβ]
      · simpa only [abs_one] using (le_add_of_nonneg_right hβ : (1 : ℝ) ≤ 1 + β)
      · simpa only [abs_zero] using (show (0 : ℝ) ≤ 1 + β by linarith)
    have hmul : iteratedDeriv s
        (fun x => x * n01aOpticalCutoff (n01aOpticalRadicand w x / δ)) r =
        ∑ k ∈ Finset.range (s + 1), (s.choose k : ℝ) *
          iteratedDeriv k (fun x : ℝ => x) r *
          iteratedDeriv (s - k) (fun x => n01aOpticalCutoff (n01aOpticalRadicand w x / δ)) r := by
      simpa only [id_eq] using
        (iteratedDeriv_fun_mul (f := fun x : ℝ => x)
          (g := fun x => n01aOpticalCutoff (n01aOpticalRadicand w x / δ))
          (contDiffAt_id : ContDiffAt ℝ s (fun x : ℝ => x) r) (hg.of_le (by simp)))
    rw [iteratedDeriv_n01aOpticalRawControl_eq hr s, hmul]
    calc
      |∑ k ∈ Finset.range (s + 1), (s.choose k : ℝ) *
          iteratedDeriv k (fun x : ℝ => x) r *
          iteratedDeriv (s - k) (fun x => n01aOpticalCutoff (n01aOpticalRadicand w x / δ)) r| ≤
          ∑ k ∈ Finset.range (s + 1), |(s.choose k : ℝ) *
            iteratedDeriv k (fun x : ℝ => x) r *
            iteratedDeriv (s - k) (fun x => n01aOpticalCutoff (n01aOpticalRadicand w x / δ)) r| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ k ∈ Finset.range (s + 1), (s.choose k : ℝ) * (1 + β) * B := by
        apply Finset.sum_le_sum
        intro k hk
        rw [abs_mul, abs_mul, abs_of_nonneg (Nat.cast_nonneg _)]
        exact mul_le_mul (mul_le_mul_of_nonneg_left (hidBound k) (Nat.cast_nonneg _))
          (hgBound (s - k) (Nat.sub_le _ _)) (abs_nonneg _)
          (mul_nonneg (Nat.cast_nonneg _) (by linarith))
      _ = A * (1 + β) * B := by rw [← Finset.sum_mul, ← Finset.sum_mul]
      _ ≤ (A + 1) * (1 + β) * B :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right (by linarith : A ≤ A + 1) (by linarith)) hB
      _ = C * (1 + β) * (1 + K / δ) ^ s := by dsimp [B, C]; ring
  · rw [iteratedDeriv_n01aOpticalRawControl_zero hl hδ hw hpos hrootL hrootR hr s, abs_zero]
    exact mul_nonneg (mul_nonneg hC.le (by linarith))
      (pow_nonneg (zero_le_one.trans hD) _)

end ContinuousFlexibility.Statements
