module

public import ContinuousFlexibility.Radial.OuterWholeKernelBounds
public import ContinuousFlexibility.Radial.WeightKernelBounds

/-!
# Spatial decay across a fixed outer core

A finite initial core only costs a constant. Its localizer levels are
bounded, while the same actual natural column and Dirichlet kernel have
the deep-tail decay. The original four-block identity then gives the
full spatial envelope, including the two mixed blocks.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Radial

open Set Real
open ContinuousFlexibility.Statements

theorem matchedOuter_fixedCore_kernel_envelope
    {a c b : ℝ} {alpha beta P ZP Q ZQ : ℝ → ℝ}
    (H : OuterFundamentalStatePair alpha beta P ZP Q ZQ a c b)
    {lam K A B C T : ℝ} (hlam : 0 < lam) (hK : 0 ≤ K)
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hC : 0 ≤ C)
    (hac : a ≤ c) (hcb : c < b) (hPc : P c = 1) (hQc : Q c = 0)
    (hflux : ZQ c = 1 / lam)
    (hU : ∀ x ∈ Icc a c, |H.U x| ≤ K)
    (hV : ∀ x ∈ Icc a c, |H.V x| ≤ K)
    (level : ℕ → ℕ) (chi : ℕ → ℝ → ℝ)
    (hchi : ∀ k x, |chi k x| ≤ 1)
    (hcore : ∀ k x, x ∈ Icc a c → chi k x ≠ 0 → radialS (level k) ≤ T)
    (hnatural : ∀ k x, x ∈ Ico c b → chi k x ≠ 0 →
      |P x| ≤ B * exp (A * radialQ (level k) - radialS (level k)))
    (hdeep : ∀ k m x y, x ∈ Ico c b → y ∈ Ico c b →
      chi k x ≠ 0 → chi m y ≠ 0 →
      |Q (min x y) * P (max x y)| ≤ C * exp
        (A * (radialQ (level k) + radialQ (level m)) -
          |radialS (level k) - radialS (level m)|))
    (k m : ℕ) {x y : ℝ} (hx : x ∈ Ico a b) (hy : y ∈ Ico a b) :
    |chi k x * outerGreenKernel lam H.U H.V x y * chi m y| ≤
      (C + lam⁻¹ * K ^ 2 * (max B (exp T)) ^ 2) * exp
        (A * (radialQ (level k) + radialQ (level m)) -
          |radialS (level k) - radialS (level m)|) := by
  let L := max B (exp T)
  let e (i : ℕ) := L * exp (A * radialQ (level i) - radialS (level i))
  let d := exp (A * (radialQ (level k) + radialQ (level m)) -
    |radialS (level k) - radialS (level m)|)
  have hL : 0 ≤ L := hB.trans (le_max_left _ _)
  have he (i : ℕ) : 0 ≤ e i := mul_nonneg hL (exp_pos _).le
  have hcost : 0 ≤ C + lam⁻¹ * K ^ 2 * L ^ 2 := by positivity
  by_cases hk : chi k x = 0
  · simpa only [hk, zero_mul, abs_zero] using mul_nonneg hcost (exp_pos _).le
  by_cases hm : chi m y = 0
  · simpa only [hm, mul_zero, abs_zero] using mul_nonneg hcost (exp_pos _).le
  have hpoint (i : ℕ) (z : ℝ) (hz : z ∈ Ico a b) (hi : chi i z ≠ 0) :
      (z ∈ Icc a c ∧ 1 ≤ e i) ∨ (z ∈ Ico c b ∧ |P z| ≤ e i) := by
    by_cases hzc : z ≤ c
    · have hzc' : z ∈ Icc a c := ⟨hz.1, hzc⟩
      refine Or.inl ⟨hzc', ?_⟩
      have ht := hcore i z hzc' hi
      have hqa := mul_nonneg hA (radialQ_nonneg (level i))
      calc
        1 ≤ exp (T + (A * radialQ (level i) - radialS (level i))) :=
          one_le_exp (by linarith only [ht, hqa])
        _ = exp T * exp (A * radialQ (level i) - radialS (level i)) := exp_add _ _
        _ ≤ e i := mul_le_mul_of_nonneg_right (le_max_right _ _) (exp_pos _).le
    · have hcz : z ∈ Ico c b := ⟨(lt_of_not_ge hzc).le, hz.2⟩
      refine Or.inr ⟨hcz, (hnatural i z hcz hi).trans ?_⟩
      exact mul_le_mul_of_nonneg_right (le_max_left _ _) (exp_pos _).le
  have hd : 0 ≤ C * d := mul_nonneg hC (exp_pos _).le
  have hkernel := H.kernel_blocks_abs_le hlam hK hac hcb hPc hQc hflux hU hV
    (he k) (he m) hd (hpoint k x hx hk) (hpoint m y hy hm)
    (fun hxc hyc => hdeep k m x y hxc hyc hk hm)
  have hdist : |radialS (level k) - radialS (level m)| ≤
      radialS (level k) + radialS (level m) := by
    have hk0 := radialS_nonneg (level k)
    have hm0 := radialS_nonneg (level m)
    exact abs_le.mpr ⟨by linarith, by linarith⟩
  have hproduct : e k * e m ≤ L ^ 2 * d := by
    calc
      e k * e m = L ^ 2 * exp
          (A * (radialQ (level k) + radialQ (level m)) -
            (radialS (level k) + radialS (level m))) := by
        dsimp only [e]
        rw [show A * (radialQ (level k) + radialQ (level m)) -
            (radialS (level k) + radialS (level m)) =
          (A * radialQ (level k) - radialS (level k)) +
            (A * radialQ (level m) - radialS (level m)) by ring, exp_add]
        ring
      _ ≤ L ^ 2 * d := mul_le_mul_of_nonneg_left
        (exp_le_exp.mpr (sub_le_sub_left hdist _)) (sq_nonneg L)
  have hchi' : |chi k x| * |chi m y| ≤ 1 := by
    simpa only [one_mul] using mul_le_mul (hchi k x) (hchi m y) (abs_nonneg _) zero_le_one
  calc
    _ = (|chi k x| * |chi m y|) * |outerGreenKernel lam H.U H.V x y| := by
      simp only [abs_mul]
      ring
    _ ≤ |outerGreenKernel lam H.U H.V x y| := by
      simpa only [one_mul] using mul_le_mul_of_nonneg_right hchi' (abs_nonneg _)
    _ ≤ C * d + (lam⁻¹ * K ^ 2) * e k * e m := hkernel
    _ = C * d + (lam⁻¹ * K ^ 2) * (e k * e m) := by ring
    _ ≤ C * d + (lam⁻¹ * K ^ 2) * (L ^ 2 * d) :=
      add_le_add le_rfl (mul_le_mul_of_nonneg_left hproduct (by positivity))
    _ = _ := by dsimp only [d, L]; ring

end ContinuousFlexibility.Radial
