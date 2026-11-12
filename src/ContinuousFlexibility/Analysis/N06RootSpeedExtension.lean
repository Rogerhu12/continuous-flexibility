import ContinuousFlexibility.Analysis.N06MorseRootSpeed

/-!
# A controlled global extension of the actual reference speed germ

The fixed cutoff leaves the original factored speed unchanged on a
quantitative two-sided collar. Outside that collar it blends to the true
value at the root. This is the explicitly chosen reference extension for
the new controlled atlas; no assertion about a previous Seeley extension
on the negative half-plane is used.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Real
open ContinuousFlexibility.Statements ContinuousFlexibility.Radial
open scoped ContDiff

set_option backward.isDefEq.respectTransparency false

def n06RootSpeedExtension (δ : ℝ) (f : ℝ → ℝ) (x : ℝ) : ℝ :=
  f 0 + positiveEndpointCutoff 0 δ x * (f x - f 0)

/-- The fixed cutoff is identically one on the explicit inner quarter. -/
theorem n06_rootSpeedExtension_eq {δ : ℝ} (hδ : 0 < δ)
    (f : ℝ → ℝ) {x : ℝ} (hx : |x| ≤ δ / 4) :
    n06RootSpeedExtension δ f x = f x := by
  have hcut : positiveEndpointCutoff 0 δ x = 1 := by
    apply boundaryTaylorCutoff.one_of_mem_closedBall
    rw [Metric.mem_closedBall, Real.dist_eq]
    change |(x - 0) / δ - 0| ≤ (1 / 4 : ℝ)
    rw [sub_zero, sub_zero, abs_div, abs_of_pos hδ]
    apply (div_le_iff₀ hδ).mpr
    linarith only [hx]
  simp only [n06RootSpeedExtension, hcut, one_mul]
  ring

/-- A finite-order, globally positive extension is constructed from
actual local data. Its jet cost is a fixed cubic in the raw cap. -/
theorem n06_rootSpeedExtension_bounds :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ (δ B : ℝ) (f : ℝ → ℝ), 0 < δ → 1 ≤ B → δ⁻¹ ≤ B →
      (∀ x ∈ Metric.ball (0 : ℝ) δ, ContDiffAt ℝ ∞ f x) →
      (∀ x ∈ Metric.ball (0 : ℝ) δ, 0 < f x) →
      (∀ x ∈ Metric.ball (0 : ℝ) δ, N06ScalarJetTwoBound f x B) →
      (∀ x ∈ Metric.ball (0 : ℝ) δ, (f x)⁻¹ ≤ B) →
      ContDiff ℝ ∞ (n06RootSpeedExtension δ f) ∧
        ∀ x : ℝ, 0 < n06RootSpeedExtension δ f x ∧
          N06ScalarJetTwoBound (n06RootSpeedExtension δ f) x (C * B ^ 3) ∧
          (n06RootSpeedExtension δ f x)⁻¹ ≤ C * B ^ 3 := by
  obtain ⟨Ccut, hCcut, hcut⟩ := n06_positiveEndpointCutoff_twoJet_bound
  let C : ℝ := 1 + 8 * Ccut
  have hC : 1 ≤ C := by dsimp only [C]; linarith only [hCcut]
  refine ⟨C, hC, ?_⟩
  intro δ B f hδ hB hδB hsm hpos hjet hinv
  have hB0 : 0 ≤ B := zero_le_one.trans hB
  have hBp : 0 < B := zero_lt_one.trans_le hB
  have hzero : (0 : ℝ) ∈ Metric.ball 0 δ := Metric.mem_ball_self hδ
  have hf0 : 0 < f 0 := hpos 0 hzero
  have hf0B : |f 0| ≤ B := (hjet 0 hzero).value
  have hconst (x : ℝ) : N06ScalarJetTwoBound (fun _ : ℝ => f 0) x B := by
    exact ⟨hf0B, by simpa only [deriv_const, abs_zero] using hB0,
      by simpa only [deriv_const', deriv_const, abs_zero] using hB0⟩
  have hdiff : ∀ x ∈ Metric.ball (0 : ℝ) δ,
      ContDiffAt ℝ ∞ (fun t => f t - f 0) x := fun x hx => (hsm x hx).sub contDiffAt_const
  have hdiffB : ∀ x ∈ Metric.ball (0 : ℝ) δ,
      N06ScalarJetTwoBound (fun t => f t - f 0) x (2 * B) := by
    intro x hx
    have h := (hjet x hx).sub_at (hsm x hx) contDiffAt_const (hconst x)
    convert h using 1 <;> ring
  have hclipsm : ContDiff ℝ ∞ (fun x => positiveEndpointCutoff 0 δ x * (f x - f 0)) :=
    contDiff_positiveEndpointCutoff_mul hδ hdiff
  have hExt : ContDiff ℝ ∞ (n06RootSpeedExtension δ f) := contDiff_const.add hclipsm
  have hBB3 : B ≤ B ^ 3 := by
    simpa only [pow_one] using pow_le_pow_right₀ hB (by norm_num : 1 ≤ 3)
  have hbound : B ≤ C * B ^ 3 := hBB3.trans
    (le_mul_of_one_le_left (pow_nonneg hB0 3) hC)
  refine ⟨hExt, ?_⟩
  intro x
  have hvalue : B⁻¹ ≤ n06RootSpeedExtension δ f x ∧ n06RootSpeedExtension δ f x ≤ B := by
    have h0lower : B⁻¹ ≤ f 0 := inv_le_of_inv_le₀ hf0 (hinv 0 hzero)
    have h0upper : f 0 ≤ B := (le_abs_self _).trans hf0B
    by_cases hx : x ∈ Metric.ball (0 : ℝ) δ
    · have hlower : B⁻¹ ≤ f x := inv_le_of_inv_le₀ (hpos x hx) (hinv x hx)
      have hupper : f x ≤ B := (le_abs_self _).trans (hjet x hx).value
      have hχ0 := positiveEndpointCutoff_nonneg 0 δ x
      have hχ1 := positiveEndpointCutoff_le_one 0 δ x
      have hcomp : 0 ≤ 1 - positiveEndpointCutoff 0 δ x := sub_nonneg.mpr hχ1
      have hlo := add_le_add
        (mul_le_mul_of_nonneg_left hlower hχ0)
        (mul_le_mul_of_nonneg_left h0lower hcomp)
      have hhi := add_le_add
        (mul_le_mul_of_nonneg_left hupper hχ0)
        (mul_le_mul_of_nonneg_left h0upper hcomp)
      constructor <;> dsimp only [n06RootSpeedExtension] <;> nlinarith only [hlo, hhi]
    · simp only [n06RootSpeedExtension,
        positiveEndpointCutoff_eq_zero_of_not_mem_ball hδ hx, zero_mul, add_zero]
      exact ⟨h0lower, h0upper⟩
  have hpositive := (inv_pos.mpr hBp).trans_le hvalue.1
  have hclip := n06_positiveEndpointCutoff_mul_twoJet hδ (by positivity : 0 ≤ 2 * B)
    (by positivity : 0 ≤ Ccut * B ^ 2) hdiff hdiffB
    (hcut 0 δ B · hδ hB hδB) x
  have hfull := (hconst x).add_at contDiffAt_const hclipsm.contDiffAt hclip
  have hjets : N06ScalarJetTwoBound (n06RootSpeedExtension δ f) x (C * B ^ 3) := by
    apply hfull.mono
    dsimp only [C]
    nlinarith only [hBB3]
  have hi : (n06RootSpeedExtension δ f x)⁻¹ ≤ B := by
    have hh := inv_anti₀ (inv_pos.mpr hBp) hvalue.1
    simpa only [inv_inv] using hh
  exact ⟨hpositive, hjets, hi.trans hbound⟩

/-- The globally smooth positive coefficient is constructed from the
same Morse profile and retains the true speed on a polynomial collar.
All constants precede both roots, both tails, and every model index. -/
theorem n06_morseRealization_rootSpeedExtension_bounds
    {T : MorseChainData} {σ : ℕ → ℝ} {D : ReferenceData} {C : ℕ → ℝ}
    (hreal : MorseChainRealization T σ D C) (hσ : ∀ n, 1 ≤ σ n ∧ σ n ≤ 2) :
    ∃ c A K P : ℝ, 0 < c ∧ 0 < A ∧ 1 ≤ K ∧ 0 < P ∧
      ∀ (side : Bool) (n : ℕ), T.index ≤ n → ∀ right : Bool,
        let r := T.radius side n
          (n06MorseOuterRoot (morseChainA T n) (morseChainB T n) right)
        let ι := n06MorseRootOrientation right
        let δ := c * radialE n ^ (-A)
        0 < δ ∧ ∃ g : ℝ → ℝ, ContDiff ℝ ∞ g ∧
          (∀ t : ℝ, -deriv D.w (r + ι * t) = t * g t) ∧
          let f := referenceRootSpeedFactor D.w g r ι
          let fext := n06RootSpeedExtension δ f
          ContDiff ℝ ∞ fext ∧
            (∀ x : ℝ, |x| ≤ δ / 4 → fext x = f x) ∧
            ∀ x : ℝ, 0 < fext x ∧ N06ScalarJetTwoBound fext x (K * radialE n ^ P) ∧
              (fext x)⁻¹ ≤ K * radialE n ^ P := by
  obtain ⟨c, A, K₀, P₀, hc, hA, hK₀, hP₀, hspeed⟩ :=
    n06_morseRealization_referenceRootSpeed_bounds hreal hσ
  obtain ⟨Cext, hCext, hext⟩ := n06_rootSpeedExtension_bounds
  let B₀ : ℝ := max K₀ c⁻¹
  let Q : ℝ := max A P₀
  let K : ℝ := Cext * B₀ ^ 3
  let P : ℝ := Q * 3
  have hB₀ : 1 ≤ B₀ := hK₀.trans (le_max_left _ _)
  have hQ : 0 < Q := hA.trans_le (le_max_left _ _)
  have hK : 1 ≤ K := one_le_mul_of_one_le_of_one_le hCext (one_le_pow₀ hB₀)
  have hP : 0 < P := mul_pos hQ (by norm_num)
  refine ⟨c, A, K, P, hc, hA, hK, hP, ?_⟩
  intro side n hn right
  let r := T.radius side n
    (n06MorseOuterRoot (morseChainA T n) (morseChainB T n) right)
  let ι := n06MorseRootOrientation right
  let δ := c * radialE n ^ (-A)
  let B : ℝ := B₀ * radialE n ^ Q
  have hE : 1 ≤ radialE n := one_le_exp_iff.mpr (radialQ_nonneg n)
  have hEp : 0 < radialE n := zero_lt_one.trans_le hE
  have hB : 1 ≤ B := one_le_mul_of_one_le_of_one_le hB₀ (Real.one_le_rpow hE hQ.le)
  have hcost : Cext * B ^ 3 = K * radialE n ^ P := by
    dsimp only [B, K, P]
    rw [mul_pow, ← Real.rpow_mul_natCast hEp.le Q 3]
    norm_num only [Nat.cast_ofNat]
    ring
  have hδB : δ⁻¹ ≤ B := by
    have he : δ⁻¹ = c⁻¹ * radialE n ^ A := by
      dsimp only [δ]
      rw [mul_inv_rev, Real.rpow_neg hEp.le, inv_inv]
      ring
    rw [he]
    exact mul_le_mul (le_max_right _ _)
      (Real.rpow_le_rpow_of_exponent_le hE (le_max_left _ _))
      (Real.rpow_nonneg hEp.le A) (zero_le_one.trans hB₀)
  have hcap : K₀ * radialE n ^ P₀ ≤ B :=
    mul_le_mul (le_max_left _ _)
      (Real.rpow_le_rpow_of_exponent_le hE (le_max_right _ _))
      (Real.rpow_nonneg hEp.le P₀) (zero_le_one.trans hB₀)
  obtain ⟨hδ, _, g, hg, _, hfactor, hraw⟩ := hspeed side n hn right
  let f : ℝ → ℝ := referenceRootSpeedFactor D.w g r ι
  have hlocal (x : ℝ) (hx : x ∈ Metric.ball (0 : ℝ) δ) :
      ContDiffAt ℝ ∞ f x ∧ 0 < f x ∧ N06ScalarJetTwoBound f x B ∧ (f x)⁻¹ ≤ B := by
    have hxx : x ∈ Icc (-δ) δ := by
      apply abs_le.mp
      have hh : |x| < δ := by
        simpa only [Metric.mem_ball, Real.dist_eq, sub_zero] using hx
      exact hh.le
    obtain ⟨_, _, _, hs, hp, hj, hi⟩ := hraw x hxx
    exact ⟨hs, hp, hj.mono hcap, hi.trans hcap⟩
  obtain ⟨hsm, hall⟩ := hext δ B f hδ hB hδB
    (fun x hx => (hlocal x hx).1) (fun x hx => (hlocal x hx).2.1)
    (fun x hx => (hlocal x hx).2.2.1) (fun x hx => (hlocal x hx).2.2.2)
  refine ⟨hδ, g, hg, hfactor, hsm, fun x hx => n06_rootSpeedExtension_eq hδ f hx, ?_⟩
  intro x
  simpa only [hcost] using hall x

end ContinuousFlexibility.Analysis
