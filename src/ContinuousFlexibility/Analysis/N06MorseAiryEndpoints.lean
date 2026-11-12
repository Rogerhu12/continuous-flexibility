import ContinuousFlexibility.Analysis.N06AiryPhysicalGerm

/-!
# Uniform physical endpoint jets from the same realized Morse profile

The divided profile, collar and speed are chosen together by the actual
Morse realization. The fixed positive extension is then used in both the
integral coordinate and its height. This proves the ordinary endpoint
slope and height jets, and their reciprocal bounds, with one coefficient
power selected before either root or any model index. No endpoint jet
estimate is an additional hypothesis.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Real
open ContinuousFlexibility.Statements ContinuousFlexibility.Radial
open scoped ContDiff

set_option backward.isDefEq.respectTransparency false

/-- The actual two-sided reference germ supplies the physical endpoint
fields required by the positive interpolation. All choices retain the
same profile, the same divided factor and the same explicit speed extension. -/
theorem n06_morseRealization_airyEndpoint_bounds
    {T : MorseChainData} {σ : ℕ → ℝ} {D : ReferenceData} {C : ℕ → ℝ}
    (hreal : MorseChainRealization T σ D C) (hσ : ∀ n, 1 ≤ σ n ∧ σ n ≤ 2) :
    ∃ c A K P : ℝ, 0 < c ∧ 0 < A ∧ 1 ≤ K ∧ 0 < P ∧
      ∀ (side : Bool) (n : ℕ), T.index ≤ n → ∀ right : Bool,
        let r := T.radius side n
          (n06MorseOuterRoot (morseChainA T n) (morseChainB T n) right)
        let ι := n06MorseRootOrientation right
        let δ := c * radialE n ^ (-A)
        0 < δ ∧ δ ≤ 1 ∧ ∃ g : ℝ → ℝ, ContDiff ℝ ∞ g ∧
          g 0 = |deriv (deriv D.w) r| ∧
          (∀ t : ℝ, -deriv D.w (r + ι * t) = t * g t) ∧
          let cext := n06RootSpeedExtension δ (referenceRootSpeedFactor D.w g r ι)
          let a := n06AiryPhysicalSlope cext r ι
          let h := n06AiryPhysicalHeight cext D.w r ι
          ContDiff ℝ ∞ cext ∧
            (∀ x : ℝ, 0 < cext x ∧ N06ScalarJetTwoBound cext x (K * radialE n ^ P) ∧
              (cext x)⁻¹ ≤ K * radialE n ^ P) ∧
            (∀ x : ℝ, |x| ≤ δ / 4 → cext x = referenceRootSpeedFactor D.w g r ι x) ∧
            ContDiff ℝ ∞ a ∧
            (∀ u : ℝ, 0 < a u ∧ N06ScalarJetTwoBound a u (K * radialE n ^ P) ∧
              (a u)⁻¹ ≤ K * radialE n ^ P) ∧
            ∀ u : ℝ, |u - r| ≤ δ / 4 →
              0 < u ∧ δ ≤ D.w u ∧ δ ≤ g (ι * (u - r)) ∧
                ContDiffAt ℝ ∞ h u ∧ 0 < h u ∧
                N06ScalarJetTwoBound h u (K * radialE n ^ P) ∧
                (h u)⁻¹ ≤ K * radialE n ^ P := by
  have hw : ContDiff ℝ ∞ D.w := hreal.geometry.2.2.1.1
  let F : ℝ → Fin 3 → ℝ := fun r i => iteratedDeriv i.val D.w r
  have hF : Continuous F := continuous_pi fun i =>
    hw.continuous_iteratedDeriv i.val (by simp)
  obtain ⟨M₀, hM₀⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (hF.continuousOn : ContinuousOn F (Icc (D.a - 1) (D.b + 1)))
  let M : ℝ := max 1 M₀
  have hM : 1 ≤ M := le_max_left _ _
  have hprofile (k : ℕ) (hk : k ≤ 2) (u : ℝ) (hu : u ∈ Icc (D.a - 1) (D.b + 1)) :
      |iteratedDeriv k D.w u| ≤ M := by
    have hnorm := norm_le_pi_norm (F u) (⟨k, by omega⟩ : Fin 3)
    have hb : |iteratedDeriv k D.w u| ≤ ‖F u‖ := by
      simpa only [F, Real.norm_eq_abs] using hnorm
    exact hb.trans ((hM₀ u hu).trans (le_max_right _ _))
  obtain ⟨c, A, K₀, P₀, hc, hA, hK₀, hP₀, hspeed⟩ :=
    n06_morseRealization_referenceRootSpeed_bounds hreal hσ
  obtain ⟨Cext, hCext, hext⟩ := n06_rootSpeedExtension_bounds
  let B₀ : ℝ := max K₀ (max M c⁻¹)
  let Q : ℝ := max A P₀
  let Hconst : ℝ := 3 * (1536 : ℝ) ^ 5
  let K : ℝ := Hconst * (Cext * B₀ ^ 3) ^ 35
  let P : ℝ := (Q * 3) * 35
  have hB₀ : 1 ≤ B₀ := hK₀.trans (le_max_left _ _)
  have hMB : M ≤ B₀ := (le_max_left _ _).trans (le_max_right _ _)
  have hcB : c⁻¹ ≤ B₀ := (le_max_right _ _).trans (le_max_right _ _)
  have hQ : 0 < Q := hA.trans_le (le_max_left _ _)
  have hHconst : 1 ≤ Hconst := by norm_num [Hconst]
  have hK : 1 ≤ K := one_le_mul_of_one_le_of_one_le hHconst
    (one_le_pow₀ (one_le_mul_of_one_le_of_one_le hCext (one_le_pow₀ hB₀)))
  have hP : 0 < P := mul_pos (mul_pos hQ (by norm_num)) (by norm_num)
  refine ⟨c, A, K, P, hc, hA, hK, hP, ?_⟩
  intro side n hn right
  let r := T.radius side n
    (n06MorseOuterRoot (morseChainA T n) (morseChainB T n) right)
  let ι := n06MorseRootOrientation right
  let δ := c * radialE n ^ (-A)
  let B : ℝ := B₀ * radialE n ^ Q
  let L : ℝ := Cext * B ^ 3
  have hι : ι = 1 ∨ ι = -1 := n06_morseRootOrientation_unit right
  have hιabs : |ι| = 1 := by rcases hι with h | h <;> rw [h] <;> norm_num
  have hE : 1 ≤ radialE n := one_le_exp_iff.mpr (radialQ_nonneg n)
  have hEp : 0 < radialE n := zero_lt_one.trans_le hE
  have hEQ : 1 ≤ radialE n ^ Q := Real.one_le_rpow hE hQ.le
  have hB₀B : B₀ ≤ B := le_mul_of_one_le_right (zero_le_one.trans hB₀) hEQ
  have hB : 1 ≤ B := hB₀.trans hB₀B
  have hB0 : 0 ≤ B := zero_le_one.trans hB
  have hL : 1 ≤ L := one_le_mul_of_one_le_of_one_le hCext (one_le_pow₀ hB)
  have hL0 : 0 ≤ L := zero_le_one.trans hL
  have hBL : B ≤ L := by
    have h13 : B ≤ B ^ 3 := by
      simpa only [pow_one] using pow_le_pow_right₀ hB (by norm_num : 1 ≤ 3)
    exact h13.trans (le_mul_of_one_le_left (pow_nonneg hB0 3) hCext)
  have hcost : Hconst * L ^ 35 = K * radialE n ^ P := by
    have hLcost : L = (Cext * B₀ ^ 3) * radialE n ^ (Q * 3) := by
      dsimp only [L, B]
      rw [mul_pow, ← Real.rpow_mul_natCast hEp.le Q 3]
      norm_num only [Nat.cast_ofNat]
      ring
    rw [hLcost, mul_pow, ← Real.rpow_mul_natCast hEp.le (Q * 3) 35]
    dsimp only [K, P]
    norm_num only [Nat.cast_ofNat]
    ring
  have hmajor (a : ℝ) (k : ℕ) (ha : a ≤ Hconst) (hk : k ≤ 35) :
      a * L ^ k ≤ K * radialE n ^ P := by
    rw [← hcost]
    exact mul_le_mul ha (pow_le_pow_right₀ hL hk)
      (pow_nonneg hL0 k) (zero_le_one.trans hHconst)
  have hLcap : L ≤ K * radialE n ^ P := by
    simpa only [pow_one, one_mul] using hmajor 1 1 hHconst (by norm_num)
  have hδB : δ⁻¹ ≤ B := by
    have hi : δ⁻¹ = c⁻¹ * radialE n ^ A := by
      dsimp only [δ]
      rw [mul_inv_rev, Real.rpow_neg hEp.le, inv_inv]
      ring
    rw [hi]
    exact mul_le_mul hcB
      (Real.rpow_le_rpow_of_exponent_le hE (le_max_left _ _))
      (Real.rpow_nonneg hEp.le A) (zero_le_one.trans hB₀)
  have hspeedB : K₀ * radialE n ^ P₀ ≤ B :=
    mul_le_mul (le_max_left _ _)
      (Real.rpow_le_rpow_of_exponent_le hE (le_max_right _ _))
      (Real.rpow_nonneg hEp.le P₀) (zero_le_one.trans hB₀)
  obtain ⟨hδ, hδ1, g, hg, hg0, hfactor, hraw⟩ := hspeed side n hn right
  let f : ℝ → ℝ := referenceRootSpeedFactor D.w g r ι
  let cext : ℝ → ℝ := n06RootSpeedExtension δ f
  let W : ℝ → ℝ := fun t => D.w (r + ι * t)
  have hW : ContDiff ℝ ∞ W := hw.comp (contDiff_const.add (contDiff_const.mul contDiff_id))
  have hlocal (x : ℝ) (hx : x ∈ Metric.ball (0 : ℝ) δ) :
      ContDiffAt ℝ ∞ f x ∧ 0 < f x ∧ N06ScalarJetTwoBound f x B ∧ (f x)⁻¹ ≤ B := by
    have hxx : x ∈ Icc (-δ) δ := by
      apply abs_le.mp
      have hh : |x| < δ := by
        simpa only [Metric.mem_ball, Real.dist_eq, sub_zero] using hx
      exact hh.le
    obtain ⟨_, _, _, hs, hp, hj, hi⟩ := hraw x hxx
    exact ⟨hs, hp, hj.mono hspeedB, hi.trans hspeedB⟩
  obtain ⟨hcext, hcextAll⟩ := hext δ B f hδ hB hδB
    (fun x hx => (hlocal x hx).1) (fun x hx => (hlocal x hx).2.1)
    (fun x hx => (hlocal x hx).2.2.1) (fun x hx => (hlocal x hx).2.2.2)
  have hcpos : ∀ x : ℝ, 0 < cext x := fun x => (hcextAll x).1
  have hcjet : ∀ x : ℝ, N06ScalarJetTwoBound cext x L := fun x => (hcextAll x).2.1
  have hcinv : ∀ x : ℝ, (cext x)⁻¹ ≤ L := fun x => (hcextAll x).2.2
  have havg : ∀ x : ℝ, 0 < n06AiryAverage cext x := fun x =>
    (n06_airyAverage_twoJet_bound hcext hL hcjet hcpos hcinv x).1
  obtain ⟨_, hsmooth, _, hslope⟩ :=
    n06_airyRadialSlope_bounds hcext hL hcjet hcpos hcinv
  have hslopecap : 384 * L ^ 6 ≤ K * radialE n ^ P :=
    hmajor 384 6 (by norm_num [Hconst]) (by norm_num)
  have hslopeinv : 2 * L ^ 2 ≤ K * radialE n ^ P :=
    hmajor 2 2 (by norm_num [Hconst]) (by norm_num)
  refine ⟨hδ, hδ1, g, hg, hg0, hfactor, hcext, ?_, ?_,
    n06_contDiff_airyPhysicalSlope hcext havg r ι, ?_, ?_⟩
  · intro x
    exact ⟨hcpos x, (hcjet x).mono hLcap, (hcinv x).trans hLcap⟩
  · intro x hx
    exact n06_rootSpeedExtension_eq hδ f hx
  · intro u
    have hsu := hslope (ι * (u - r))
    exact ⟨hsu.1, (hsu.2.1.oriented_center hι).mono hslopecap,
      hsu.2.2.trans hslopeinv⟩
  · intro u hu
    let x : ℝ := ι * (u - r)
    have hback : r + ι * x = u := by
      dsimp only [x]
      rcases hι with h | h <;> rw [h] <;> ring
    have hx : x ∈ Icc (-δ) δ := by
      apply abs_le.mp
      calc
        |x| = |u - r| := by dsimp only [x]; rw [abs_mul, hιabs, one_mul]
        _ ≤ δ / 4 := hu
        _ ≤ δ := by linarith only [hδ]
    obtain ⟨hgt, hwt, hrt, _, _, _, _⟩ := hraw x hx
    rw [hback] at hwt hrt
    have hup : 0 < u := (half_pos hreal.geometry.1).trans_le hrt
    have hwp : 0 < W x := by simpa only [W, hback] using hδ.trans_le hwt
    have hr := (n06_morseRealization_root_profile_data hreal hσ side hn right).1
    have hu1 : |u - r| ≤ 1 := hu.trans (by linarith only [hδ1, hδ])
    have hucompact : u ∈ Icc (D.a - 1) (D.b + 1) := by
      have hdu := abs_le.mp hu1
      constructor <;> linarith only [hdu.1, hdu.2, hr.1, hr.2]
    have hWjet : N06ScalarJetTwoBound W x L := by
      apply n06_scalarJetTwoBound_iff.mpr
      intro k hk
      have hshift : |iteratedDeriv k W x| = |iteratedDeriv k D.w (r + ι * x)| := by
        dsimp only [W]
        rcases hι with h | h
        · simp only [h, one_mul, iteratedDeriv_comp_const_add]
        · simp only [h, neg_one_mul, ← sub_eq_add_neg, iteratedDeriv_comp_const_sub,
            smul_eq_mul, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul]
      rw [hshift, hback]
      exact (hprofile k hk u hucompact).trans ((hMB.trans hB₀B).trans hBL)
    have hWinv : (W x)⁻¹ ≤ L := by
      rw [show W x = D.w u by simp only [W, hback]]
      exact ((inv_anti₀ hδ hwt).trans hδB).trans hBL
    obtain ⟨hheightSm, hheightPos, hheightJet, hheightInv⟩ :=
      n06_airyRadialHeight_twoJet_bound hcext hL hcjet hcpos hcinv
        hW.contDiffAt hwp hWjet hWinv
    have hheightEq := n06_airyPhysicalHeight_fun_eq_radial cext D.w r ι hι
    have hheightAt : ContDiffAt ℝ ∞ (n06AiryPhysicalHeight cext D.w r ι) u := by
      rw [hheightEq]
      exact hheightSm.comp u (contDiffAt_const.mul (contDiffAt_id.sub contDiffAt_const))
    have hheightJ : N06ScalarJetTwoBound (n06AiryPhysicalHeight cext D.w r ι) u
        (K * radialE n ^ P) := by
      rw [hheightEq]
      have hh := hheightJet.oriented_center (r := r) hι
      simpa only [← hcost, Hconst, W, x] using hh
    have hheightV : n06AiryPhysicalHeight cext D.w r ι u = n06AiryRadialHeight cext W x :=
      n06_airyPhysicalHeight_eq_radial cext D.w r ι u hι
    refine ⟨hup, hwt, hgt, hheightAt, ?_, hheightJ, ?_⟩
    · rw [hheightV]
      exact hheightPos
    · rw [hheightV, ← hcost]
      exact hheightInv

end ContinuousFlexibility.Analysis
