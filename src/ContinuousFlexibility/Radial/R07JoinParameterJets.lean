import ContinuousFlexibility.Radial.R07MorseJoinParameters
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas

/-!
# Joint continuity of all chosen-join spatial jets

The amplitude formula controls the actual profile on a neighborhood of every
point of the closed join, including its endpoints.  Smooth dependence on the
two finite-dimensional logarithmic amplitudes therefore gives continuity of
every spatial derivative for the product topology on the height cube.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open Real Set Filter
open scoped Topology ContDiff

/-- Collar-germ invariance holds as a full germ at every point of the closed
join, including both endpoints. -/
theorem morseJoinLog_germs_of_germs {a b hL hR : ℝ}
    {fL fR FL FR : ℝ → ℝ} (hhL : 0 < hL) (hhR : 0 < hR)
    (hsep : a + hL < b - hR)
    (hfL : ContDiff ℝ ∞ fL) (hfR : ContDiff ℝ ∞ fR)
    (hFL : ContDiff ℝ ∞ FL) (hFR : ContDiff ℝ ∞ FR)
    (hLg : ∀ x ∈ Icc a (a + hL), FL =ᶠ[𝓝 x] fL)
    (hRg : ∀ x ∈ Icc (b - hR) b, FR =ᶠ[𝓝 x] fR)
    {x : ℝ} (hx : x ∈ Icc a b) :
    morseJoinLog a b hL hR FL FR =ᶠ[𝓝 x] morseJoinLog a b hL hR fL fR := by
  obtain ⟨hLa, hRb⟩ := morseJoinLog_endpoint_germs hhL hhR hsep hFL hFR
  obtain ⟨hla, hrb⟩ := morseJoinLog_endpoint_germs hhL hhR hsep hfL hfR
  by_cases hxa : x = a
  · subst x
    exact hLa.trans ((hLg a ⟨le_rfl, le_add_of_nonneg_right hhL.le⟩).trans hla.symm)
  by_cases hxb : x = b
  · subst x
    exact hRb.trans ((hRg b ⟨sub_le_self _ hhR.le, le_rfl⟩).trans hrb.symm)
  have hxi : x ∈ Ioo a b := ⟨lt_of_le_of_ne hx.1 (Ne.symm hxa), lt_of_le_of_ne hx.2 hxb⟩
  have hab : a ≤ b := hx.1.trans hx.2
  filter_upwards [isOpen_Ioo.mem_nhds hxi] with y hy
  exact morseJoinLog_eqOn_of_germs hab hhL hhR hLg hRg (Ioo_subset_Icc_self hy)

theorem morseJoinProfile_germs_of_germs {a b hL hR : ℝ}
    {fL fR FL FR : ℝ → ℝ} (hhL : 0 < hL) (hhR : 0 < hR)
    (hsep : a + hL < b - hR)
    (hfL : ContDiff ℝ ∞ fL) (hfR : ContDiff ℝ ∞ fR)
    (hFL : ContDiff ℝ ∞ FL) (hFR : ContDiff ℝ ∞ FR)
    (hLg : ∀ x ∈ Icc a (a + hL), FL =ᶠ[𝓝 x] fL)
    (hRg : ∀ x ∈ Icc (b - hR) b, FR =ᶠ[𝓝 x] fR)
    {x : ℝ} (hx : x ∈ Icc a b) :
    morseJoinProfile a b hL hR FL FR =ᶠ[𝓝 x] morseJoinProfile a b hL hR fL fR :=
  (morseJoinLog_germs_of_germs hhL hhR hsep hfL hfR hFL hFR hLg hRg hx).fun_comp exp

/-- Spatial differentiation preserves smooth joint dependence on a parameter
in any real normed space. -/
theorem contDiff_parametric_iteratedDeriv {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : E → ℝ → ℝ} (hf : ContDiff ℝ ∞ (Function.uncurry f)) (n : ℕ) :
    ContDiff ℝ ∞ (fun z : E × ℝ => iteratedDeriv n (f z.1) z.2) := by
  induction n with
  | zero => simpa only [iteratedDeriv_zero, Function.uncurry_def] using hf
  | succ n ih =>
    let F : (E × ℝ) → ℝ → ℝ := fun z t => iteratedDeriv n (f z.1) t
    have hF : ContDiff ℝ ∞ (Function.uncurry F) :=
      ih.comp (contDiff_fst.fst.prodMk contDiff_snd)
    have hd := hF.fderiv_apply
      (contDiff_snd : ContDiff ℝ ∞ (fun z : E × ℝ => z.2))
      (contDiff_const : ContDiff ℝ ∞ (fun _ : E × ℝ => (1 : ℝ))) (by simp)
    simpa only [F, fderiv_apply_one_eq_deriv, iteratedDeriv_succ] using hd

private theorem contDiff_morseJoinProfile_two_amplitudes {a b hL hR : ℝ} {fL fR : ℝ → ℝ}
    (hfL : ContDiff ℝ ∞ fL) (hfR : ContDiff ℝ ∞ fR) :
    ContDiff ℝ ∞ (fun z : (ℝ × ℝ) × ℝ => morseJoinProfile a b hL hR
      (fun y => fL y + z.1.1) (fun y => fR y + z.1.2) z.2) := by
  have he : (fun z : (ℝ × ℝ) × ℝ => morseJoinProfile a b hL hR
      (fun y => fL y + z.1.1) (fun y => fR y + z.1.2) z.2) =
      (fun z => exp (morseJoinLog a b hL hR fL fR z.2 + z.1.1 +
        (z.1.2 - z.1.1) * morseJoinHeightCoordinate a b hL hR z.2)) := by
    funext z
    rw [morseJoinProfile, morseJoinLog_add_const hfL hfR]
  rw [he]
  exact ((((contDiff_morseJoinLog hfL hfR).comp contDiff_snd).add contDiff_fst.fst).add
    ((contDiff_fst.snd.sub contDiff_fst.fst).mul
      ((contDiff_morseJoinHeightCoordinate a b hL hR).comp contDiff_snd))).exp

/-- Every spatial jet of the explicit two-log-amplitude join is jointly
continuous in arbitrary continuous parameters. -/
theorem continuous_morseJoinProfile_add_const_iteratedDeriv {X : Type*} [TopologicalSpace X]
    {a b hL hR : ℝ} {fL fR : ℝ → ℝ}
    (hfL : ContDiff ℝ ∞ fL) (hfR : ContDiff ℝ ∞ fR) (n : ℕ)
    {cL cR x : X → ℝ} (hCL : Continuous cL) (hCR : Continuous cR) (hx : Continuous x) :
    Continuous (fun z => iteratedDeriv n
      (morseJoinProfile a b hL hR (fun y => fL y + cL z) (fun y => fR y + cR z)) (x z)) := by
  have hf := contDiff_morseJoinProfile_two_amplitudes
    (a := a) (b := b) (hL := hL) (hR := hR) hfL hfR
  have hi := contDiff_parametric_iteratedDeriv hf n
  exact hi.continuous.comp ((hCL.prodMk hCR).prodMk hx)

/-- Product-topology continuity of every actual chosen-join spatial jet,
including at either endpoint of the physical join. -/
theorem continuousOn_morseChainChosenJoinProfile_iteratedDeriv {T : Statements.MorseChainData}
    (G : MorseChainGeometryWitness T) (side : Bool) (k n : ℕ) :
    ContinuousOn (fun z : Statements.HeightRatios × ℝ =>
      iteratedDeriv n (morseChainChosenJoinProfile G z.1.val z.1.property side k) z.2)
      {z | z.2 ∈ Icc (T.joinLeft side (T.index + k)) (T.joinRight side (T.index + k))} := by
  let P₀ := morseChainChosenJoin G morseUnitHeights morseUnitHeights_admissible side k
  let a := T.joinLeft side (T.index + k)
  let b := T.joinRight side (T.index + k)
  let h := morseChainProfileJoinCutoff T side k
  let cL : Statements.HeightRatios → ℝ :=
    fun σ => morseChainHeightLogRatio T σ.val (T.index + morseChainJoinDeparture side k)
  let cR : Statements.HeightRatios → ℝ :=
    fun σ => morseChainHeightLogRatio T σ.val (T.index + morseChainJoinArrival side k)
  have hL : Continuous cL := continuous_morseChainHeightLogRatio T _
  have hR : Continuous cR := continuous_morseChainHeightLogRatio T _
  have hc : Continuous (fun z : Statements.HeightRatios × ℝ =>
      iteratedDeriv n (morseJoinProfile a b h h (fun y => P₀.leftLog y + cL z.1)
        (fun y => P₀.rightLog y + cR z.1)) z.2) :=
    continuous_morseJoinProfile_add_const_iteratedDeriv P₀.left_smooth P₀.right_smooth n
      (hL.comp continuous_fst) (hR.comp continuous_fst) continuous_snd
  refine hc.continuousOn.congr ?_
  intro z hz
  let P := morseChainChosenJoin G z.1.val z.1.property side k
  obtain ⟨hgL, hgR⟩ := morseChainChosenJoin_log_germs G z.1.val z.1.property side k
  have hab := morseChainPhysicalJoin_order G side k
  have hh : 0 < morseChainProfileJoinCutoff T side k :=
    div_pos (sub_pos.mpr hab) (by norm_num)
  have hsep : a + h < b - h := by
    dsimp only [a, b, h, morseChainProfileJoinCutoff]
    linarith only [hab]
  have he := morseJoinProfile_germs_of_germs hh hh hsep
    (P₀.left_smooth.add contDiff_const) (P₀.right_smooth.add contDiff_const)
    P.left_smooth P.right_smooth hgL hgR hz
  exact he.iteratedDeriv_eq n

end ContinuousFlexibility.Radial
