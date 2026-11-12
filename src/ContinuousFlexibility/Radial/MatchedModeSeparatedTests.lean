import ContinuousFlexibility.Radial.MatchedModeTestClosure
import ContinuousFlexibility.Radial.MatchingWeakGluing

/-!
# The original test class on separated outer intervals

A test supported in two disjoint intervals vanishes near their separating
gap. Its two indicator restrictions are therefore smooth and retain the
original endpoint behavior. The equation follows from the equations on
the two intervals, without imposing topological support at the endpoints.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open Set Filter MeasureTheory
open scoped Topology ContDiff
open ContinuousFlexibility.Statements

theorem modeLocalEquation_disjointIntervals {D : ReferenceData}
    (hD : IsAccumulatingProfile D) (hB : RadialTrueBorder D)
    {j : ℕ} {U F : RadialModePair D} {a b c d : ℝ} (hbc : b < c)
    (hL : ModeLocalEquation D j (Ioo a b) U F)
    (hR : ModeLocalEquation D j (Ioo c d) U F) :
    ModeLocalEquation D j (Ioo a b ∪ Ioo c d) U F := by
  classical
  apply modeLocalEquation_iff_matchingModeTestResidual_zero.mpr
  intro ψ hψ hcψ hsψ
  let e : ℝ := (b + c) / 2
  have hbe : b < e := by dsimp only [e]; linarith
  have hec : e < c := by dsimp only [e]; linarith
  have hzero : ψ =ᶠ[𝓝 e] fun _ => 0 := by
    filter_upwards [show Ioo b c ∈ 𝓝 e from isOpen_Ioo.mem_nhds ⟨hbe, hec⟩]
      with x hx
    apply Function.notMem_support.mp
    intro hxs
    rcases hsψ hxs with hxl | hxr
    · exact (not_lt_of_ge hx.1.le) hxl.2
    · exact (not_lt_of_ge hx.2.le) hxr.1
  let ψL : ℝ → ℝ := (Iio e).indicator ψ
  let ψR : ℝ → ℝ := fun x => ψ x - ψL x
  have hLs : ContDiff ℝ ∞ ψL := matching_contDiff_indicator_Iio hψ hzero
  have hRs : ContDiff ℝ ∞ ψR := hψ.sub hLs
  have hLsub : Function.support ψL ⊆ Function.support ψ := by
    intro x hx hz
    apply hx
    simp only [ψL, Set.indicator_apply, hz, ite_self]
  have hRsub : Function.support ψR ⊆ Function.support ψ := by
    intro x hx hz
    apply hx
    simp only [ψR, ψL, Set.indicator_apply, hz, ite_self, sub_self]
  have hLc : HasCompactSupport ψL := hcψ.mono hLsub
  have hRc : HasCompactSupport ψR := hcψ.mono hRsub
  have hLsupport : Function.support ψL ⊆ Ioo a b := by
    intro x hx
    have hxe : x < e := by
      by_contra h
      apply hx
      exact Set.indicator_of_notMem (show x ∉ Iio e from h) ψ
    rcases hsψ (hLsub hx) with hxl | hxr
    · exact hxl
    · exact False.elim ((not_lt_of_ge hec.le) (hxr.1.trans hxe))
  have hRsupport : Function.support ψR ⊆ Ioo c d := by
    intro x hx
    have hex : e ≤ x := by
      by_contra h
      have hxe : x ∈ Iio e := lt_of_not_ge h
      apply hx
      dsimp only [ψR, ψL]
      rw [Set.indicator_of_mem hxe, sub_self]
    rcases hsψ (hRsub hx) with hxl | hxr
    · exact False.elim ((not_lt_of_ge hex) (hxl.2.trans hbe))
    · exact hxr
  have heq : ψ = fun x => ψL x + ψR x := by
    funext x
    dsimp only [ψR]
    ring
  have hzL := modeLocalEquation_iff_matchingModeTestResidual_zero.mp hL
    ψL hLs hLc hLsupport
  have hzR := modeLocalEquation_iff_matchingModeTestResidual_zero.mp hR
    ψR hRs hRc hRsupport
  rw [heq, matchingModeTestResidual_add hD hB hLs hRs hLc hRc, hzL, hzR, zero_add]

/-- The two actual outer equations imply the frozen separated equation. -/
theorem modeLocalEquation_matchingOuter_of_sides {D : ReferenceData}
    (hD : IsAccumulatingProfile D) (hB : RadialTrueBorder D)
    {M : RadialMatchingData D} (hm : M.innerLeft < M.innerRight)
    {U F : RadialModePair D}
    (hL : ModeLocalEquation D M.frequency (Ioo D.a M.innerLeft) U F)
    (hR : ModeLocalEquation D M.frequency (Ioo M.innerRight D.b) U F) :
    ModeLocalEquation D M.frequency (matchingOuterRegion D M) U F :=
  modeLocalEquation_disjointIntervals hD hB hm hL hR

end ContinuousFlexibility.Radial
