import ContinuousFlexibility.Analysis.StateKappaBounds
import ContinuousFlexibility.Blueprint.Statements
import Mathlib.Analysis.SpecialFunctions.SmoothTransition

/-!
# Normalizing the coefficient envelope without changing the physical model

We replace only `E0` by `E0 + smoothTransition (2 - E0)`. On the open
annulus the new weight is at least one and at least the old weight. It is
identical to the old weight wherever `E0 ≥ 2`, in particular on the actual
endpoint regions. The coordinate, height weights, samples, norms, spaces,
controls, flows and neighbourhood remain the same.

This is a construction from the original N01b hypotheses. The lower bound
on `E0` is a conclusion about a replacement witness, not a new hypothesis
on the original witness.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open Set ContinuousFlexibility.Analysis ContinuousFlexibility.Blueprint
open scoped ContDiff

set_option backward.isDefEq.respectTransparency false

def normalizeMaterialE0 (T : MaterialData) : MaterialData :=
  { T with E0 := fun r => T.E0 r + Real.smoothTransition (2 - T.E0 r) }

theorem normalizeMaterialE0_apply (T : MaterialData) (r : ℝ) :
    (normalizeMaterialE0 T).E0 r = T.E0 r + Real.smoothTransition (2 - T.E0 r) := rfl

theorem le_normalizeMaterialE0 (T : MaterialData) (r : ℝ) :
    T.E0 r ≤ (normalizeMaterialE0 T).E0 r :=
  le_add_of_nonneg_right (Real.smoothTransition.nonneg _)

theorem normalizeMaterialE0_le_add_one (T : MaterialData) (r : ℝ) :
    (normalizeMaterialE0 T).E0 r ≤ T.E0 r + 1 := by
  rw [normalizeMaterialE0_apply]
  exact add_le_add le_rfl (Real.smoothTransition.le_one (2 - T.E0 r))

theorem normalizeMaterialE0_eq_of_two_le (T : MaterialData) {r : ℝ}
    (hr : 2 ≤ T.E0 r) : (normalizeMaterialE0 T).E0 r = T.E0 r := by
  rw [normalizeMaterialE0_apply, Real.smoothTransition.zero_of_nonpos (by linarith), add_zero]

theorem one_le_normalizeMaterialE0 (T : MaterialData) {r : ℝ}
    (hr : 0 ≤ T.E0 r) : 1 ≤ (normalizeMaterialE0 T).E0 r := by
  by_cases h : 1 ≤ T.E0 r
  · exact h.trans (le_normalizeMaterialE0 T r)
  · rw [normalizeMaterialE0_apply,
      Real.smoothTransition.one_of_one_le (by linarith)]
    linarith

theorem contDiffOn_normalizeMaterialE0
    {D : ReferenceData} {T : MaterialData} (hT : IsMaterialData D T) :
    ContDiffOn ℝ ∞ (normalizeMaterialE0 T).E0 (Ioo D.a D.b) := by
  have hE : ContDiffOn ℝ ∞ T.E0 (Ioo D.a D.b) := hT.1 T.E0 (by simp)
  exact hE.add (Real.smoothTransition.contDiff.comp_contDiffOn (contDiffOn_const.sub hE))

private theorem two_le_materialE0_of_nonneg {x : ℝ} (hx : 0 ≤ x) :
    2 ≤ materialE0 x := by
  have he : 1 ≤ Real.exp (1 : ℝ) := Real.one_le_exp_iff.mpr (by norm_num)
  have hlog : 0 ≤ materialLogFactor x :=
    Real.log_nonneg (he.trans (le_add_of_nonneg_right hx))
  have hexponent : 1 ≤ materialE0Exponent x :=
    le_add_of_nonneg_right (mul_nonneg (Real.rpow_nonneg hx _) hlog)
  have htwo : (2 : ℝ) ≤ Real.exp 1 := by
    simpa only [one_add_one_eq_two] using Real.add_one_le_exp (1 : ℝ)
  exact htwo.trans (Real.exp_le_exp.mpr hexponent)

/-- Every real power of the normalized weight satisfies the original
envelope estimate. The endpoint regions are unchanged; continuity controls
the compact middle and `M ≥ 1` supplies its envelope. -/
theorem normalizeMaterialE0_rpow_le_M
    {D : ReferenceData} {T : MaterialData} (hT : IsMaterialData D T) (A : ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∀ r ∈ Ioo D.a D.b,
      (normalizeMaterialE0 T).E0 r ^ A ≤ C * T.M r := by
  have hdata := hT
  obtain ⟨_, hpos, _, _, _, _, _, _, _, _, hends, henv, _⟩ := hdata
  obtain ⟨d0, δ, _, hδ, _, hL, hR⟩ := hends
  obtain ⟨C₀, hC₀, hCbound⟩ := henv A
  have hEpos (r : ℝ) (hr : r ∈ Ioo D.a D.b) :
      0 < (normalizeMaterialE0 T).E0 r :=
    (hpos r hr).2.2.1.trans_le (le_normalizeMaterialE0 T r)
  have hc : ContinuousOn (fun r => (normalizeMaterialE0 T).E0 r ^ A)
      (Ioo D.a D.b) :=
    ((contDiffOn_normalizeMaterialE0 hT).rpow_const_of_ne
      (fun r hr => (hEpos r hr).ne')).continuousOn
  have hsub : Icc (D.a + δ) (D.b - δ) ⊆ Ioo D.a D.b :=
    fun _ hr => ⟨by linarith [hr.1], by linarith [hr.2]⟩
  obtain ⟨B, hB⟩ := isCompact_Icc.bddAbove_image (hc.mono hsub)
  let C : ℝ := max C₀ (max B 1)
  have hC : 0 < C := hC₀.trans_le (le_max_left _ _)
  have hC₀C : C₀ ≤ C := le_max_left _ _
  have hBC : B ≤ C := (le_max_left B 1).trans (le_max_right _ _)
  refine ⟨C, hC, fun r hr => ?_⟩
  have hM : 0 ≤ T.M r := zero_le_one.trans (hpos r hr).2.2.2
  by_cases hl : r < D.a + δ
  · have he : 2 ≤ T.E0 r := by
      rw [(hL r ⟨hr.1, hl⟩).2.2.1]
      exact two_le_materialE0_of_nonneg (Real.sqrt_nonneg _)
    rw [normalizeMaterialE0_eq_of_two_le T he]
    exact (hCbound r hr).trans (mul_le_mul_of_nonneg_right hC₀C hM)
  by_cases hright : D.b - δ < r
  · have he : 2 ≤ T.E0 r := by
      rw [(hR r ⟨hright, hr.2⟩).2.2.1]
      exact two_le_materialE0_of_nonneg (Real.sqrt_nonneg _)
    rw [normalizeMaterialE0_eq_of_two_le T he]
    exact (hCbound r hr).trans (mul_le_mul_of_nonneg_right hC₀C hM)
  have hb : (normalizeMaterialE0 T).E0 r ^ A ≤ B :=
    hB ⟨r, ⟨le_of_not_gt hl, le_of_not_gt hright⟩, rfl⟩
  exact hb.trans (hBC.trans (le_mul_of_one_le_right hC.le (hpos r hr).2.2.2))

/-- Only the coefficient envelope changes; both actual jet norms are
definitionally unchanged. -/
theorem physicalNorm_normalizeMaterialE0 (T : MaterialData) (γ : ℝ)
    (s : ℕ) (f : PolarPoint → ℝ) :
    physicalNorm (normalizeMaterialE0 T) γ s f = physicalNorm T γ s f := rfl

theorem circleNorm_normalizeMaterialE0 (T : MaterialData) (γ : ℝ)
    (s : ℕ) (f : ℕ → ℝ → ℝ) :
    circleNorm (normalizeMaterialE0 T) γ s f = circleNorm T γ s f := rfl

theorem isPhysicalSpaces_normalizeMaterialE0
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    (hS : IsPhysicalSpaces D T S) : IsPhysicalSpaces D (normalizeMaterialE0 T) S := hS

/-- The normalized data satisfy every original material-data condition.
The existing radial partition places the samples inside the annulus, which
justifies monotonicity of the negative sample-weight powers. -/
theorem isMaterialData_normalizeMaterialE0
    {D : ReferenceData} {T : MaterialData}
    (hT : IsMaterialData D T) (hRef : IsAccumulatingProfile D) :
    IsMaterialData D (normalizeMaterialE0 T) := by
  have hpartition : RadialPartition D := by
    obtain ⟨_, h⟩ := hRef
    exact h.2.1
  have hsample : ∀ m, T.sample m ∈ Ioo D.a D.b :=
    materialSample_mem_radialCore hT hpartition
  have hdata := hT
  obtain ⟨hs, hp, hrho, hmono, hleft, hright, hradius, hrange, hinv, hderiv,
    hends, _, hdecay, hlog, hexpansion, hsampleCell, hwidth, hcompare⟩ := hdata
  refine ⟨?_, ?_, hrho, hmono, hleft, hright, hradius, hrange, hinv, hderiv,
    ?_, ?_, hdecay, hlog, ?_, hsampleCell, ?_, ?_⟩
  · intro f hf
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hf
    rcases hf with rfl | rfl | rfl | rfl | rfl
    · exact hs T.ell (by simp)
    · exact hs T.H (by simp)
    · exact contDiffOn_normalizeMaterialE0 hT
    · exact hs T.M (by simp)
    · exact hs T.rho (by simp)
  · intro r hr
    exact ⟨(hp r hr).1, (hp r hr).2.1,
      (hp r hr).2.2.1.trans_le (le_normalizeMaterialE0 T r), (hp r hr).2.2.2⟩
  · obtain ⟨d0, δ, hd0, hδ, hδlt, hL, hR⟩ := hends
    refine ⟨d0, δ, hd0, hδ, hδlt, ?_, ?_⟩
    · intro r hr
      have hv := hL r hr
      refine ⟨hv.1, hv.2.1, ?_, hv.2.2.2⟩
      rw [normalizeMaterialE0_eq_of_two_le T (by
        rw [hv.2.2.1]
        exact two_le_materialE0_of_nonneg (Real.sqrt_nonneg _))]
      exact hv.2.2.1
    · intro r hr
      have hv := hR r hr
      refine ⟨hv.1, hv.2.1, ?_, hv.2.2.2⟩
      rw [normalizeMaterialE0_eq_of_two_le T (by
        rw [hv.2.2.1]
        exact two_le_materialE0_of_nonneg (Real.sqrt_nonneg _))]
      exact hv.2.2.1
  · exact normalizeMaterialE0_rpow_le_M hT
  · intro n
    obtain ⟨c, hc, ⟨C, A, hC, hA, hbound⟩, hformula⟩ := hexpansion n
    refine ⟨c, hc, ⟨C, A, hC, hA, ?_⟩, hformula⟩
    intro j r hr
    exact (hbound j r hr).trans (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow (hp r hr).2.2.1.le (le_normalizeMaterialE0 T r) hA) hC)
  · obtain ⟨widths, K, hK, hw, hpair⟩ := hwidth
    refine ⟨widths, K, hK, fun m => ⟨(hw m).1, ?_, (hw m).2.2⟩, hpair⟩
    have he := Real.rpow_le_rpow_of_nonpos (hp (T.sample m) (hsample m)).2.2.1
      (le_normalizeMaterialE0 T (T.sample m)) (neg_nonpos.mpr hK.le)
    exact (mul_le_mul_of_nonneg_left he (inv_nonneg.mpr hK.le)).trans (hw m).2.1
  · obtain ⟨C, A, hC, hA, hc⟩ := hcompare
    refine ⟨C, A, hC, hA, fun m r hr => ?_⟩
    have hr' : r ∈ Ioo D.a D.b := hpartition.2.2.2.1 m hr
    have he := mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow (hp r hr').2.2.1.le (le_normalizeMaterialE0 T r) hA) hC.le
    exact ⟨(hc m r hr).1, (hc m r hr).2.1.trans he, (hc m r hr).2.2.trans he⟩

/-- The same controls satisfy the original PartA bounds after normalizing
the envelope. Neither the control functions nor their constants change. -/
theorem n01PartA_normalizeMaterialE0
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} (hT : IsMaterialData D T)
    (hA : N01PartA D T S C) : N01PartA D (normalizeMaterialE0 T) S C := by
  have hpartition : RadialPartition D := by
    obtain ⟨_, h⟩ := hA.1.1
    exact h.2.1
  have hsample : ∀ m, T.sample m ∈ Ioo D.a D.b :=
    materialSample_mem_radialCore hT hpartition
  refine ⟨hA.1, hA.2.1, hA.2.2.1, hA.2.2.2.1, ?_⟩
  intro s
  obtain ⟨B, hB, hb⟩ := hA.2.2.2.2 s
  refine ⟨B, hB, fun m r hr => ?_⟩
  exact (hb m r hr).trans (mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow (hT.2.1 _ (hsample (C.cell m))).2.2.1.le
      (le_normalizeMaterialE0 T (T.sample (C.cell m))) hB.le) hB.le)

/-- A concrete replacement of any N01b witness. The state model, geometry,
base and radius are identical; the envelope lower bound is newly proved. -/
theorem n01b_normalizeMaterialE0
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {base : ℕ} {ε : ℝ}
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (hA : N01PartA D T S C) (hB : N01PartB D S C base ε) :
    IsMaterialData D (normalizeMaterialE0 T) ∧
    IsPhysicalSpaces D (normalizeMaterialE0 T) S ∧
    N01PartA D (normalizeMaterialE0 T) S C ∧
    N01PartB D S C base ε ∧
    ∀ r ∈ Ioo D.a D.b, 1 ≤ (normalizeMaterialE0 T).E0 r :=
  ⟨isMaterialData_normalizeMaterialE0 hT hA.1.1,
    isPhysicalSpaces_normalizeMaterialE0 hS,
    n01PartA_normalizeMaterialE0 hT hA, hB,
    fun r hr => one_le_normalizeMaterialE0 T (hT.2.1 r hr).2.2.1.le⟩

/-- Increasing the material envelope weakens the negative-power reference
lower bound and preserves the same primitive geometric witness. -/
theorem n01PrimitiveGeometry_normalizeMaterialE0
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S}
    (hT : IsMaterialData D T) (hA : N01PartA D T S C)
    (hG : N01PrimitiveGeometry D T S C) :
    N01PrimitiveGeometry D (normalizeMaterialE0 T) S C := by
  obtain ⟨hloc, hχ, K, hK, hbound⟩ := hG
  refine ⟨hloc, hχ, K, hK, fun m r hr => ?_⟩
  have hpart : RadialPartition D := hA.1.1.choose_spec.2.1
  have hs := materialSample_mem_radialCore hT hpart (C.cell m)
  have hE : 0 < T.E0 (T.sample (C.cell m)) := (hT.2.1 _ hs).2.2.1
  have hpow := Real.rpow_le_rpow_of_nonpos hE
    (le_normalizeMaterialE0 T (T.sample (C.cell m))) (neg_nonpos.mpr hK.le)
  have hδ : 0 ≤ min (r - C.left m) (C.right m - r) :=
    le_min (sub_nonneg.mpr hr.1.le) (sub_nonneg.mpr hr.2.le)
  exact (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hpow (inv_nonneg.mpr hK.le)) hδ).trans (hbound m r hr)

/-- N01b can always be realized with a coefficient envelope at least one.
This is an existence-preserving construction from N01b itself. -/
theorem n01b_exists_normalized_material (h : N01bStatement) :
    ∃ A : RadialReference, ∃ T : MaterialData, ∃ S : PhysicalSpacesData,
      ∃ C : NonlinearGeometryData S, ∃ base : ℕ, ∃ ε : ℝ,
        IsMaterialData A.val T ∧ IsPhysicalSpaces A.val T S ∧
        N01PartA A.val T S C ∧ 0 < ε ∧ N01PartB A.val S C base ε ∧
        N01PrimitiveGeometry A.val T S C ∧
        ∀ r ∈ Ioo A.val.a A.val.b, 1 ≤ T.E0 r := by
  obtain ⟨A, T, S, C, base, ε, hT, hS, hA, hε, hB, hG⟩ := h
  have hn := n01b_normalizeMaterialE0 hT hS hA hB
  exact ⟨A, normalizeMaterialE0 T, S, C, base, ε,
    hn.1, hn.2.1, hn.2.2.1, hε, hn.2.2.2.1,
    n01PrimitiveGeometry_normalizeMaterialE0 hT hA hG, hn.2.2.2.2⟩

end ContinuousFlexibility.Statements
