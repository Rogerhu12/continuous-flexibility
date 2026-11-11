import ContinuousFlexibility.Radial.SelectedRetainedCone
import ContinuousFlexibility.Radial.SelectedGrowingCone
import ContinuousFlexibility.Radial.SelectedBoundaryMargin

/-!
# Actual first-band growing lifts with exactly retained matching states
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open Real Set Filter
open scoped Topology ContDiff
open ContinuousFlexibility.Statements

theorem SeedRetainedFirstCone.profile_old_germ {S : SelectedTailData}
    {right : Bool} {length r : ℝ} (T : SeedRetainedFirstCone S right length)
    (hr : r ∈ radialCore (S.family S.sigma))
    (ho : if right then S.cut right S.chain.index ≤ r else r ≤ S.cut right S.chain.index) :
    T.tail.profile =ᶠ[𝓝 r] (S.family S.sigma).w := by
  by_cases he : r = S.cut right S.chain.index
  · subst r
    exact (T.cone_germ _ right_mem_uIcc).trans T.old_cone_germ.symm
  · have ht : r ∈ radialTailInterval (S.family S.sigma) right (S.cut right S.chain.index) := by
      cases right
      · exact ⟨hr.1, lt_of_le_of_ne ho he⟩
      · exact ⟨lt_of_le_of_ne ho (Ne.symm he), hr.2⟩
    have hopen : IsOpen (radialTailInterval (S.family S.sigma) right
        (S.cut right S.chain.index)) := by
      cases right <;> exact isOpen_Ioo
    exact Filter.eventuallyEq_of_mem (hopen.mem_nhds ht) (fun t ht => (T.tail.tail_eq t ht).1)

/-- The selected first-band incoming solution extends over the actual
new cone while retaining every outward germ from the old join onward. -/
theorem SeedRetainedFirstCone.exists_growingIncoming {S : SelectedTailData}
    (hS : IsSelectedTail S) {right : Bool} {length : ℝ}
    (T : SeedRetainedFirstCone S right length) {j : ℕ}
    (hj : 2 ≤ j) (heven : Even j)
    (hband : radialFrequencyBand S.chain S.Cstar S.chain.index j)
    (hu : ContDiff ℝ ∞ (S.incoming right j))
    (hcone : ∃ C : ℝ, 0 < C ∧ ∀ r ∈ uIcc (S.cut right S.chain.index)
        (S.joinInner right S.chain.index),
      (S.family S.sigma).w =ᶠ[𝓝 r] (fun t => C * t)) :
    ∃ U : ℝ → ℝ, ContDiff ℝ ∞ U ∧
      EqOn U (fun r => r ^ (if right then (j : ℝ) else -(j : ℝ)) /
        (S.cut right S.chain.index) ^ (if right then (j : ℝ) else -(j : ℝ)))
        (uIcc T.inner (S.joinInner right S.chain.index)) ∧
      (∀ r, (if right then S.joinInner right S.chain.index ≤ r
        else r ≤ S.joinInner right S.chain.index) → U =ᶠ[𝓝 r] S.incoming right j) ∧
      (∀ r ∈ uIcc T.inner (S.entry right S.chain.index),
        radialJacobi ((j : ℝ) ^ 2) T.tail.profile U r = 0) ∧
      0 < U (S.joinInner right S.chain.index) := by
  let D := S.family S.sigma
  let c := S.cut right S.chain.index
  let p := S.joinInner right S.chain.index
  let e := S.entry right S.chain.index
  let ν : ℝ := if right then (j : ℝ) else -(j : ℝ)
  have hD : RadialProfileGeometry D :=
    MorseChainRealization.geometry (hS.2.2.2.1 S.sigma hS.2.2.1).1
  have hm := hS.2.2.2.2.2 right S.chain.index j hj heven hband
  rcases hm with ⟨hc, he, hp, _, horder, _, hfirst, _, _, _, hODE, _, _⟩
  have h₀ : S.incoming right j c = 1 := by
    have hh := hfirst
    rw [if_pos rfl] at hh
    exact hh.2.1
  have h₁ : deriv (S.incoming right j) c = ν / c := by
    have hh := hfirst
    rw [if_pos rfl] at hh
    exact hh.2.2
  obtain ⟨C, _, hCg⟩ := hcone
  have hCeq : C = T.coneScale := by
    have hh : C * c = T.coneScale * c :=
      (hCg c left_mem_uIcc).eq_of_nhds.symm.trans T.old_cone_germ.eq_of_nhds
    exact mul_right_cancel₀ (hD.1.trans hc.1).ne' hh
  have hcone' (r : ℝ) (hr : r ∈ uIcc c p) :
      D.w =ᶠ[𝓝 r] (fun t => T.coneScale * t) := by
    simpa only [hCeq] using hCg r hr
  have horder' : if right then T.inner < c ∧ c < p ∧ p < e
      else e < p ∧ p < c ∧ c < T.inner := by
    cases right
    · exact ⟨horder.1, horder.2, T.inner_order⟩
    · exact ⟨T.inner_order, horder.1, horder.2⟩
  have hν : ν ^ 2 = (j : ℝ) ^ 2 := by
    cases right <;> simp only [ν, Bool.false_eq_true, ite_false, ite_true, neg_sq]
  have hold (r : ℝ) (hr : r ∈ uIcc c e) :
      T.tail.profile =ᶠ[𝓝 r] D.w := by
    have hrCore : r ∈ radialCore D :=
      ⟨(lt_min hc.1 he.1).trans_le hr.1, hr.2.trans_lt (max_lt hc.2 he.2)⟩
    apply T.profile_old_germ hrCore
    cases right
    · rw [uIcc_of_ge (horder.1.trans horder.2).le] at hr
      exact hr.2
    · rw [uIcc_of_le (horder.1.trans horder.2).le] at hr
      exact hr.1
  obtain ⟨U, hUs, _, hUpower, hUret, hUeq⟩ := exists_radialConeIncoming_graft hD
    T.inner_pos hc hp he horder' hcone' hu hODE.2 h₀ h₁ hν T.cone_germ hold
  refine ⟨U, hUs, hUpower, hUret, hUeq, ?_⟩
  rw [hUpower right_mem_uIcc]
  exact div_pos (rpow_pos_of_pos (hD.1.trans hp.1) ν)
    (rpow_pos_of_pos (hD.1.trans hc.1) ν)

/-- Normalize at the actual old join. The stand-in is the exact growing
power on the complete long cap, and the selected incoming is changed only
by a positive constant on every outward germ. -/
theorem SeedRetainedFirstCone.exists_normalized_growingIncoming {S : SelectedTailData}
    (hS : IsSelectedTail S) {right : Bool} {length : ℝ}
    (T : SeedRetainedFirstCone S right length) {j : ℕ}
    (hj : 2 ≤ j) (heven : Even j)
    (hband : radialFrequencyBand S.chain S.Cstar S.chain.index j)
    (hu : ContDiff ℝ ∞ (S.incoming right j))
    (hcone : ∃ C : ℝ, 0 < C ∧ ∀ r ∈ uIcc (S.cut right S.chain.index)
        (S.joinInner right S.chain.index),
      (S.family S.sigma).w =ᶠ[𝓝 r] (fun t => C * t)) :
    ∃ U : ℝ → ℝ, ∃ α : ℝ, 0 < α ∧ ContDiff ℝ ∞ U ∧
      U (S.joinInner right S.chain.index) = 1 ∧
      EqOn U (fun r => r ^ (if right then (j : ℝ) else -(j : ℝ)) /
        (S.joinInner right S.chain.index) ^ (if right then (j : ℝ) else -(j : ℝ)))
        (uIcc T.inner (S.joinInner right S.chain.index)) ∧
      (∀ r, (if right then S.joinInner right S.chain.index ≤ r
        else r ≤ S.joinInner right S.chain.index) →
        U =ᶠ[𝓝 r] (fun t => α * S.incoming right j t)) ∧
      ∀ r ∈ uIcc T.inner (S.entry right S.chain.index),
        radialJacobi ((j : ℝ) ^ 2) T.tail.profile U r = 0 := by
  obtain ⟨V, hVs, hVpower, hVret, hVeq, hVp⟩ :=
    T.exists_growingIncoming hS hj heven hband hu hcone
  let p := S.joinInner right S.chain.index
  let c := S.cut right S.chain.index
  let ν : ℝ := if right then (j : ℝ) else -(j : ℝ)
  have hD : RadialProfileGeometry (S.family S.sigma) :=
    MorseChainRealization.geometry (hS.2.2.2.1 S.sigma hS.2.2.1).1
  have hm := hS.2.2.2.2.2 right S.chain.index j hj heven hband
  have hcpos : 0 < c := hD.1.trans hm.1.1
  have hppos : 0 < p := hD.1.trans hm.2.2.1.1
  have hVpEq : V p = p ^ ν / c ^ ν := hVpower right_mem_uIcc
  refine ⟨fun r => (V p)⁻¹ * V r, (V p)⁻¹, inv_pos.mpr hVp,
    contDiff_const.mul hVs, inv_mul_cancel₀ hVp.ne', ?_, ?_, ?_⟩
  · intro r hr
    change (V p)⁻¹ * V r = r ^ ν / p ^ ν
    rw [hVpower hr, hVpEq]
    field_simp [(rpow_pos_of_pos hcpos ν).ne', (rpow_pos_of_pos hppos ν).ne']
    <;> ring
  · intro r hr
    exact (hVret r hr).fun_comp (fun t => (V p)⁻¹ * t)
  · intro r hr
    rw [radialJacobi_const_mul, hVeq r hr, mul_zero]

/-- A local profile dilation suffices to transport the actual equation
of a grafted stand-in to the final, common reference geometry. -/
theorem radialJacobi_radiusScale_of_profile_germ {E : ReferenceData}
    {w U : ℝ → ℝ} {κ β α J r : ℝ} (hκ : κ ≠ 0)
    (hw : E.w =ᶠ[𝓝 (κ * r)] radialRadiusScale κ (β * κ) w)
    (hU : radialJacobi J w U r = 0) :
    radialJacobi J E.w (radialRadiusScale κ α U) (κ * r) = 0 :=
  (radialJacobi_eq_of_profile_germ hw).trans
    (radialJacobi_radialRadiusScale_eq_zero hκ hU)

/-- On the same final reference, a retained incoming germ changes the
selected angle by exactly zero, including at the old join. -/
theorem radialState_radiusScale_angle_of_scaled_germ {D E : ReferenceData} (j : ℕ)
    {κ β A B α r scale : ℝ} {U u v : ℝ → ℝ}
    (hκ : κ ≠ 0) (hβ : β ≠ 0) (hA : A ≠ 0) (hB : B ≠ 0) (hα : α ≠ 0)
    (hprofile : E.w (κ * r) = (β * κ) * D.w r)
    (hu : DifferentiableAt ℝ u r) (hg : U =ᶠ[𝓝 r] (fun t => α * u t)) :
    radialAngleSine
      (radialState E j (κ * r) ((β * κ) * scale) (radialRadiusScale κ A U))
      (radialState E j (κ * r) ((β * κ) * scale) (radialRadiusScale κ B v)) =
      radialAngleSine (radialState D j r scale u) (radialState D j r scale v) := by
  rw [radialState_radiusScale_angle j hκ hβ hA hB hprofile U v]
  have hstate : radialState D j r scale U =
      radialState D j r scale (fun t => α * u t) := by
    simp only [radialState, hg.eq_of_nhds, hg.deriv_eq]
  rw [hstate, radialState_const_mul D j r scale α hu, radialAngleSine_scale_left hα]

end ContinuousFlexibility.Radial
