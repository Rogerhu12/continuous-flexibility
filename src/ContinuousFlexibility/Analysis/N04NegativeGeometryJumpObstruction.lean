module

public import ContinuousFlexibility.Analysis.TameElementaryCalculus

/-!
# A statewise rescaling obstructs a current directional tower

Two continuous scalar families cannot agree at a nonzero reference value
and differ by a fixed nonunit factor on a punctured parameter neighborhood.
The conclusion uses only continuity, so directional towers of the
current-minus-reference functions already rule out such a jump.

The curve form applies after any shrinking of the open parameter domain.
The axis form is the one needed when a positive transport multiplier is
the identity at scalar parameter zero and has a different value elsewhere.
No gauge or frozen statement is modified in this module.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter ContinuousFlexibility.Statements
open scoped Topology

/-- A nonunit rescaling on a punctured germ forces a common continuous
reference value to vanish. -/
theorem n04NegativeGeometry_eq_zero_of_punctured_rescaling
    {f g : ℝ → ℝ} {a : ℝ}
    (hf : ContinuousAt f 0) (hg : ContinuousAt g 0)
    (heq : g =ᶠ[𝓝[≠] (0 : ℝ)] (fun t => f t / a))
    (hzero : g 0 = f 0) (ha : a ≠ 1) : f 0 = 0 := by
  have hflim : Tendsto (fun t => f t / a) (𝓝[≠] (0 : ℝ)) (𝓝 (f 0 / a)) :=
    (hf.tendsto.mono_left nhdsWithin_le_nhds).div_const a
  have hglim : Tendsto g (𝓝[≠] (0 : ℝ)) (𝓝 (g 0)) :=
    hg.tendsto.mono_left nhdsWithin_le_nhds
  have hlim : g 0 = f 0 / a :=
    tendsto_nhds_unique_of_eventuallyEq hglim hflim heq
  have hvalue : f 0 = f 0 / a := hzero.symm.trans hlim
  by_cases ha0 : a = 0
  · simpa only [ha0, div_zero] using hvalue
  · have hmul : f 0 * a = f 0 := (eq_div_iff ha0).mp hvalue
    have hprod : f 0 * (a - 1) = 0 := by
      calc
        f 0 * (a - 1) = f 0 * a - f 0 := by ring
        _ = 0 := sub_eq_zero.mpr hmul
    exact (mul_eq_zero.mp hprod).resolve_right (sub_ne_zero.mpr ha)

/-- Directional towers of two current-minus-reference functions cannot
coexist with a nonunit jump along any continuous parameter curve. -/
theorem n04NegativeGeometry_smooth_jump_contradiction
    {E : Type*} [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
    {U : Set E} {f g : E → ℝ} {c d a : ℝ}
    (Jf : SmoothDirections U (fun z => f z - c))
    (Jg : SmoothDirections U (fun z => g z - d))
    {x : E} (hx : x ∈ U) {γ : ℝ → E}
    (hγ : ContinuousAt γ 0) (hγzero : γ 0 = x)
    (heq : ∀ t : ℝ, t ≠ 0 → γ t ∈ U → g (γ t) = f (γ t) / a)
    (hzero : g x = f x) (hvalue : f x ≠ 0) (ha : a ≠ 1) : False := by
  have hfsub : ContinuousAt (fun z => f z - c) x :=
    Jf.continuousOn.continuousAt (Jf.open_domain.mem_nhds hx)
  have hgsub : ContinuousAt (fun z => g z - d) x :=
    Jg.continuousOn.continuousAt (Jg.open_domain.mem_nhds hx)
  have hc : ContinuousAt (fun _ : E => c) x := continuousAt_const
  have hd : ContinuousAt (fun _ : E => d) x := continuousAt_const
  have hf : ContinuousAt f x := by
    have hsum : ContinuousAt (fun z : E => (f z - c) + c) x := hfsub.add hc
    simpa only [sub_add_cancel] using hsum
  have hg : ContinuousAt g x := by
    have hsum : ContinuousAt (fun z : E => (g z - d) + d) x := hgsub.add hd
    simpa only [sub_add_cancel] using hsum
  have hfline : ContinuousAt (fun t : ℝ => f (γ t)) 0 :=
    hf.comp_of_eq hγ hγzero
  have hgline : ContinuousAt (fun t : ℝ => g (γ t)) 0 :=
    hg.comp_of_eq hγ hγzero
  have hmem : ∀ᶠ t : ℝ in 𝓝 0, γ t ∈ U :=
    hγ.eventually (Jf.open_domain.mem_nhds (hγzero.symm ▸ hx))
  have hevent : (fun t => g (γ t)) =ᶠ[𝓝[≠] (0 : ℝ)]
      (fun t => f (γ t) / a) := by
    filter_upwards [hmem.filter_mono nhdsWithin_le_nhds, self_mem_nhdsWithin]
      with t ht htne
    have ht0 : t ≠ 0 := by
      simpa only [mem_compl_iff, mem_singleton_iff] using htne
    exact heq t ht0 ht
  have hlinezero : g (γ 0) = f (γ 0) := by
    simpa only [hγzero] using hzero
  have hvanish := n04NegativeGeometry_eq_zero_of_punctured_rescaling
    hfline hgline hevent hlinezero ha
  apply hvalue
  simpa only [hγzero] using hvanish

/-- The scalar axis version requires no lower bound on the size of the
open neighborhood, so restricting to any smaller open neighborhood
containing zero cannot remove the obstruction. -/
theorem n04NegativeGeometry_axis_jump_contradiction
    {E : Type*} [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
    {U : Set (E × ℝ)} {f g : E × ℝ → ℝ} {c d a : ℝ}
    (Jf : SmoothDirections U (fun z => f z - c))
    (Jg : SmoothDirections U (fun z => g z - d))
    (hmem : (0 : E × ℝ) ∈ U)
    (heq : ∀ t : ℝ, t ≠ 0 → (0, t) ∈ U → g (0, t) = f (0, t) / a)
    (hzero : g 0 = f 0) (hvalue : f 0 ≠ 0) (ha : a ≠ 1) : False :=
  n04NegativeGeometry_smooth_jump_contradiction Jf Jg hmem
    (γ := fun t => (0, t)) (continuous_const.prodMk continuous_id).continuousAt
    rfl heq hzero hvalue ha

end ContinuousFlexibility.Analysis

/--
info: 'ContinuousFlexibility.Analysis.n04NegativeGeometry_axis_jump_contradiction' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms ContinuousFlexibility.Analysis.n04NegativeGeometry_axis_jump_contradiction
