import ContinuousFlexibility.Analysis.TameInverseFamily

/-!
# Joint continuity forced by the actual forward family and tame inverse bounds

The inverse identities reduce a changing parameter and source to one
vanishing source error. At every fixed output order the tame estimate
then tends to zero in the original topology defined by the seminorms.
No continuity of the inverse is assumed, and no operator norm is used.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter
open scoped Topology
open ContinuousFlexibility.Statements

variable {X Y Z : Type*}
  [TopologicalSpace X] [AddCommGroup X] [Module ℝ X]
  [TopologicalSpace Y] [AddCommGroup Y] [Module ℝ Y]
  [TopologicalSpace Z] [AddCommGroup Z] [Module ℝ Z]

/-- The actual two-sided inverse is jointly continuous once its true
forward family is jointly continuous and its linear-family bound holds. -/
theorem n07a_inverseFamily_continuousOn_of_linearFamilyTame
    {p : ℕ → Seminorm ℝ X} {q : ℕ → Seminorm ℝ Y} {r : ℕ → Seminorm ℝ Z}
    (hp : WithSeminorms p) (hq : WithSeminorms q) (hr : WithSeminorms r)
    (hmono : Monotone q) {U : Set X}
    (L : X → Y →ₗ[ℝ] Z) (V : X → Z →ₗ[ℝ] Y)
    (hL : ContinuousOn (fun z : X × Y => L z.1 z.2) (U ×ˢ univ))
    (hleft : ∀ x ∈ U, ∀ u, V x (L x u) = u)
    (hright : ∀ x ∈ U, ∀ f, L x (V x f) = f)
    (hV : LinearFamilyTame p q r U V) :
    ContinuousOn (fun z : X × Z => V z.1 z.2) (U ×ˢ univ) := by
  let : IsTopologicalAddGroup Z := hr.isTopologicalAddGroup
  obtain ⟨loss, base, hbound⟩ := hV
  intro z₀ hz₀
  let u : Y := V z₀.1 z₀.2
  let e : X × Z → Z := fun z => z.2 - L z.1 u
  have hecont : ContinuousOn e (U ×ˢ univ) :=
    continuous_snd.continuousOn.sub
      (hL.comp (continuous_fst.prodMk continuous_const).continuousOn
        (fun z hz => ⟨hz.1, mem_univ _⟩))
  have he : Tendsto e (𝓝[U ×ˢ univ] z₀) (𝓝 0) := by
    have hec : Tendsto e (𝓝[U ×ˢ univ] z₀) (𝓝 (e z₀)) := hecont z₀ hz₀
    simpa only [e, u, hright z₀.1 hz₀.1 z₀.2, sub_self] using hec
  have heq (z : X × Z) (hz : z.1 ∈ U) : V z.1 z.2 - u = V z.1 (e z) := by
    dsimp only [e]
    rw [map_sub, hleft z.1 hz u]
  apply (hq.tendsto_nhds (fun z : X × Z => V z.1 z.2) u).mpr
  intro s η hη
  let t : ℕ := max base s
  obtain ⟨C, _hC, hCbound⟩ := hbound t (le_max_left _ _)
  have hhigh : Tendsto (fun z : X × Z => r (t + loss) (e z))
      (𝓝[U ×ˢ univ] z₀) (𝓝 0) := by
    simpa only [map_zero, Function.comp_def] using
      ((hr.continuous_seminorm (t + loss)).tendsto 0).comp he
  have hlow : Tendsto (fun z : X × Z => r base (e z))
      (𝓝[U ×ˢ univ] z₀) (𝓝 0) := by
    simpa only [map_zero, Function.comp_def] using
      ((hr.continuous_seminorm base).tendsto 0).comp he
  have hparam : Tendsto (fun z : X × Z => p (t + loss) z.1)
      (𝓝[U ×ˢ univ] z₀) (𝓝 (p (t + loss) z₀.1)) :=
    (((hp.continuous_seminorm (t + loss)).comp continuous_fst).tendsto z₀).mono_left
      nhdsWithin_le_nhds
  have hzero : Tendsto
      (fun z : X × Z => C * (r (t + loss) (e z) +
        (1 + p (t + loss) z.1) * r base (e z)))
      (𝓝[U ×ˢ univ] z₀) (𝓝 0) := by
    simpa only [mul_zero, add_zero] using
      tendsto_const_nhds.mul (hhigh.add ((tendsto_const_nhds.add hparam).mul hlow))
  filter_upwards [hzero.eventually_lt_const hη, self_mem_nhdsWithin] with z hz hzU
  have hb : q s (V z.1 z.2 - u) ≤
      C * (r (t + loss) (e z) + (1 + p (t + loss) z.1) * r base (e z)) := by
    rw [heq z hzU.1]
    exact (hmono (le_max_right base s) _).trans (hCbound z.1 hzU.1 (e z))
  exact hb.trans_lt hz

end ContinuousFlexibility.Analysis
