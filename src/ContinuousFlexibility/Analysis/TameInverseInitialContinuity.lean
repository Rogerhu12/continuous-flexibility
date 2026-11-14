module

public import ContinuousFlexibility.Analysis.TameInverseFamily

/-!
# Initial continuity of a tame inverse family

The exact resolvent identity reduces continuity of the inverse to joint
continuity of the forward family and its actual linear-family estimate.
No operator-norm topology or prior continuity of the inverse is assumed.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter ContinuousFlexibility.Statements
open scoped Topology

variable {X Y Z : Type*}
  [TopologicalSpace X] [AddCommGroup X] [Module ℝ X]
  [TopologicalSpace Y] [AddCommGroup Y] [Module ℝ Y]
  [TopologicalSpace Z] [AddCommGroup Z] [Module ℝ Z]
  [IsTopologicalAddGroup Z]

theorem continuousOn_inverseFamily_of_linearFamilyTame
    {p : ℕ → Seminorm ℝ X} {q : ℕ → Seminorm ℝ Y} {r : ℕ → Seminorm ℝ Z}
    (hp : WithSeminorms p) (hq : WithSeminorms q) (hr : WithSeminorms r)
    (hqmono : Monotone q) {U : Set X}
    (L : X → Y →ₗ[ℝ] Z) (V : X → Z →ₗ[ℝ] Y)
    (hL : ContinuousOn (fun z : X × Y => L z.1 z.2) (U ×ˢ univ))
    (hleft : ∀ x ∈ U, ∀ y, V x (L x y) = y)
    (hright : ∀ x ∈ U, ∀ y, L x (V x y) = y)
    (hT : LinearFamilyTame p q r U V) :
    ContinuousOn (fun z : X × Z => V z.1 z.2) (U ×ˢ univ) := by
  obtain ⟨loss, base, hb⟩ := hT
  intro z₀ hz₀
  apply (hq.tendsto_nhds _ _).mpr
  intro s ε hε
  let t : ℕ := max s base
  obtain ⟨C, hC, hbound⟩ := hb t (le_max_right _ _)
  let d : X × Z → Z := fun z =>
    (z.2 - z₀.2) - (L z.1 (V z₀.1 z₀.2) - L z₀.1 (V z₀.1 z₀.2))
  let A : X × Z → ℝ := fun z =>
    C * (r (t + loss) (d z) + (1 + p (t + loss) z.1) * r base (d z))
  have hfixed : ContinuousOn (fun z : X × Z => L z.1 (V z₀.1 z₀.2)) (U ×ˢ univ) :=
    hL.comp (continuous_fst.prodMk continuous_const).continuousOn
      (fun z hz => ⟨hz.1, mem_univ _⟩)
  have hd : ContinuousOn d (U ×ˢ univ) :=
    (continuous_snd.continuousOn.sub continuousOn_const).sub
      (hfixed.sub continuousOn_const)
  have hrd (n : ℕ) : ContinuousOn (fun z => r n (d z)) (U ×ˢ univ) :=
    (hr.continuous_seminorm n).comp_continuousOn hd
  have hpz : ContinuousOn (fun z : X × Z => p (t + loss) z.1) (U ×ˢ univ) :=
    ((hp.continuous_seminorm (t + loss)).comp continuous_fst).continuousOn
  have hA : ContinuousOn A (U ×ˢ univ) :=
    ((hrd (t + loss)).add ((continuousOn_const.add hpz).mul (hrd base))).const_mul C
  have hA₀ : A z₀ = 0 := by
    simp only [A, d, sub_self, sub_zero, map_zero, mul_zero, add_zero]
  have hlim : Tendsto A (𝓝[U ×ˢ univ] z₀) (𝓝 (0 : ℝ)) := by
    have hlim' : Tendsto A (𝓝[U ×ˢ univ] z₀) (𝓝 (A z₀)) := hA z₀ hz₀
    simpa only [hA₀] using hlim'
  filter_upwards [hlim.eventually (gt_mem_nhds hε), self_mem_nhdsWithin] with z hz hzU
  have hid : V z.1 z.2 - V z₀.1 z₀.2 = V z.1 (d z) :=
    inverseFamily_resolvent L V (hleft z.1 hzU.1) (hright z₀.1 hz₀.1) z₀.2 z.2
  have hupper : q s (V z.1 z.2 - V z₀.1 z₀.2) ≤ A z := by
    calc
      _ ≤ q t (V z.1 z.2 - V z₀.1 z₀.2) := hqmono (le_max_left _ _) _
      _ = q t (V z.1 (d z)) := congrArg (q t) hid
      _ ≤ A z := hbound z.1 hzU.1 (d z)
  exact hupper.trans_lt hz

end ContinuousFlexibility.Analysis
