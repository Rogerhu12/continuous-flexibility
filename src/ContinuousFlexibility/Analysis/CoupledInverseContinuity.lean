module

public import ContinuousFlexibility.Analysis.TameInverseTheorem

/-!
# Continuity of the coupled inverse from its actual tame estimates

The resolvent identity converts a uniform linear-family estimate into
joint continuity of the inverse in the original seminorm topologies.
This applies to diagonal circle inverses and to the recovered control
inverse without imposing an operator-norm topology on a Fréchet space.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter
open scoped Topology
open ContinuousFlexibility.Statements

section Continuity

variable {X Y Z : Type*}
  [TopologicalSpace X] [AddCommGroup X] [Module ℝ X]
  [TopologicalSpace Y] [AddCommGroup Y] [Module ℝ Y]
  [TopologicalSpace Z] [AddCommGroup Z] [Module ℝ Z]
  [IsTopologicalAddGroup Z]

/-- The exact resolvent identity and the stated linear tame bounds already
give the joint continuity required by Hamilton's inverse-family theorem. -/
theorem coupled_continuousOn_inverseFamily_of_tame
    {p : ℕ → Seminorm ℝ X} {q : ℕ → Seminorm ℝ Y} {r : ℕ → Seminorm ℝ Z}
    (hq : Monotone q) (htp : WithSeminorms p) (htq : WithSeminorms q)
    (htr : WithSeminorms r) {U : Set X}
    (L : X → Y →ₗ[ℝ] Z) (V : X → Z →ₗ[ℝ] Y)
    (hL : ContinuousOn (fun z : X × Y => L z.1 z.2) (U ×ˢ univ))
    (hleft : ∀ x ∈ U, ∀ y, V x (L x y) = y)
    (hright : ∀ x ∈ U, ∀ z, L x (V x z) = z)
    (hV : LinearFamilyTame p q r U V) :
    ContinuousOn (fun z : X × Z => V z.1 z.2) (U ×ˢ univ) := by
  obtain ⟨loss, base, hbound⟩ := hV
  intro z0 hz0
  apply (htq.tendsto_nhds _ _).mpr
  intro s ε hε
  let t : ℕ := max s base
  obtain ⟨C, hC, hCs⟩ := hbound t (le_max_right _ _)
  let u0 : Y := V z0.1 z0.2
  let error : X × Z → Z := fun z =>
    (z.2 - z0.2) - (L z.1 u0 - L z0.1 u0)
  have hfixed : ContinuousOn (fun z : X × Z => L z.1 u0) (U ×ˢ univ) :=
    hL.comp (continuous_fst.prodMk continuous_const).continuousOn
      (fun z hz => ⟨hz.1, mem_univ u0⟩)
  have herr : ContinuousOn error (U ×ˢ univ) :=
    (continuous_snd.continuousOn.sub continuousOn_const).sub
      (hfixed.sub continuousOn_const)
  let bound : X × Z → ℝ := fun z =>
    C * (r (t + loss) (error z) + (1 + p (t + loss) z.1) * r base (error z))
  have herror (n : ℕ) : ContinuousOn (fun z => r n (error z)) (U ×ˢ univ) :=
    (htr.continuous_seminorm n).comp_continuousOn herr
  have hparameter : ContinuousOn (fun z : X × Z => 1 + p (t + loss) z.1)
      (U ×ˢ univ) :=
    continuousOn_const.add
      ((htp.continuous_seminorm _).comp continuous_fst).continuousOn
  have hboundcont : ContinuousOn bound (U ×ˢ univ) :=
    ((herror _).add (hparameter.mul (herror _))).const_mul C
  have hzero : bound z0 = 0 := by
    simp only [bound, error, sub_self, map_zero, mul_zero, add_zero]
  have hlim := hboundcont z0 hz0
  change Tendsto bound (𝓝[U ×ˢ univ] z0) (𝓝 (bound z0)) at hlim
  rw [hzero] at hlim
  filter_upwards [self_mem_nhdsWithin, hlim.eventually (gt_mem_nhds hε)] with z hz hsmall
  have hres : V z.1 z.2 - V z0.1 z0.2 = V z.1 (error z) :=
    inverseFamily_resolvent L V (hleft z.1 hz.1) (hright z0.1 hz0.1) z0.2 z.2
  calc
    q s (V z.1 z.2 - V z0.1 z0.2) ≤ q t (V z.1 z.2 - V z0.1 z0.2) :=
      hq (le_max_left _ _) _
    _ = q t (V z.1 (error z)) := by rw [hres]
    _ ≤ bound z := hCs z.1 hz.1 (error z)
    _ < ε := hsmall

end Continuity

section Smoothness

variable {X Y Z : Type*}
  [TopologicalSpace X] [AddCommGroup X] [Module ℝ X]
  [IsTopologicalAddGroup X] [ContinuousSMul ℝ X]
  [TopologicalSpace Y] [AddCommGroup Y] [Module ℝ Y]
  [IsTopologicalAddGroup Y] [ContinuousSMul ℝ Y] [T2Space Y]
  [TopologicalSpace Z] [AddCommGroup Z] [Module ℝ Z]
  [IsTopologicalAddGroup Z] [ContinuousSMul ℝ Z] [T2Space Z]

/-- In the coupled construction the inverse-family regularity follows
from the two exact inverse identities and its established tame estimates. -/
theorem coupled_smoothTameOn_inverseFamily_of_tame
    {p : ℕ → Seminorm ℝ X} {q : ℕ → Seminorm ℝ Y} {r : ℕ → Seminorm ℝ Z}
    (hp : Monotone p) (hq : Monotone q) (hr : Monotone r)
    (htp : WithSeminorms p) (htq : WithSeminorms q) (htr : WithSeminorms r)
    {U : Set X} (hU : IsOpen U)
    (L : X → Y →L[ℝ] Z) (V : X → Z →ₗ[ℝ] Y)
    (hL : SmoothTameOn (pairGrading p q) r (U ×ˢ univ)
      (fun z : X × Y => L z.1 z.2))
    (hleft : ∀ x ∈ U, ∀ y, V x (L x y) = y)
    (hright : ∀ x ∈ U, ∀ z, L x (V x z) = z)
    (hV : LinearFamilyTame p q r U V) :
    SmoothTameOn (pairGrading p r) q (U ×ˢ univ)
      (fun z : X × Z => V z.1 z.2) := by
  have hcontinuous : ContinuousOn (fun z : X × Z => V z.1 z.2) (U ×ˢ univ) :=
    coupled_continuousOn_inverseFamily_of_tame hq htp htq htr
      (fun x => (L x).toLinearMap) V hL.choose.continuousOn hleft hright hV
  exact smoothTameOn_inverseFamily hp hq hr htp htq htr hU L V
    hL hleft hright hcontinuous hV

end Smoothness

end ContinuousFlexibility.Analysis
