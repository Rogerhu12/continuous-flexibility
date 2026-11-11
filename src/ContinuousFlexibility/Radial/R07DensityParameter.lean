import ContinuousFlexibility.Radial.R07TailParameter
import ContinuousFlexibility.Radial.R07DeepTailDensity
import Mathlib.Analysis.Calculus.IteratedDeriv.FaaDiBruno

/-!
# Joint continuity of all physical deep-tail density jets

Finite Faà di Bruno and Leibniz formulas transfer joint continuity of all
profile jets through a fixed smooth coordinate change and multiplication by
a fixed smooth weight.  The normalized physical density has precisely this
form, since the two endpoint radii are fixed throughout the height family.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open Real Set Filter Function
open scoped Topology ContDiff BigOperators

/-- Joint continuity of all spatial jets is preserved by composition with
a fixed smooth real coordinate change. -/
theorem continuousOn_parametric_iteratedDeriv_comp {X : Type*} [TopologicalSpace X]
    {f : X → ℝ → ℝ} {g : ℝ → ℝ} {s t : Set ℝ}
    (hf : ∀ p, ContDiff ℝ ∞ (f p))
    (hjets : ∀ k, ContinuousOn (fun z : X × ℝ => iteratedDeriv k (f z.1) z.2)
      {z | z.2 ∈ t})
    (hg : ContDiff ℝ ∞ g) (hmap : MapsTo g s t) (n : ℕ) :
    ContinuousOn (fun z : X × ℝ => iteratedDeriv n (fun x => f z.1 (g x)) z.2)
      {z | z.2 ∈ s} := by
  have hsum : ContinuousOn (fun z : X × ℝ =>
      ∑ c : OrderedFinpartition n,
        iteratedDeriv c.length (f z.1) (g z.2) *
          ∏ i, iteratedDeriv (c.partSize i) g z.2) {z | z.2 ∈ s} := by
    apply continuousOn_finsetSum Finset.univ
    intro c _
    have hleft : ContinuousOn (fun z : X × ℝ =>
        iteratedDeriv c.length (f z.1) (g z.2)) {z | z.2 ∈ s} :=
      (hjets c.length).comp
        (continuous_fst.prodMk (hg.continuous.comp continuous_snd)).continuousOn
        (fun z hz => hmap hz)
    have hright : Continuous (fun z : X × ℝ =>
        ∏ i, iteratedDeriv (c.partSize i) g z.2) := by
      apply continuous_finsetProd Finset.univ
      intro i _
      exact (hg.continuous_iteratedDeriv (c.partSize i) (by simp)).comp continuous_snd
    exact hleft.mul hright.continuousOn
  refine hsum.congr ?_
  intro z _
  exact iteratedDeriv_comp_eq_sum_orderedFinpartition
    (hf z.1).contDiffAt hg.contDiffAt (by simp)

/-- Multiplication by a fixed smooth weight also preserves joint continuity
of every spatial jet. -/
theorem continuousOn_parametric_iteratedDeriv_fixed_mul {X : Type*} [TopologicalSpace X]
    {f : X → ℝ → ℝ} {g : ℝ → ℝ} {s : Set ℝ}
    (hf : ∀ p, ContDiff ℝ ∞ (f p))
    (hjets : ∀ k, ContinuousOn (fun z : X × ℝ => iteratedDeriv k (f z.1) z.2)
      {z | z.2 ∈ s})
    (hg : ContDiff ℝ ∞ g) (n : ℕ) :
    ContinuousOn (fun z : X × ℝ => iteratedDeriv n (fun x => g x * f z.1 x) z.2)
      {z | z.2 ∈ s} := by
  have hsum : ContinuousOn (fun z : X × ℝ =>
      ∑ i ∈ Finset.range (n + 1),
        (n.choose i : ℝ) * iteratedDeriv i g z.2 * iteratedDeriv (n - i) (f z.1) z.2)
      {z | z.2 ∈ s} := by
    apply continuousOn_finsetSum (Finset.range (n + 1))
    intro i _
    have hi : Continuous (fun z : X × ℝ => iteratedDeriv i g z.2) :=
      (hg.continuous_iteratedDeriv i (by simp)).comp continuous_snd
    exact (continuousOn_const.mul hi.continuousOn).mul (hjets (n - i))
  refine hsum.congr ?_
  intro z _
  exact iteratedDeriv_mul (hg.contDiffAt.of_le (by simp))
    ((hf z.1).contDiffAt.of_le (by simp))

/-- The combined form needed for a fixed physical gauge and logarithmic
radius coordinate. -/
theorem continuousOn_parametric_iteratedDeriv_weight_comp {X : Type*} [TopologicalSpace X]
    {f : X → ℝ → ℝ} {g h : ℝ → ℝ} {s t : Set ℝ}
    (hf : ∀ p, ContDiff ℝ ∞ (f p))
    (hjets : ∀ k, ContinuousOn (fun z : X × ℝ => iteratedDeriv k (f z.1) z.2)
      {z | z.2 ∈ t})
    (hg : ContDiff ℝ ∞ g) (hh : ContDiff ℝ ∞ h) (hmap : MapsTo h s t) (n : ℕ) :
    ContinuousOn (fun z : X × ℝ => iteratedDeriv n (fun x => g x * f z.1 (h x)) z.2)
      {z | z.2 ∈ s} :=
  continuousOn_parametric_iteratedDeriv_fixed_mul (fun p => (hf p).comp hh)
    (fun k => continuousOn_parametric_iteratedDeriv_comp hf hjets hh hmap k) hg n

/-- The exact normalized density in `TailPhysicalRelation` has jointly
continuous spatial jets whenever the physical profile does and the endpoint
used for normalization is fixed. -/
theorem continuousOn_r07PhysicalDensity_iteratedDeriv {X : Type*} [TopologicalSpace X]
    {D : X → Statements.ReferenceData} {s t : Set ℝ} (side : Bool) (j : ℕ)
    {endpoint : ℝ} (he : 0 < endpoint)
    (hfixed : ∀ p, (if side then (D p).b else (D p).a) = endpoint)
    (hw : ∀ p, ContDiff ℝ ∞ (D p).w)
    (hjets : ∀ k, ContinuousOn (fun z : X × ℝ => iteratedDeriv k (D z.1).w z.2)
      {z | z.2 ∈ t})
    (hmap : MapsTo (Statements.tailPhysicalRadius side) s t) (n : ℕ) :
    ContinuousOn (fun z : X × ℝ => iteratedDeriv n (r07PhysicalDensity (D z.1) side j) z.2)
      {z | z.2 ∈ s} := by
  let weight : ℝ → ℝ := fun x =>
    (Statements.tailPhysicalRadius side x / endpoint) ^ (2 * (j : ℝ) ^ 2) /
      Statements.tailPhysicalRadius side x
  have hr := r07_contDiff_radius side
  have hg : ContDiff ℝ ∞ weight :=
    ((hr.div_const endpoint).rpow_const_of_ne
      (fun x => (div_pos (r07_radius_pos side x) he).ne')).div hr
        (fun x => (r07_radius_pos side x).ne')
  have hc := continuousOn_parametric_iteratedDeriv_weight_comp hw hjets hg hr hmap n
  refine hc.congr ?_
  intro z _
  have heq : r07PhysicalDensity (D z.1) side j =
      fun x => weight x * (D z.1).w (Statements.tailPhysicalRadius side x) := by
    funext x
    unfold r07PhysicalDensity
    rw [hfixed z.1]
    dsimp only [weight]
    ring
  change iteratedDeriv n (r07PhysicalDensity (D z.1) side j) z.2 =
    iteratedDeriv n (fun x => weight x * (D z.1).w (Statements.tailPhysicalRadius side x)) z.2
  rw [heq]

theorem r07_radialJet_eq_iteratedDeriv (n : ℕ) (f : ℝ → ℝ) :
    Statements.radialJet n f = iteratedDeriv n f := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [Statements.radialJet, ih, iteratedDeriv_succ]

/-- The preceding density-jet continuity in the exact `radialJet` notation
of the fixed `DeepTailParameterContinuity` statement. -/
theorem continuousOn_r07PhysicalDensity_radialJet {X : Type*} [TopologicalSpace X]
    {D : X → Statements.ReferenceData} {s t : Set ℝ} (side : Bool) (j : ℕ)
    {endpoint : ℝ} (he : 0 < endpoint)
    (hfixed : ∀ p, (if side then (D p).b else (D p).a) = endpoint)
    (hw : ∀ p, ContDiff ℝ ∞ (D p).w)
    (hjets : ∀ k, ContinuousOn (fun z : X × ℝ => iteratedDeriv k (D z.1).w z.2)
      {z | z.2 ∈ t})
    (hmap : MapsTo (Statements.tailPhysicalRadius side) s t) (n : ℕ) :
    ContinuousOn (fun z : X × ℝ => Statements.radialJet n (r07PhysicalDensity (D z.1) side j) z.2)
      {z | z.2 ∈ s} := by
  simp only [r07_radialJet_eq_iteratedDeriv]
  exact continuousOn_r07PhysicalDensity_iteratedDeriv side j he hfixed hw hjets hmap n

end ContinuousFlexibility.Radial
