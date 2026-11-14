module

public import ContinuousFlexibility.Scalar.WeightedMaterialRadiusJets
public import ContinuousFlexibility.Scalar.WeightedNormalizedMaterialJets
public import Mathlib.Analysis.Calculus.IteratedDeriv.FaaDiBruno

/-!
# Finite formulas for the actual material-coordinate jets

At weight zero each material-coordinate mixed jet is a finite linear
combination of ordinary physical jets. Its coefficients depend only on
the fixed radius map. They are smooth and globally bounded, before any
state or parameter variation is chosen.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set
open scoped ContDiff BigOperators
open ContinuousFlexibility.Statements

/-- The coefficient associated with one partition in the ordinary
one-dimensional chain rule for the actual radius. -/
def n07aRadiusJetCoefficient (T : MaterialData) {a : ℕ}
    (c : OrderedFinpartition a) (x : ℝ) : ℝ :=
  ∏ j, iteratedDeriv (c.partSize j) T.radius x

theorem n07aRadiusJetCoefficient_contDiff
    {D : ReferenceData} {T : MaterialData} (hT : IsMaterialData D T)
    {a : ℕ} (c : OrderedFinpartition a) :
    ContDiff ℝ ∞ (n07aRadiusJetCoefficient T c) := by
  have hradius : ContDiff ℝ ∞ T.radius := hT.2.2.2.2.2.2.1
  unfold n07aRadiusJetCoefficient
  apply contDiff_prod
  intro j _
  rw [iteratedDeriv_eq_iterate]
  exact hradius.iterate_deriv (c.partSize j)

/-- Each fixed chain-rule coefficient has one bound on the whole material
axis, independent of every nonlinear state and every direction. -/
theorem n07aRadiusJetCoefficient_bounded
    {D : ReferenceData} {T : MaterialData} (hT : IsMaterialData D T)
    {a : ℕ} (c : OrderedFinpartition a) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ x : ℝ, |n07aRadiusJetCoefficient T c x| ≤ K := by
  choose B hB hBb using fun j : Fin c.length =>
    iteratedDeriv_materialRadius_bounded hT (c.partSize j)
  refine ⟨∏ j, B j, Finset.prod_nonneg (fun j _ => hB j), fun x => ?_⟩
  simp only [n07aRadiusJetCoefficient, Finset.abs_prod]
  exact Finset.prod_le_prod₀ (fun _ _ => abs_nonneg _) (fun j _ => hBb j x)

/-- The physical orders used in the finite expansion never exceed the
original radial order. No inversion of a derivative expansion is needed. -/
theorem n07a_materialPullback_zero_mixedDerivative
    {D : ReferenceData} {T : MaterialData} (hT : IsMaterialData D T)
    {f : PolarPoint → ℝ} (hf : ContDiffOn ℝ ∞ f (annularOpen D))
    (a b : ℕ) (p : PolarPoint) :
    mixedDerivative a b (materialPullback T 0 f) p =
      ∑ c : OrderedFinpartition a,
        mixedDerivative c.length b f (T.radius p.1, p.2) *
          n07aRadiusJetCoefficient T c p.1 := by
  have hradius : ContDiff ℝ ∞ T.radius := hT.2.2.2.2.2.2.1
  have hr : T.radius p.1 ∈ Ioo D.a D.b := (hT.2.2.2.2.2.2.2.1 p.1).1
  let g : ℝ → ℝ := fun r => iteratedDeriv b (fun θ => f (r, θ)) p.2
  have hg : ContDiffOn ℝ ∞ g (Ioo D.a D.b) := by
    have hs : ContDiff ℝ ∞ (fun r : ℝ => (r, p.2)) :=
      contDiff_id.prodMk contDiff_const
    have hm : MapsTo (fun r : ℝ => (r, p.2)) (Ioo D.a D.b) (annularOpen D) :=
      fun _ ht => ⟨ht, mem_univ _⟩
    simpa only [g, Function.comp_def, mixedDerivative, iteratedDeriv_zero, id_eq] using
      (contDiffOn_mixedDerivative (isOpen_Ioo.prod isOpen_univ) hf 0 b).comp
        hs.contDiffOn hm
  have h := iteratedDeriv_comp_eq_sum_orderedFinpartition
    (hg.contDiffAt (isOpen_Ioo.mem_nhds hr)) hradius.contDiffAt
    (show (a : ℕ∞ω) ≤ ∞ by simp)
  simpa only [materialPullback, neg_zero, Real.rpow_zero, one_mul, mixedDerivative,
    Function.comp_def, g, n07aRadiusJetCoefficient] using h

/-- A common bound for the finite list of ordinary jets gives a common
bound for the material jet with no increase in its differential order. -/
theorem n07a_materialPullback_zero_mixedDerivative_bound
    {D : ReferenceData} {T : MaterialData} (hT : IsMaterialData D T) (a : ℕ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (f : PolarPoint → ℝ),
      ContDiffOn ℝ ∞ f (annularOpen D) → ∀ (b : ℕ) (p : PolarPoint) (W : ℝ),
      0 ≤ W →
      (∀ j : ℕ, j ≤ a → |mixedDerivative j b f (T.radius p.1, p.2)| ≤ W) →
      |mixedDerivative a b (materialPullback T 0 f) p| ≤ K * W := by
  choose B hB hBb using fun c : OrderedFinpartition a =>
    n07aRadiusJetCoefficient_bounded hT c
  refine ⟨∑ c, B c, Finset.sum_nonneg (fun c _ => hB c), ?_⟩
  intro f hf b p W hW hfBound
  rw [n07a_materialPullback_zero_mixedDerivative hT hf, Finset.sum_mul]
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  apply Finset.sum_le_sum
  intro c _
  rw [abs_mul]
  exact (mul_le_mul (hfBound c.length c.length_le) (hBb c p.1)
    (abs_nonneg _) hW).trans_eq (mul_comm W (B c))

end ContinuousFlexibility.Analysis
