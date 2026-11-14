module

public import ContinuousFlexibility.Analysis.WeightedJointComposition
public import ContinuousFlexibility.Analysis.ScalarRpowJetGrowth

/-!
# Positive powers of actual weighted joint towers

A quantitative positive lower bound on each component controls every
outer power derivative. The genuine finite-partition composition then
keeps one high parameter factor and a fixed joint derivative loss.
Square root and reciprocal are special cases on the very same tower.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set ContinuousFlexibility.Statements
open scoped ContDiff BigOperators

variable {I E P : Type*}
  [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
  [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]
  [NormedAddCommGroup P] [NormedSpace ℝ P]
  {p : ℕ → Seminorm ℝ E} {W : I → ℝ}
  {U : Set E} {V : I → Set P} {f : I → E × P → ℝ}
  {J : ∀ i, SmoothDirections (U ×ˢ V i) (f i)} {base loss : ℕ}

theorem UniformWeightedJointGrowth.rpow
    (hJ : UniformWeightedJointGrowth p W J base loss)
    (hp : Monotone p) (hIp : HasInterpolation p) (hW : ∀ i, 1 ≤ W i)
    {lam P₀ : ℝ} (hlam : 0 < lam) (hP₀ : 0 ≤ P₀)
    (hlower : ∀ i x, x ∈ U → ∀ y ∈ V i, lam * W i ^ (-P₀) ≤ f i (x, y))
    (r : ℝ) (K : ∀ i, SmoothDirections (U ×ˢ V i) (fun z => (f i z) ^ r)) :
    ∃ B L : ℕ, base ≤ B ∧ loss ≤ B ∧ UniformWeightedJointGrowth p W K B L := by
  have hpos (i : I) (x : E) (hx : x ∈ U) (y : P) (hy : y ∈ V i) :
      0 < f i (x, y) :=
    (mul_pos hlam (Real.rpow_pos_of_pos (zero_lt_one.trans_le (hW i)) _)).trans_le
      (hlower i x hx y hy)
  have hg : ContDiffOn ℝ ∞ (fun a : ℝ => a ^ r) (Ioi (0 : ℝ)) :=
    fun a ha => (Real.contDiffAt_rpow_const_of_ne (ne_of_gt ha)).contDiffWithinAt
  have hmap (i : I) : MapsTo (f i) (U ×ˢ V i) (Ioi (0 : ℝ)) :=
    fun z hz => hpos i z.1 hz.1 z.2 hz.2
  have houter : ∀ R : ℝ, 0 ≤ R → ∀ k : ℕ, ∃ C Q : ℝ, 0 ≤ C ∧ 0 ≤ Q ∧
      ∀ i x, x ∈ U → p (max base loss) x ≤ R → ∀ y ∈ V i,
        ‖contDiffOnJetFamily (fun a : ℝ => a ^ r) (Ioi (0 : ℝ)) k (f i (x, y))‖ ≤
          C * W i ^ Q := by
    intro R hR k
    obtain ⟨A, Q₀, hA, hQ₀, hzero⟩ := hJ R hR 0
    have hAR : 0 ≤ A * (1 + R) := mul_nonneg hA (add_nonneg zero_le_one hR)
    obtain ⟨C, Q, hC, hQ, hb⟩ :=
      iteratedDeriv_rpow_polynomial_bound hlam hAR hP₀ hQ₀ r k
    refine ⟨C, Q, hC, hQ, fun i x hx hlow y hy => ?_⟩
    have hvalue : |f i (x, y)| ≤ A * W i ^ Q₀ * (1 + p loss x) := by
      have h := hzero i x hx ((hp (le_max_left _ _) x).trans hlow) y hy
        Fin.elim0 (fun j => Fin.elim0 j)
      simpa only [(J i).zero (x, y) ⟨hx, hy⟩, Nat.zero_add,
        Finset.univ_eq_empty, Finset.sum_empty, add_zero, Real.norm_eq_abs] using h
    have hupper : f i (x, y) ≤ (A * (1 + R)) * W i ^ Q₀ := by
      have hpl : p loss x ≤ R := (hp (le_max_right _ _) x).trans hlow
      exact ((le_abs_self _).trans hvalue).trans
        ((mul_le_mul_of_nonneg_left (add_le_add le_rfl hpl)
          (mul_nonneg hA (Real.rpow_nonneg (zero_le_one.trans (hW i)) _))).trans_eq (by ring))
    change ‖iteratedFDerivWithin ℝ k (fun a : ℝ => a ^ r) (Ioi (0 : ℝ)) (f i (x, y))‖ ≤ _
    rw [iteratedFDerivWithin_of_isOpen k isOpen_Ioi (hpos i x hx y hy),
      norm_iteratedFDeriv_eq_norm_iteratedDeriv, Real.norm_eq_abs]
    exact hb (W i) (f i (x, y)) (hW i) (hlower i x hx y hy) hupper
  obtain ⟨B, L, hb, ho, hcomp⟩ := hJ.comp_contDiff hp hIp hW isOpen_Ioi hg hmap
    (max base loss) houter
  exact ⟨B, L, hb, (le_max_right _ _).trans ho,
    hcomp.congr K (fun _ _ _ => rfl)⟩

theorem UniformWeightedJointGrowth.sqrt
    (hJ : UniformWeightedJointGrowth p W J base loss)
    (hp : Monotone p) (hIp : HasInterpolation p) (hW : ∀ i, 1 ≤ W i)
    {lam P₀ : ℝ} (hlam : 0 < lam) (hP₀ : 0 ≤ P₀)
    (hlower : ∀ i x, x ∈ U → ∀ y ∈ V i, lam * W i ^ (-P₀) ≤ f i (x, y))
    (K : ∀ i, SmoothDirections (U ×ˢ V i) (fun z => Real.sqrt (f i z))) :
    ∃ B L : ℕ, base ≤ B ∧ loss ≤ B ∧ UniformWeightedJointGrowth p W K B L := by
  let K' := fun i => (K i).congrOn (fun z _ => Real.sqrt_eq_rpow (f i z))
  obtain ⟨B, L, hb, hl, h⟩ := hJ.rpow hp hIp hW hlam hP₀ hlower (1 / 2 : ℝ) K'
  exact ⟨B, L, hb, hl, h⟩

theorem UniformWeightedJointGrowth.inv
    (hJ : UniformWeightedJointGrowth p W J base loss)
    (hp : Monotone p) (hIp : HasInterpolation p) (hW : ∀ i, 1 ≤ W i)
    {lam P₀ : ℝ} (hlam : 0 < lam) (hP₀ : 0 ≤ P₀)
    (hlower : ∀ i x, x ∈ U → ∀ y ∈ V i, lam * W i ^ (-P₀) ≤ f i (x, y))
    (K : ∀ i, SmoothDirections (U ×ˢ V i) (fun z => (f i z)⁻¹)) :
    ∃ B L : ℕ, base ≤ B ∧ loss ≤ B ∧ UniformWeightedJointGrowth p W K B L := by
  let K' := fun i => (K i).congrOn (fun z _ => (Real.rpow_neg_one (f i z)).symm)
  obtain ⟨B, L, hb, hl, h⟩ := hJ.rpow hp hIp hW hlam hP₀ hlower (-1 : ℝ) K'
  exact ⟨B, L, hb, hl, h⟩

end ContinuousFlexibility.Analysis
