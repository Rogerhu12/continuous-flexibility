import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Topology.Order.Compact

/-!
# Classical comparison in a positive buffer

These lemmas concern the scalar equation `u'' = q * u` on an increasing
coordinate interval.  Composing with the inward coordinate at either cut
uses the same statements at both ends of a buffer.  No solution-existence
or weak-domain assertion is assumed implicitly.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open Set Filter Real
open scoped Topology

/-- A twice differentiable scalar function with nonpositive boundary
values cannot be positive if its second derivative is positive wherever
the function is positive.  The proof uses strict convexity near a positive
maximum, so no regularity of the second derivative is needed. -/
theorem positiveBuffer_maximum_principle {a b : ℝ} {u du ddu : ℝ → ℝ}
    (hc : ContinuousOn u (Icc a b))
    (hu : ∀ x ∈ Ioo a b, HasDerivAt u (du x) x)
    (hdu : ∀ x ∈ Ioo a b, HasDerivAt du (ddu x) x)
    (hpositive : ∀ x ∈ Ioo a b, 0 < u x → 0 < ddu x)
    (ha : u a ≤ 0) (hb : u b ≤ 0) :
    ∀ x ∈ Icc a b, u x ≤ 0 := by
  intro x hx
  by_contra hn
  have hxpos : 0 < u x := lt_of_not_ge hn
  obtain ⟨c, hcI, hmax⟩ := isCompact_Icc.exists_isMaxOn ⟨x, hx⟩ hc
  have hcpos : 0 < u c := hxpos.trans_le (hmax hx)
  have hca : a < c := lt_of_le_of_ne hcI.1 (by
    intro heq
    have : u c ≤ 0 := heq ▸ ha
    linarith)
  have hcb : c < b := lt_of_le_of_ne hcI.2 (by
    intro heq
    have : u c ≤ 0 := heq.symm ▸ hb
    linarith)
  have hcopen : c ∈ Ioo a b := ⟨hca, hcb⟩
  have hnear : ∀ᶠ y in 𝓝 c, y ∈ Ioo a b ∧ 0 < u y := by
    filter_upwards [Ioo_mem_nhds hca hcb,
      (hu c hcopen).continuousAt.preimage_mem_nhds (Ioi_mem_nhds hcpos)] with y hy hyu
    exact ⟨hy, hyu⟩
  obtain ⟨l, r, hclr, hsub⟩ := hnear.exists_Ioo_subset
  have hconv : StrictConvexOn ℝ (Ioo l r) u := by
    apply strictConvexOn_of_deriv2_pos (convex_Ioo l r)
    · exact fun y hy => (hu y (hsub hy).1).continuousAt.continuousWithinAt
    · intro y hy
      rw [interior_Ioo] at hy
      have hyeq : deriv u =ᶠ[𝓝 y] du := by
        filter_upwards [Ioo_mem_nhds (hsub hy).1.1 (hsub hy).1.2] with z hz
        exact (hu z hz).deriv
      have heq : (deriv^[2] u) y = ddu y := by
        change deriv (deriv u) y = ddu y
        rw [hyeq.deriv_eq, (hdu y (hsub hy).1).deriv]
      rw [heq]
      exact hpositive y (hsub hy).1 (hsub hy).2
  let c₁ : ℝ := (l + c) / 2
  let c₂ : ℝ := (c + r) / 2
  have hc₁ : c₁ ∈ Ioo l r := by dsimp [c₁]; constructor <;> linarith [hclr.1, hclr.2]
  have hc₂ : c₂ ∈ Ioo l r := by dsimp [c₂]; constructor <;> linarith [hclr.1, hclr.2]
  have hmid : c ∈ Ioo c₁ c₂ := by dsimp [c₁, c₂]; constructor <;> linarith [hclr.1, hclr.2]
  have hne : c₁ ≠ c₂ := ne_of_lt (hmid.1.trans hmid.2)
  have hlt := hconv.lt_on_openSegment hc₁ hc₂ hne (Ioo_subset_openSegment hmid)
  have hle : max (u c₁) (u c₂) ≤ u c :=
    max_le (hmax (Ioo_subset_Icc_self (hsub hc₁).1))
      (hmax (Ioo_subset_Icc_self (hsub hc₂).1))
  exact (not_lt_of_ge hle) hlt

/-- Positivity of a solution of `-u'' + q u = 0` with nonnegative
endpoint values, for a strictly positive potential. -/
theorem positiveBuffer_solution_nonneg {a b : ℝ} {u du q : ℝ → ℝ}
    (hc : ContinuousOn u (Icc a b))
    (hu : ∀ x ∈ Ioo a b, HasDerivAt u (du x) x)
    (hdu : ∀ x ∈ Ioo a b, HasDerivAt du (q x * u x) x)
    (hq : ∀ x ∈ Ioo a b, 0 < q x)
    (ha : 0 ≤ u a) (hb : 0 ≤ u b) :
    ∀ x ∈ Icc a b, 0 ≤ u x := by
  have h := positiveBuffer_maximum_principle (u := fun x => -u x)
    (du := fun x => -du x) (ddu := fun x => -(q x * u x)) hc.neg
    (fun x hx => (hu x hx).neg) (fun x hx => (hdu x hx).neg)
    (fun x hx hxpos => by
      have hux : u x < 0 := by linarith
      exact neg_pos.mpr (mul_neg_of_pos_of_neg (hq x hx) hux))
    (by linarith) (by linarith)
  intro x hx
  have := h x hx
  linarith

/-- Comparison with a nonnegative classical supersolution.  This form
is convenient for exponential barriers, and does not assume positivity
of the solution being compared. -/
theorem positiveBuffer_solution_le_supersolution {a b : ℝ}
    {u du q v dv ddv : ℝ → ℝ}
    (huc : ContinuousOn u (Icc a b)) (hvc : ContinuousOn v (Icc a b))
    (hu : ∀ x ∈ Ioo a b, HasDerivAt u (du x) x)
    (hdu : ∀ x ∈ Ioo a b, HasDerivAt du (q x * u x) x)
    (hv : ∀ x ∈ Ioo a b, HasDerivAt v (dv x) x)
    (hdv : ∀ x ∈ Ioo a b, HasDerivAt dv (ddv x) x)
    (hq : ∀ x ∈ Ioo a b, 0 < q x)
    (hsuper : ∀ x ∈ Ioo a b, ddv x ≤ q x * v x)
    (ha : u a ≤ v a) (hb : u b ≤ v b) :
    ∀ x ∈ Icc a b, u x ≤ v x := by
  have h := positiveBuffer_maximum_principle
    (u := fun x => u x - v x) (du := fun x => du x - dv x)
    (ddu := fun x => q x * u x - ddv x) (huc.sub hvc)
    (fun x hx => (hu x hx).sub (hv x hx))
    (fun x hx => (hdu x hx).sub (hdv x hx))
    (fun x hx hxpos => by
      have hmul : 0 < q x * (u x - v x) := mul_pos (hq x hx) hxpos
      nlinarith [hsuper x hx])
    (by linarith) (by linarith)
  intro x hx
  have := h x hx
  linarith

/-- The inward exponential barrier and its two derivatives. -/
theorem positiveBuffer_hasDerivAt_exponential (A m a x : ℝ) :
    HasDerivAt (fun y : ℝ => A * exp (-m * (y - a)))
      (-m * (A * exp (-m * (x - a)))) x := by
  have hd := (((hasDerivAt_id x).sub_const a).const_mul (-m)).exp.const_mul A
  convert hd using 1 <;> simp only [id_eq, mul_one] <;> ring

theorem positiveBuffer_hasDerivAt_exponential_deriv (A m a x : ℝ) :
    HasDerivAt (fun y : ℝ => -m * (A * exp (-m * (y - a))))
      (m ^ 2 * (A * exp (-m * (x - a)))) x := by
  have hd := (positiveBuffer_hasDerivAt_exponential A m a x).const_mul (-m)
  convert hd using 1 <;> ring

/-- A Dirichlet wall at the inner end of a positive buffer gives the
sharp one-sided exponential upper bound from the cut. -/
theorem positiveBuffer_dirichlet_exponential_bound {a b A m : ℝ}
    {u du q : ℝ → ℝ} (hm : 0 < m) (hA : 0 ≤ A)
    (hc : ContinuousOn u (Icc a b))
    (hu : ∀ x ∈ Ioo a b, HasDerivAt u (du x) x)
    (hdu : ∀ x ∈ Ioo a b, HasDerivAt du (q x * u x) x)
    (hq : ∀ x ∈ Ioo a b, m ^ 2 ≤ q x)
    (ha : u a ≤ A) (hb : u b ≤ 0) :
    ∀ x ∈ Icc a b, u x ≤ A * exp (-m * (x - a)) := by
  apply positiveBuffer_solution_le_supersolution hc
    (show ContinuousOn (fun x => A * exp (-m * (x - a))) (Icc a b) from
      fun x _ => (positiveBuffer_hasDerivAt_exponential A m a x).continuousAt.continuousWithinAt)
    hu hdu
    (fun x _ => positiveBuffer_hasDerivAt_exponential A m a x)
    (fun x _ => positiveBuffer_hasDerivAt_exponential_deriv A m a x)
  · intro x hx
    exact lt_of_lt_of_le (sq_pos_of_pos hm) (hq x hx)
  · intro x hx
    exact mul_le_mul_of_nonneg_right (hq x hx) (mul_nonneg hA (exp_pos _).le)
  · simpa using ha
  · exact hb.trans (mul_nonneg hA (exp_pos _).le)

end ContinuousFlexibility.Radial
