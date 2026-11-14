module

public import Mathlib.Analysis.Convex.Deriv
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
public import Mathlib.Topology.Order.Compact

/-!
# Classical comparison in a positive buffer

These lemmas concern the scalar equation `u'' = q * u` on an increasing
coordinate interval.  Composing with the inward coordinate at either cut
uses the same statements at both ends of a buffer.  No solution-existence
or weak-domain assertion is assumed implicitly.
-/

@[expose] public section

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

/-- Comparison with a classical supersolution.  This form
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

/-- A nonnegative solution in a nonnegative potential is convex. -/
theorem positiveBuffer_solution_convex {a b : ℝ} {u du q : ℝ → ℝ}
    (hc : ContinuousOn u (Icc a b))
    (hu : ∀ x ∈ Ioo a b, HasDerivAt u (du x) x)
    (hdu : ∀ x ∈ Ioo a b, HasDerivAt du (q x * u x) x)
    (hq : ∀ x ∈ Ioo a b, 0 ≤ q x)
    (hnn : ∀ x ∈ Ioo a b, 0 ≤ u x) : ConvexOn ℝ (Icc a b) u := by
  apply convexOn_of_hasDerivWithinAt2_nonneg (convex_Icc a b) hc
  · intro x hx
    rw [interior_Icc] at hx
    exact (hu x hx).hasDerivWithinAt
  · intro x hx
    rw [interior_Icc] at hx
    exact (hdu x hx).hasDerivWithinAt
  · intro x hx
    rw [interior_Icc] at hx
    exact mul_nonneg (hq x hx) (hnn x hx)

/-- At a right Dirichlet wall a nonnegative function has nonpositive
outward ordinary derivative.  The trace is taken from the retained
interval, although the derivative itself is an ordinary derivative. -/
theorem positiveBuffer_wall_derivative_nonpos {a b d : ℝ} {u : ℝ → ℝ}
    (hab : a < b) (hd : HasDerivAt u d b)
    (hnn : ∀ x ∈ Icc a b, 0 ≤ u x) (hb : u b = 0) : d ≤ 0 := by
  apply le_of_tendsto (hasDerivAt_iff_tendsto_slope_left_right.mp hd).1
  have hnear : ∀ᶠ x in 𝓝[<] b, a < x :=
    (eventually_gt_nhds hab).filter_mono nhdsWithin_le_nhds
  filter_upwards [hnear, self_mem_nhdsWithin] with x hax (hxb : x < b)
  rw [slope_def_field, hb, sub_zero]
  exact div_nonpos_of_nonneg_of_nonpos (hnn x ⟨hax.le, hxb.le⟩) (sub_nonpos.mpr hxb.le)

/-- A nonnegative convex function vanishing at the right wall is
nonincreasing, including its ordinary derivative at that wall. -/
theorem positiveBuffer_convex_derivative_nonpos {a b s d : ℝ} {u : ℝ → ℝ}
    (hab : a < b) (hconv : ConvexOn ℝ (Icc a b) u)
    (hnn : ∀ x ∈ Icc a b, 0 ≤ u x) (hb : u b = 0)
    (hs : s ∈ Icc a b) (hd : HasDerivAt u d s) : d ≤ 0 := by
  by_cases hsb : s = b
  · subst s
    exact positiveBuffer_wall_derivative_nonpos hab hd hnn hb
  · have hsb' : s < b := lt_of_le_of_ne hs.2 hsb
    have hle := hconv.le_slope_of_hasDerivAt hs ⟨hab.le, le_rfl⟩ hsb' hd
    rw [slope_def_field, hb, zero_sub] at hle
    exact hle.trans (div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (hnn s hs))
      (sub_pos.mpr hsb').le)

/-- Interior derivative attenuation one layer after a sampling point.
It uses only the lower potential bound, not an upper bound in the layer.
The inner wall is allowed as the evaluation point. -/
theorem positiveBuffer_derivative_exponential_bound {a b x s A m d : ℝ}
    {u du q : ℝ → ℝ} (hm : 0 < m) (hA : 0 ≤ A)
    (hx : a ≤ x) (hxs : x < s) (hsb : s ≤ b)
    (hc : ContinuousOn u (Icc a b))
    (hu : ∀ y ∈ Ioo a b, HasDerivAt u (du y) y)
    (hdu : ∀ y ∈ Ioo a b, HasDerivAt du (q y * u y) y)
    (hq : ∀ y ∈ Ioo a b, m ^ 2 ≤ q y)
    (ha : 0 ≤ u a) (haA : u a ≤ A) (hb : u b = 0)
    (hds : HasDerivAt u d s) :
    |d| ≤ A * exp (-m * (x - a)) / (s - x) := by
  have hqpos : ∀ y ∈ Ioo a b, 0 < q y :=
    fun y hy => lt_of_lt_of_le (sq_pos_of_pos hm) (hq y hy)
  have hnn := positiveBuffer_solution_nonneg hc hu hdu hqpos ha (by rw [hb])
  have hconv := positiveBuffer_solution_convex hc hu hdu
    (fun y hy => (hqpos y hy).le) (fun y hy => hnn y (Ioo_subset_Icc_self hy))
  have hab : a < b := (hx.trans_lt hxs).trans_le hsb
  have hsI : s ∈ Icc a b := ⟨hx.trans hxs.le, hsb⟩
  have hxI : x ∈ Icc a b := ⟨hx, hxs.le.trans hsb⟩
  have hdnonpos := positiveBuffer_convex_derivative_nonpos hab hconv hnn hb hsI hds
  have hlow := hconv.slope_le_of_hasDerivAt hxI hsI hxs hds
  rw [slope_def_field] at hlow
  have hlow' : -(u x / (s - x)) ≤ d := by
    calc
      -(u x / (s - x)) = (0 - u x) / (s - x) := by ring
      _ ≤ (u s - u x) / (s - x) :=
        div_le_div_of_nonneg_right (sub_le_sub_right (hnn s hsI) _) (sub_pos.mpr hxs).le
      _ ≤ d := hlow
  have hexp := positiveBuffer_dirichlet_exponential_bound hm hA hc hu hdu hq haA
    (le_of_eq hb) x hxI
  rw [abs_of_nonpos hdnonpos]
  calc
    -d ≤ u x / (s - x) := by linarith
    _ ≤ A * exp (-m * (x - a)) / (s - x) :=
      div_le_div_of_nonneg_right hexp (sub_pos.mpr hxs).le

/-- The derivative at the inner Dirichlet wall has the same exponential
attenuation as the function one layer before the wall.  The sampling
point `x` is arbitrary, so a layer of width `1 / m` can be used later. -/
theorem positiveBuffer_wall_derivative_bound {a b x A m d : ℝ}
    {u du q : ℝ → ℝ} (hm : 0 < m) (hA : 0 ≤ A)
    (hx : a ≤ x) (hxb : x < b)
    (hc : ContinuousOn u (Icc a b))
    (hu : ∀ y ∈ Ioo a b, HasDerivAt u (du y) y)
    (hdu : ∀ y ∈ Ioo a b, HasDerivAt du (q y * u y) y)
    (hq : ∀ y ∈ Ioo a b, m ^ 2 ≤ q y)
    (ha : 0 ≤ u a) (haA : u a ≤ A) (hb : u b = 0)
    (hdb : HasDerivAt u d b) :
    |d| ≤ A * exp (-m * (x - a)) / (b - x) := by
  have hqpos : ∀ y ∈ Ioo a b, 0 < q y :=
    fun y hy => lt_of_lt_of_le (sq_pos_of_pos hm) (hq y hy)
  have hnn := positiveBuffer_solution_nonneg hc hu hdu hqpos ha (by rw [hb])
  have hconv := positiveBuffer_solution_convex hc hu hdu
    (fun y hy => (hqpos y hy).le) (fun y hy => hnn y (Ioo_subset_Icc_self hy))
  have hab : a < b := hx.trans_lt hxb
  have hdnonpos := positiveBuffer_wall_derivative_nonpos hab hdb hnn hb
  have hlow := hconv.slope_le_of_hasDerivAt ⟨hx, hxb.le⟩ ⟨hab.le, le_rfl⟩ hxb hdb
  rw [slope_def_field, hb, zero_sub, neg_div] at hlow
  have hexp := positiveBuffer_dirichlet_exponential_bound hm hA hc hu hdu hq haA
    (le_of_eq hb) x ⟨hx, hxb.le⟩
  rw [abs_of_nonpos hdnonpos]
  calc
    -d ≤ u x / (b - x) := by linarith
    _ ≤ A * exp (-m * (x - a)) / (b - x) :=
      div_le_div_of_nonneg_right hexp (sub_pos.mpr hxb).le

/-- Exponential barriers from both boundary components.  This estimate
does not require a sign condition on the solution. -/
theorem positiveBuffer_two_boundary_exponential_bound {a b A B m : ℝ}
    {u du q : ℝ → ℝ} (hm : 0 < m) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hc : ContinuousOn u (Icc a b))
    (hu : ∀ x ∈ Ioo a b, HasDerivAt u (du x) x)
    (hdu : ∀ x ∈ Ioo a b, HasDerivAt du (q x * u x) x)
    (hq : ∀ x ∈ Ioo a b, m ^ 2 ≤ q x)
    (ha : u a ≤ A) (hb : u b ≤ B) :
    ∀ x ∈ Icc a b,
      u x ≤ A * exp (-m * (x - a)) + B * exp (m * (x - b)) := by
  let v : ℝ → ℝ := fun x => A * exp (-m * (x - a)) + B * exp (m * (x - b))
  let dv : ℝ → ℝ := fun x => -m * (A * exp (-m * (x - a))) +
    m * (B * exp (m * (x - b)))
  have hv (x : ℝ) : HasDerivAt v (dv x) x := by
    simpa only [v, dv, neg_neg] using
      (positiveBuffer_hasDerivAt_exponential A m a x).fun_add
        (positiveBuffer_hasDerivAt_exponential B (-m) b x)
  have hdv (x : ℝ) : HasDerivAt dv (m ^ 2 * v x) x := by
    have hd := (positiveBuffer_hasDerivAt_exponential_deriv A m a x).fun_add
      (positiveBuffer_hasDerivAt_exponential_deriv B (-m) b x)
    simp only [neg_neg, neg_sq] at hd
    convert hd using 1 <;> dsimp [v, dv] <;> ring
  apply positiveBuffer_solution_le_supersolution hc
    (fun x _ => (hv x).continuousAt.continuousWithinAt) hu hdu
    (fun x _ => hv x) (fun x _ => hdv x)
  · intro x hx
    exact lt_of_lt_of_le (sq_pos_of_pos hm) (hq x hx)
  · intro x hx
    exact mul_le_mul_of_nonneg_right (hq x hx)
      (add_nonneg (mul_nonneg hA (exp_pos _).le) (mul_nonneg hB (exp_pos _).le))
  · dsimp [v]
    simpa using ha.trans (le_add_of_nonneg_right (mul_nonneg hB (exp_pos (m * (a - b))).le))
  · dsimp [v]
    simpa using hb.trans (le_add_of_nonneg_left (mul_nonneg hA (exp_pos (-m * (b - a))).le))

/-- A bounded classical solution on a positive half-line has the
one-sided exponential upper bound.  Energy-space applications can
supply boundedness from their one-dimensional Sobolev estimate. -/
theorem positiveBuffer_halfline_exponential_bound {a A M m : ℝ}
    {u du q : ℝ → ℝ} (hm : 0 < m) (hA : 0 ≤ A) (hM : 0 ≤ M)
    (hc : ContinuousOn u (Ici a))
    (hu : ∀ x ∈ Ioi a, HasDerivAt u (du x) x)
    (hdu : ∀ x ∈ Ioi a, HasDerivAt du (q x * u x) x)
    (hq : ∀ x ∈ Ioi a, m ^ 2 ≤ q x)
    (ha : u a ≤ A) (hbound : ∀ x ∈ Ici a, u x ≤ M) :
    ∀ x ∈ Ici a, u x ≤ A * exp (-m * (x - a)) := by
  intro x hx
  have harg : Tendsto (fun b : ℝ => m * (x - b)) atTop atBot := by
    apply tendsto_atBot.mpr
    intro y
    filter_upwards [eventually_ge_atTop (x - y / m)] with b hb
    have hmul := mul_le_mul_of_nonneg_left hb hm.le
    have hcancel : y / m * m = y := div_mul_cancel₀ y hm.ne'
    nlinarith
  have hexp : Tendsto (fun b : ℝ => exp (m * (x - b))) atTop (𝓝 0) :=
    tendsto_exp_atBot.comp harg
  have hlim : Tendsto
      (fun b : ℝ => A * exp (-m * (x - a)) + M * exp (m * (x - b)))
      atTop (𝓝 (A * exp (-m * (x - a)))) := by
    simpa using
      (tendsto_const_nhds : Tendsto (fun _ : ℝ => A * exp (-m * (x - a)))
        atTop (𝓝 (A * exp (-m * (x - a))))).add (hexp.const_mul M)
  apply ge_of_tendsto hlim
  filter_upwards [eventually_gt_atTop x] with b hxb
  exact positiveBuffer_two_boundary_exponential_bound hm hA hM
    (hc.mono (fun _ hy => hy.1))
    (fun y hy => hu y hy.1) (fun y hy => hdu y hy.1)
    (fun y hy => hq y hy.1) ha (hbound b (hx.trans hxb.le)) x ⟨hx, hxb.le⟩

/-- Absolute exponential attenuation of a bounded half-line solution;
both signs of the solution are treated by the same comparison theorem. -/
theorem positiveBuffer_halfline_abs_exponential_bound {a M m : ℝ}
    {u du q : ℝ → ℝ} (hm : 0 < m) (hM : 0 ≤ M)
    (hc : ContinuousOn u (Ici a))
    (hu : ∀ x ∈ Ioi a, HasDerivAt u (du x) x)
    (hdu : ∀ x ∈ Ioi a, HasDerivAt du (q x * u x) x)
    (hq : ∀ x ∈ Ioi a, m ^ 2 ≤ q x)
    (hbound : ∀ x ∈ Ici a, |u x| ≤ M) :
    ∀ x ∈ Ici a, |u x| ≤ |u a| * exp (-m * (x - a)) := by
  have hup := positiveBuffer_halfline_exponential_bound hm (abs_nonneg (u a)) hM
    hc hu hdu hq (le_abs_self (u a))
    (fun x hx => (le_abs_self (u x)).trans (hbound x hx))
  have hdown := positiveBuffer_halfline_exponential_bound
    (u := fun x => -u x) (du := fun x => -du x) (q := q)
    hm (abs_nonneg (u a)) hM hc.neg
    (fun x hx => (hu x hx).neg)
    (fun x hx => by simpa only [mul_neg] using (hdu x hx).fun_neg)
    hq (neg_le_abs (u a))
    (fun x hx => (neg_le_abs (u x)).trans (hbound x hx))
  intro x hx
  exact abs_le.mpr ⟨by linarith [hdown x hx], hup x hx⟩

/-- A bounded homogeneous half-line solution with nonnegative finite
boundary value is nonnegative everywhere. -/
theorem positiveBuffer_halfline_solution_nonneg {a M m : ℝ}
    {u du q : ℝ → ℝ} (hm : 0 < m) (hM : 0 ≤ M)
    (hc : ContinuousOn u (Ici a))
    (hu : ∀ x ∈ Ioi a, HasDerivAt u (du x) x)
    (hdu : ∀ x ∈ Ioi a, HasDerivAt du (q x * u x) x)
    (hq : ∀ x ∈ Ioi a, m ^ 2 ≤ q x)
    (ha : 0 ≤ u a) (hbound : ∀ x ∈ Ici a, |u x| ≤ M) :
    ∀ x ∈ Ici a, 0 ≤ u x := by
  have h := positiveBuffer_halfline_exponential_bound
    (u := fun x => -u x) (du := fun x => -du x) (q := q) (A := 0)
    hm le_rfl hM hc.neg (fun x hx => (hu x hx).neg)
    (fun x hx => by simpa only [mul_neg] using (hdu x hx).fun_neg)
    hq (neg_nonpos.mpr ha)
    (fun x hx => (neg_le_abs (u x)).trans (hbound x hx))
  intro x hx
  simpa using h x hx

/-- A function nonpositive to the right of a zero has nonpositive
right derivative, when its ordinary derivative exists. -/
theorem positiveBuffer_right_derivative_nonpos {a d : ℝ} {u : ℝ → ℝ}
    (hd : HasDerivAt u d a) (ha : u a = 0)
    (hnonpos : ∀ x ∈ Ioi a, u x ≤ 0) : d ≤ 0 := by
  apply le_of_tendsto (hasDerivAt_iff_tendsto_slope_left_right.mp hd).2
  filter_upwards [self_mem_nhdsWithin] with x (hx : a < x)
  rw [slope_def_field, ha, sub_zero]
  exact div_nonpos_of_nonpos_of_nonneg (hnonpos x hx) (sub_pos.mpr hx).le

/-- Differentiating the sharp exponential comparison at the cut gives
the lower bound for the exterior conormal coefficient. -/
theorem positiveBuffer_halfline_conormal_lower {a M m d : ℝ}
    {u du q : ℝ → ℝ} (hm : 0 < m) (hM : 0 ≤ M)
    (hc : ContinuousOn u (Ici a))
    (hu : ∀ x ∈ Ioi a, HasDerivAt u (du x) x)
    (hdu : ∀ x ∈ Ioi a, HasDerivAt du (q x * u x) x)
    (hq : ∀ x ∈ Ioi a, m ^ 2 ≤ q x)
    (ha : 0 ≤ u a) (hbound : ∀ x ∈ Ici a, u x ≤ M)
    (hda : HasDerivAt u d a) : m * u a ≤ -d := by
  have h := positiveBuffer_halfline_exponential_bound hm ha hM hc hu hdu hq
    le_rfl hbound
  have hd : HasDerivAt (fun x => u x - u a * exp (-m * (x - a)))
      (d + m * u a) a := by
    convert hda.sub (positiveBuffer_hasDerivAt_exponential (u a) m a a) using 1 <;> simp <;> ring
  have hnonpos := positiveBuffer_right_derivative_nonpos hd (by simp)
    (fun x hx => sub_nonpos.mpr (h x (Ioi_subset_Ici_self hx)))
  linarith

/-- A nonnegative homogeneous solution is convex on the whole positive
half-line.  Endpoint derivatives are not required for this assertion. -/
theorem positiveBuffer_halfline_solution_convex {a : ℝ} {u du q : ℝ → ℝ}
    (hc : ContinuousOn u (Ici a))
    (hu : ∀ x ∈ Ioi a, HasDerivAt u (du x) x)
    (hdu : ∀ x ∈ Ioi a, HasDerivAt du (q x * u x) x)
    (hq : ∀ x ∈ Ioi a, 0 ≤ q x)
    (hnn : ∀ x ∈ Ioi a, 0 ≤ u x) : ConvexOn ℝ (Ici a) u := by
  apply convexOn_of_hasDerivWithinAt2_nonneg (convex_Ici a) hc
  · intro x hx
    rw [interior_Ici] at hx
    exact (hu x hx).hasDerivWithinAt
  · intro x hx
    rw [interior_Ici] at hx
    exact (hdu x hx).hasDerivWithinAt
  · intro x hx
    rw [interior_Ici] at hx
    exact mul_nonneg (hq x hx) (hnn x hx)

/-- A convex function bounded above on a half-line has nonpositive
derivative.  A positive derivative would force linear growth along a
supporting secant. -/
theorem positiveBuffer_halfline_convex_derivative_nonpos {a s M d : ℝ} {u : ℝ → ℝ}
    (hconv : ConvexOn ℝ (Ici a) u) (hbound : ∀ x ∈ Ici a, u x ≤ M)
    (hs : s ∈ Ici a) (hd : HasDerivAt u d s) : d ≤ 0 := by
  by_contra hn
  have hdpos : 0 < d := lt_of_not_ge hn
  let t : ℝ := s + (M - u s + 1) / d
  have hnum : 0 < M - u s + 1 := by linarith [hbound s hs]
  have hst : s < t := by dsimp [t]; exact lt_add_of_pos_right _ (div_pos hnum hdpos)
  have ht : t ∈ Ici a := hs.trans hst.le
  have hle := hconv.le_slope_of_hasDerivAt hs ht hst hd
  rw [slope_def_field] at hle
  have hmul : d * (t - s) ≤ u t - u s := (le_div_iff₀ (sub_pos.mpr hst)).mp hle
  have hcancel : (M - u s + 1) / d * d = M - u s + 1 :=
    div_mul_cancel₀ _ hdpos.ne'
  dsimp [t] at hmul
  nlinarith [hbound t ht]

/-- The derivative of a nonnegative bounded homogeneous solution is
nonpositive and monotone increasing on the half-line.  In particular
its absolute value is bounded by its value at the finite endpoint. -/
theorem positiveBuffer_halfline_derivative_bounds {a M : ℝ} {u du q : ℝ → ℝ}
    (hc : ContinuousOn u (Ici a)) (hdc : ContinuousOn du (Ici a))
    (hu : ∀ x ∈ Ici a, HasDerivAt u (du x) x)
    (hdu : ∀ x ∈ Ioi a, HasDerivAt du (q x * u x) x)
    (hq : ∀ x ∈ Ioi a, 0 ≤ q x)
    (hnn : ∀ x ∈ Ici a, 0 ≤ u x)
    (hbound : ∀ x ∈ Ici a, u x ≤ M) :
    MonotoneOn du (Ici a) ∧ ∀ x ∈ Ici a, du x ≤ 0 ∧ |du x| ≤ |du a| := by
  have hconv := positiveBuffer_halfline_solution_convex hc
    (fun x hx => hu x (Ioi_subset_Ici_self hx)) hdu hq
    (fun x hx => hnn x (Ioi_subset_Ici_self hx))
  have hmono : MonotoneOn du (Ici a) := by
    apply monotoneOn_of_deriv_nonneg (convex_Ici a) hdc
    · intro x hx
      rw [interior_Ici] at hx
      exact (hdu x hx).differentiableAt.differentiableWithinAt
    · intro x hx
      rw [interior_Ici] at hx
      rw [(hdu x hx).deriv]
      exact mul_nonneg (hq x hx) (hnn x (Ioi_subset_Ici_self hx))
  have hnonpos : ∀ x ∈ Ici a, du x ≤ 0 := fun x hx =>
    positiveBuffer_halfline_convex_derivative_nonpos hconv hbound hx (hu x hx)
  refine ⟨hmono, fun x hx => ⟨hnonpos x hx, ?_⟩⟩
  have ha : a ∈ Ici a := by change a ≤ a; exact le_rfl
  rw [abs_of_nonpos (hnonpos x hx), abs_of_nonpos (hnonpos a ha)]
  exact neg_le_neg (hmono ha hx hx)

/-- The boundary energy flux of a nonnegative bounded homogeneous
solution tends to zero at the infinite end of a positive buffer. -/
theorem positiveBuffer_halfline_flux_tendsto_zero {a M m : ℝ}
    {u du q : ℝ → ℝ} (hm : 0 < m) (hM : 0 ≤ M)
    (hc : ContinuousOn u (Ici a)) (hdc : ContinuousOn du (Ici a))
    (hu : ∀ x ∈ Ici a, HasDerivAt u (du x) x)
    (hdu : ∀ x ∈ Ioi a, HasDerivAt du (q x * u x) x)
    (hq : ∀ x ∈ Ioi a, m ^ 2 ≤ q x)
    (hnn : ∀ x ∈ Ici a, 0 ≤ u x)
    (hbound : ∀ x ∈ Ici a, u x ≤ M) :
    Tendsto (fun x : ℝ => u x * du x) atTop (𝓝 0) := by
  have hd := positiveBuffer_halfline_derivative_bounds hc hdc hu hdu
    (fun x hx => (sq_nonneg m).trans (hq x hx)) hnn hbound
  have habs : ∀ x ∈ Ici a, |u x| ≤ M := fun x hx => by
    rw [abs_of_nonneg (hnn x hx)]
    exact hbound x hx
  have he := positiveBuffer_halfline_abs_exponential_bound hm hM hc
    (fun x hx => hu x (Ioi_subset_Ici_self hx)) hdu hq habs
  have harg : Tendsto (fun x : ℝ => -m * (x - a)) atTop atBot := by
    apply tendsto_atBot.mpr
    intro y
    filter_upwards [eventually_ge_atTop (a - y / m)] with x hx
    have hmul := mul_le_mul_of_nonneg_left hx hm.le
    have hcancel : y / m * m = y := div_mul_cancel₀ y hm.ne'
    nlinarith
  have he0 := tendsto_exp_atBot.comp harg
  have hmajorant : ∀ᶠ x in atTop,
      ‖u x * du x‖ ≤ |u a| * exp (-m * (x - a)) * |du a| := by
    filter_upwards [eventually_ge_atTop a] with x hx
    rw [Real.norm_eq_abs, abs_mul]
    exact mul_le_mul (he x hx) (hd.2 x hx).2 (abs_nonneg _)
      (mul_nonneg (abs_nonneg _) (exp_pos _).le)
  have hzero : Tendsto (fun x : ℝ => |u a| * exp (-m * (x - a)) * |du a|)
      atTop (𝓝 0) := by
    simpa using (he0.const_mul |u a|).mul_const |du a|
  exact squeeze_zero_norm' hmajorant hzero

/-- On the inner cutoff layer of a unit-mass buffer of length
`σ + 6`, both the normalized Dirichlet minimizer and its first
derivative are bounded by `exp (-σ)`.  This is the attenuation used
for the cutoff commutator; no upper potential bound is needed here. -/
theorem positiveBuffer_normalized_inner_decay {σ : ℝ} {u du q : ℝ → ℝ}
    (hσ : 0 < σ) (hc : ContinuousOn u (Icc 0 (σ + 6)))
    (hu : ∀ x ∈ Ioo 0 (σ + 6), HasDerivAt u (du x) x)
    (hdu : ∀ x ∈ Ioo 0 (σ + 6), HasDerivAt du (q x * u x) x)
    (hq : ∀ x ∈ Ioo 0 (σ + 6), 1 ≤ q x)
    (h0 : u 0 = 1) (hwall : u (σ + 6) = 0) :
    ∀ s ∈ Icc (σ + 2) (σ + 4),
      |u s| ≤ exp (-σ) ∧ |du s| ≤ exp (-σ) := by
  have hq1 : ∀ x ∈ Ioo 0 (σ + 6), (1 : ℝ) ^ 2 ≤ q x := by
    simpa only [one_pow] using hq
  have hnn := positiveBuffer_solution_nonneg hc hu hdu
    (fun x hx => lt_of_lt_of_le zero_lt_one (hq x hx))
    (by rw [h0]; norm_num) (by rw [hwall])
  intro s hs
  have hsI : s ∈ Ioo 0 (σ + 6) := by constructor <;> linarith [hs.1, hs.2]
  have hv := positiveBuffer_dirichlet_exponential_bound (m := 1) (A := 1)
    (by norm_num) (by norm_num) hc hu hdu hq1
    (le_of_eq h0) (le_of_eq hwall) s (Ioo_subset_Icc_self hsI)
  have hv' : u s ≤ exp (-s) := by simpa using hv
  have hd := positiveBuffer_derivative_exponential_bound
    (a := 0) (b := σ + 6) (x := s - 1) (s := s) (A := 1) (m := 1)
    (d := du s) (by norm_num) (by norm_num)
    (by linarith [hs.1]) (by linarith) hsI.2.le hc hu hdu hq1
    (by rw [h0]; norm_num) (le_of_eq h0) hwall (hu s hsI)
  have hd' : |du s| ≤ exp (-(s - 1)) := by
    simpa only [one_mul, neg_mul, one_mul, sub_zero,
      show s - (s - 1) = 1 by ring, div_one] using hd
  constructor
  · rw [abs_of_nonneg (hnn s (Ioo_subset_Icc_self hsI))]
    exact hv'.trans (exp_le_exp.mpr (by linarith [hs.1]))
  · exact hd'.trans (exp_le_exp.mpr (by linarith [hs.1]))

end ContinuousFlexibility.Radial
