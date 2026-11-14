module

public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
public import Mathlib.Analysis.Calculus.Deriv.MeanValue
public import Mathlib.Topology.Order.Monotone

/-!
# Dirichlet cut through a positive cap: Riccati comparison

Paper §5, eq. (js6). Let `u'' = q u` on `[0, L]` with `0 ≤ q ≤ M ^ 2`, `u 0 = 0` and
`0 < u' 0`. Then `u` and `u'` are positive on `(0, L]` (indeed `u' 0 ≤ u'`), the
Wronskian against the constant-potential solution `sinh (M x)` has a sign,

  `u' x * sinh (M x) ≤ u x * M cosh (M x)`,

and consequently the logarithmic slope satisfies

  `0 < u' x / u x ≤ M coth (M x) ≤ M + 1 / x`  for `x ∈ (0, L]`.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Radial

open Set Real

/-! ### Elementary hyperbolic facts (proved from `exp`, to avoid an unbuilt import) -/

private lemma hasDerivAt_sinh_mul (M x : ℝ) :
    HasDerivAt (fun y => Real.sinh (M * y)) (M * Real.cosh (M * x)) x := by
  have hl : HasDerivAt (fun y => M * y) M x := by
    simpa using (hasDerivAt_id x).const_mul M
  have hn : HasDerivAt (fun y => -(M * y)) (-M) x := hl.neg
  have := (hl.exp.sub hn.exp).div_const 2
  rw [show (fun y => Real.sinh (M * y))
      = fun y => (Real.exp (M * y) - Real.exp (-(M * y))) / 2 from
      funext fun y => Real.sinh_eq _]
  convert this using 1
  rw [Real.cosh_eq]
  ring

private lemma hasDerivAt_cosh_mul (M x : ℝ) :
    HasDerivAt (fun y => Real.cosh (M * y)) (M * Real.sinh (M * x)) x := by
  have hl : HasDerivAt (fun y => M * y) M x := by
    simpa using (hasDerivAt_id x).const_mul M
  have hn : HasDerivAt (fun y => -(M * y)) (-M) x := hl.neg
  have := (hl.exp.add hn.exp).div_const 2
  rw [show (fun y => Real.cosh (M * y))
      = fun y => (Real.exp (M * y) + Real.exp (-(M * y))) / 2 from
      funext fun y => Real.cosh_eq _]
  convert this using 1
  rw [Real.sinh_eq]
  ring

private lemma sinh_pos_of_pos' {t : ℝ} (ht : 0 < t) : 0 < Real.sinh t := by
  rw [Real.sinh_eq]
  have : Real.exp (-t) < Real.exp t := Real.exp_lt_exp.2 (by linarith)
  linarith

private lemma sinh_nonneg_of_nonneg' {t : ℝ} (ht : 0 ≤ t) : 0 ≤ Real.sinh t := by
  rw [Real.sinh_eq]
  have : Real.exp (-t) ≤ Real.exp t := Real.exp_le_exp.2 (by linarith)
  linarith

/-- Auxiliary: if `u' > 0` on `[0, b)`, then `u ≥ 0` on `[0, b]` and `u' 0 ≤ u' b`. -/
private lemma dirichlet_aux {u u' q : ℝ → ℝ} {L b : ℝ}
    (hu : ∀ x ∈ Icc 0 L, HasDerivAt u (u' x) x)
    (hu' : ∀ x ∈ Icc 0 L, HasDerivAt u' (q x * u x) x)
    (hq0 : ∀ x ∈ Icc 0 L, 0 ≤ q x) (h0 : u 0 = 0)
    (hb0 : 0 ≤ b) (hbL : b ≤ L) (hpos : ∀ y ∈ Ico 0 b, 0 < u' y) :
    (∀ y ∈ Icc 0 b, 0 ≤ u y) ∧ u' 0 ≤ u' b := by
  have hsub : Icc 0 b ⊆ Icc 0 L := Icc_subset_Icc le_rfl hbL
  have hcu : ContinuousOn u (Icc 0 b) := fun y hy =>
    (hu y (hsub hy)).continuousAt.continuousWithinAt
  have hcu' : ContinuousOn u' (Icc 0 b) := fun y hy =>
    (hu' y (hsub hy)).continuousAt.continuousWithinAt
  have hmono : MonotoneOn u (Icc 0 b) := by
    apply monotoneOn_of_deriv_nonneg (convex_Icc 0 b) hcu
    · intro y hy
      rw [interior_Icc] at hy
      exact (hu y (hsub (Ioo_subset_Icc_self hy))).differentiableAt.differentiableWithinAt
    · intro y hy
      rw [interior_Icc] at hy
      rw [(hu y (hsub (Ioo_subset_Icc_self hy))).deriv]
      exact (hpos y ⟨hy.1.le, hy.2⟩).le
  have hnn : ∀ y ∈ Icc 0 b, 0 ≤ u y := fun y hy => by
    have := hmono ⟨le_rfl, hb0⟩ hy hy.1
    rwa [h0] at this
  have hmono' : MonotoneOn u' (Icc 0 b) := by
    apply monotoneOn_of_deriv_nonneg (convex_Icc 0 b) hcu'
    · intro y hy
      rw [interior_Icc] at hy
      exact (hu' y (hsub (Ioo_subset_Icc_self hy))).differentiableAt.differentiableWithinAt
    · intro y hy
      rw [interior_Icc] at hy
      rw [(hu' y (hsub (Ioo_subset_Icc_self hy))).deriv]
      exact mul_nonneg (hq0 y (hsub (Ioo_subset_Icc_self hy)))
        (hnn y (Ioo_subset_Icc_self hy))
  exact ⟨hnn, hmono' ⟨le_rfl, hb0⟩ ⟨hb0, le_rfl⟩ hb0⟩

/-- The derivative stays positive on the whole closed interval `[0, L]`. -/
theorem dirichlet_deriv_pos_Icc {u u' q : ℝ → ℝ} {L M : ℝ}
    (hu : ∀ x ∈ Icc 0 L, HasDerivAt u (u' x) x)
    (hu' : ∀ x ∈ Icc 0 L, HasDerivAt u' (q x * u x) x)
    (hq : ∀ x ∈ Icc 0 L, 0 ≤ q x ∧ q x ≤ M ^ 2) (h0 : u 0 = 0) (h1 : 0 < u' 0) :
    ∀ x ∈ Icc 0 L, 0 < u' x := by
  have hq0 : ∀ x ∈ Icc 0 L, 0 ≤ q x := fun x hx => (hq x hx).1
  by_contra hcon
  simp only [not_forall, not_lt] at hcon
  obtain ⟨x, hx, hx'⟩ := hcon
  have hcont : ContinuousOn u' (Icc 0 L) := fun y hy =>
    (hu' y hy).continuousAt.continuousWithinAt
  set S : Set ℝ := Icc 0 L ∩ u' ⁻¹' Iic 0 with hSdef
  have hS : IsClosed S := hcont.preimage_isClosed_of_isClosed isClosed_Icc isClosed_Iic
  have hne : S.Nonempty := ⟨x, hx, hx'⟩
  have hbdd : BddBelow S := ⟨0, fun y hy => hy.1.1⟩
  have ha : sInf S ∈ S := hS.csInf_mem hne hbdd
  have haL : sInf S ∈ Icc 0 L := ha.1
  have ha' : u' (sInf S) ≤ 0 := ha.2
  have hpos : ∀ y ∈ Ico 0 (sInf S), 0 < u' y := by
    intro y hy
    by_contra hy'
    have hyS : y ∈ S := ⟨⟨hy.1, hy.2.le.trans haL.2⟩, not_lt.1 hy'⟩
    exact absurd (csInf_le hbdd hyS) (not_le.2 hy.2)
  have := (dirichlet_aux hu hu' hq0 h0 haL.1 haL.2 hpos).2
  linarith

/-- `u` is nonnegative on `[0, L]`. -/
theorem dirichlet_nonneg {u u' q : ℝ → ℝ} {L M : ℝ}
    (hu : ∀ x ∈ Icc 0 L, HasDerivAt u (u' x) x)
    (hu' : ∀ x ∈ Icc 0 L, HasDerivAt u' (q x * u x) x)
    (hq : ∀ x ∈ Icc 0 L, 0 ≤ q x ∧ q x ≤ M ^ 2) (h0 : u 0 = 0) (h1 : 0 < u' 0) :
    ∀ x ∈ Icc 0 L, 0 ≤ u x := by
  intro x hx
  have hd := dirichlet_deriv_pos_Icc hu hu' hq h0 h1
  exact (dirichlet_aux hu hu' (fun y hy => (hq y hy).1) h0 hx.1 hx.2
    (fun y hy => hd y ⟨hy.1, hy.2.le.trans hx.2⟩)).1 x ⟨hx.1, le_rfl⟩

/-- The slope never drops below its initial value: `u' 0 ≤ u' x` on `[0, L]`. -/
theorem dirichlet_deriv_ge {u u' q : ℝ → ℝ} {L M : ℝ}
    (hu : ∀ x ∈ Icc 0 L, HasDerivAt u (u' x) x)
    (hu' : ∀ x ∈ Icc 0 L, HasDerivAt u' (q x * u x) x)
    (hq : ∀ x ∈ Icc 0 L, 0 ≤ q x ∧ q x ≤ M ^ 2) (h0 : u 0 = 0) (h1 : 0 < u' 0) :
    ∀ x ∈ Icc 0 L, u' 0 ≤ u' x := by
  intro x hx
  have hd := dirichlet_deriv_pos_Icc hu hu' hq h0 h1
  exact (dirichlet_aux hu hu' (fun y hy => (hq y hy).1) h0 hx.1 hx.2
    (fun y hy => hd y ⟨hy.1, hy.2.le.trans hx.2⟩)).2

/-- Positivity of `u` and `u'` on `(0, L]`. -/
theorem dirichlet_pos {u u' q : ℝ → ℝ} {L M : ℝ}
    (hu : ∀ x ∈ Icc 0 L, HasDerivAt u (u' x) x)
    (hu' : ∀ x ∈ Icc 0 L, HasDerivAt u' (q x * u x) x)
    (hq : ∀ x ∈ Icc 0 L, 0 ≤ q x ∧ q x ≤ M ^ 2) (h0 : u 0 = 0) (h1 : 0 < u' 0) :
    ∀ x ∈ Ioc 0 L, 0 < u x ∧ 0 < u' x := by
  intro x hx
  have hd := dirichlet_deriv_pos_Icc hu hu' hq h0 h1
  have hcu : ContinuousOn u (Icc 0 L) := fun y hy =>
    (hu y hy).continuousAt.continuousWithinAt
  have hsm : StrictMonoOn u (Icc 0 L) := by
    apply strictMonoOn_of_deriv_pos (convex_Icc 0 L) hcu
    intro y hy
    rw [interior_Icc] at hy
    rw [(hu y (Ioo_subset_Icc_self hy)).deriv]
    exact hd y (Ioo_subset_Icc_self hy)
  have hL : (0 : ℝ) ≤ L := hx.1.le.trans hx.2
  have := hsm ⟨le_rfl, hL⟩ ⟨hx.1.le, hx.2⟩ hx.1
  rw [h0] at this
  exact ⟨this, hd x ⟨hx.1.le, hx.2⟩⟩

/-- Wronskian comparison with the constant-potential solution `sinh (M x)`. -/
theorem dirichlet_wronskian_le {u u' q : ℝ → ℝ} {L M : ℝ} (hM : 0 < M)
    (hu : ∀ x ∈ Icc 0 L, HasDerivAt u (u' x) x)
    (hu' : ∀ x ∈ Icc 0 L, HasDerivAt u' (q x * u x) x)
    (hq : ∀ x ∈ Icc 0 L, 0 ≤ q x ∧ q x ≤ M ^ 2) (h0 : u 0 = 0) (h1 : 0 < u' 0) :
    ∀ x ∈ Icc 0 L, u' x * Real.sinh (M * x) ≤ u x * (M * Real.cosh (M * x)) := by
  have hnn := dirichlet_nonneg hu hu' hq h0 h1
  have hW : ∀ x ∈ Icc 0 L, HasDerivAt
      (fun y => u' y * Real.sinh (M * y) - u y * (M * Real.cosh (M * y)))
      ((q x - M ^ 2) * u x * Real.sinh (M * x)) x := by
    intro x hx
    have := ((hu' x hx).mul (hasDerivAt_sinh_mul M x)).sub
      ((hu x hx).mul ((hasDerivAt_cosh_mul M x).const_mul M))
    convert this using 1
    ring
  have hanti : AntitoneOn
      (fun y => u' y * Real.sinh (M * y) - u y * (M * Real.cosh (M * y))) (Icc 0 L) := by
    apply antitoneOn_of_deriv_nonpos (convex_Icc 0 L)
    · exact fun y hy => (hW y hy).continuousAt.continuousWithinAt
    · intro y hy
      rw [interior_Icc] at hy
      exact (hW y (Ioo_subset_Icc_self hy)).differentiableAt.differentiableWithinAt
    · intro y hy
      rw [interior_Icc] at hy
      have hy' : y ∈ Icc 0 L := Ioo_subset_Icc_self hy
      rw [(hW y hy').deriv]
      exact mul_nonpos_of_nonpos_of_nonneg
        (mul_nonpos_of_nonpos_of_nonneg (sub_nonpos.2 (hq y hy').2) (hnn y hy'))
        (sinh_nonneg_of_nonneg' (mul_nonneg hM.le hy'.1))
  intro x hx
  have hL : (0 : ℝ) ≤ L := hx.1.trans hx.2
  have := hanti ⟨le_rfl, hL⟩ hx hx.1
  simp only [mul_zero, Real.sinh_zero, Real.cosh_zero, h0, zero_mul, sub_zero] at this
  linarith

/-- The logarithmic slope is positive on `(0, L]`. -/
theorem dirichlet_logSlope_pos {u u' q : ℝ → ℝ} {L M : ℝ}
    (hu : ∀ x ∈ Icc 0 L, HasDerivAt u (u' x) x)
    (hu' : ∀ x ∈ Icc 0 L, HasDerivAt u' (q x * u x) x)
    (hq : ∀ x ∈ Icc 0 L, 0 ≤ q x ∧ q x ≤ M ^ 2) (h0 : u 0 = 0) (h1 : 0 < u' 0) :
    ∀ x ∈ Ioc 0 L, 0 < u' x / u x := by
  intro x hx
  obtain ⟨hux, hu'x⟩ := dirichlet_pos hu hu' hq h0 h1 x hx
  exact div_pos hu'x hux

/-- Riccati comparison: `u' / u ≤ M coth (M x)` on `(0, L]`. -/
theorem dirichlet_logSlope_le {u u' q : ℝ → ℝ} {L M : ℝ} (hM : 0 < M)
    (hu : ∀ x ∈ Icc 0 L, HasDerivAt u (u' x) x)
    (hu' : ∀ x ∈ Icc 0 L, HasDerivAt u' (q x * u x) x)
    (hq : ∀ x ∈ Icc 0 L, 0 ≤ q x ∧ q x ≤ M ^ 2) (h0 : u 0 = 0) (h1 : 0 < u' 0) :
    ∀ x ∈ Ioc 0 L, u' x / u x ≤ M * Real.cosh (M * x) / Real.sinh (M * x) := by
  intro x hx
  have hux := (dirichlet_pos hu hu' hq h0 h1 x hx).1
  have hs : 0 < Real.sinh (M * x) := sinh_pos_of_pos' (mul_pos hM hx.1)
  have hW := dirichlet_wronskian_le hM hu hu' hq h0 h1 x ⟨hx.1.le, hx.2⟩
  rw [div_le_div_iff₀ hux hs]
  calc u' x * Real.sinh (M * x) ≤ u x * (M * Real.cosh (M * x)) := hW
    _ = M * Real.cosh (M * x) * u x := by ring

/-- Elementary inequality `t cosh t ≤ (t + 1) sinh t` (valid for every real `t`);
for `t > 0` it says `coth t ≤ 1 + 1/t`. -/
lemma self_mul_cosh_le_add_one_mul_sinh (t : ℝ) :
    t * Real.cosh t ≤ (t + 1) * Real.sinh t := by
  -- with `a = exp t`, `b = exp (-t)`, `a b = 1`, the claim is `b (2 t + 1) ≤ a`,
  -- which follows from `2 t + 1 ≤ exp (2 t) = a * a`.
  have hab : Real.exp t * Real.exp (-t) = 1 := by
    rw [← Real.exp_add]; simp
  have h2 : 2 * t + 1 ≤ Real.exp t * Real.exp t := by
    rw [← Real.exp_add]; linarith [Real.add_one_le_exp (t + t)]
  have hb : 0 ≤ Real.exp (-t) := (Real.exp_pos _).le
  have h3 : Real.exp (-t) * (2 * t + 1) ≤ Real.exp t := by
    calc Real.exp (-t) * (2 * t + 1) ≤ Real.exp (-t) * (Real.exp t * Real.exp t) :=
          mul_le_mul_of_nonneg_left h2 hb
      _ = (Real.exp t * Real.exp (-t)) * Real.exp t := by ring
      _ = Real.exp t := by rw [hab, one_mul]
  rw [Real.cosh_eq, Real.sinh_eq]
  nlinarith [h3]

/-- Convenient corollary: `u' / u ≤ M + 1 / x` on `(0, L]`. -/
theorem dirichlet_logSlope_le_add {u u' q : ℝ → ℝ} {L M : ℝ} (hM : 0 < M)
    (hu : ∀ x ∈ Icc 0 L, HasDerivAt u (u' x) x)
    (hu' : ∀ x ∈ Icc 0 L, HasDerivAt u' (q x * u x) x)
    (hq : ∀ x ∈ Icc 0 L, 0 ≤ q x ∧ q x ≤ M ^ 2) (h0 : u 0 = 0) (h1 : 0 < u' 0) :
    ∀ x ∈ Ioc 0 L, u' x / u x ≤ M + 1 / x := by
  intro x hx
  refine (dirichlet_logSlope_le hM hu hu' hq h0 h1 x hx).trans ?_
  have hs : 0 < Real.sinh (M * x) := sinh_pos_of_pos' (mul_pos hM hx.1)
  have key := self_mul_cosh_le_add_one_mul_sinh (M * x)
  rw [div_le_iff₀ hs]
  have hx1 : x * (1 / x) = 1 := mul_one_div_cancel hx.1.ne'
  have e : x * ((M + 1 / x) * Real.sinh (M * x)) = (M * x + 1) * Real.sinh (M * x) := by
    rw [show x * ((M + 1 / x) * Real.sinh (M * x))
        = M * x * Real.sinh (M * x) + (x * (1 / x)) * Real.sinh (M * x) by ring, hx1]
    ring
  refine le_of_mul_le_mul_left ?_ hx.1
  rw [e]
  linarith

end ContinuousFlexibility.Radial
