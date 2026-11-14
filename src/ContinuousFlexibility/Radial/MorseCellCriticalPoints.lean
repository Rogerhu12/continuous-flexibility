module

public import ContinuousFlexibility.Radial.MorseCellJoinCollars

/-!
# The actual simple critical points of a Morse model profile

The log-height slope is converted to the derivative of the actual
physical height. Differentiating its model pullback at a root gives
the ordinary physical second derivative, with the correct positive
radius and speed factors.
-/

@[expose] public section

namespace ContinuousFlexibility.Radial

open Filter Real Set
open scoped ContDiff Topology

noncomputable def morseCollarExpHeight (r : ℝ → ℝ) (amplitude s a b : ℝ) (y : ℝ) : ℝ :=
  exp (morseCollarLogProfile r amplitude s a b y)

/-- The exponential is the literal physical height at a model radius. -/
theorem morseCollarExpHeight_at_model {A B amplitude s a b x : ℝ} {r : ℝ → ℝ}
    (hAmp : 0 < amplitude) (hs : 0 < s) (hr : ContDiff ℝ ∞ r)
    (hv : ∀ t ∈ Ioo a b, 0 < deriv r t) (hx : x ∈ Ioo a b)
    (hEq : deriv (deriv r) x = -morseRho A B x * r x) :
    morseCollarExpHeight r amplitude s a b (s * r x) = amplitude * s * deriv r x := by
  have hInv := (morseCollarLogProfile_jet hAmp hs hr hv hx hEq).1
  unfold morseCollarExpHeight morseCollarLogProfile
  rw [hInv, exp_log (mul_pos (mul_pos hAmp hs) (hv x hx))]

theorem hasDerivAt_morseCollarExpHeight {A B amplitude s a b x : ℝ} {r : ℝ → ℝ}
    (hAmp : 0 < amplitude) (hs : 0 < s) (hr : ContDiff ℝ ∞ r)
    (hv : ∀ t ∈ Ioo a b, 0 < deriv r t) (hx : x ∈ Ioo a b)
    (hEq : deriv (deriv r) x = -morseRho A B x * r x) :
    HasDerivAt (morseCollarExpHeight r amplitude s a b)
      (-amplitude * morseRho A B x * r x / deriv r x) (s * r x) := by
  have hd := (morseCollarLogProfile_jet hAmp hs hr hv hx hEq).2.2.exp
  apply hd.congr_deriv
  change morseCollarExpHeight r amplitude s a b (s * r x) *
      (-morseRho A B x * r x / (s * deriv r x ^ 2)) =
    -amplitude * morseRho A B x * r x / deriv r x
  rw [morseCollarExpHeight_at_model hAmp hs hr hv hx hEq]
  field_simp [hs.ne', (hv x hx).ne']

/-- At a genuine coefficient root, the actual ordinary second derivative
in physical radius has the nonzero simple-root factor. -/
theorem morseCollarExpHeight_second_deriv_at_root {A B amplitude s a b x : ℝ} {r : ℝ → ℝ}
    (hAmp : 0 < amplitude) (hs : 0 < s) (hr : ContDiff ℝ ∞ r)
    (hv : ∀ t ∈ Ioo a b, 0 < deriv r t) (hx : x ∈ Ioo a b)
    (hEq : ∀ t ∈ Ioo a b, deriv (deriv r) t = -morseRho A B t * r t)
    (hRoot : morseRho A B x = 0) :
    deriv (deriv (morseCollarExpHeight r amplitude s a b)) (s * r x) =
      -amplitude * deriv (morseRho A B) x * r x / (s * deriv r x ^ 2) := by
  let w := morseCollarExpHeight r amplitude s a b
  let R := fun t => s * r t
  let v := deriv r
  let ρ := morseRho A B
  let H := fun t => -amplitude * ρ t * r t / v t
  have hV : ContDiff ℝ ∞ v := (contDiff_infty_iff_deriv.mp hr).2
  have hvp : 0 < v x := hv x hx
  have hW : ContDiffAt ℝ ∞ w (R x) :=
    (morseCollarLogProfile_jet hAmp hs hr hv hx (hEq x hx)).2.1.exp
  have hWD : ContDiffAt ℝ 1 (deriv w) (R x) := hW.derivWithin (by simp)
  have hR : HasDerivAt R (s * v x) x := ((hr.differentiable (by simp) x).hasDerivAt).const_mul s
  have hComp : HasDerivAt (fun t => deriv w (R t))
      (deriv (deriv w) (R x) * (s * v x)) x :=
    ((hWD.differentiableAt (by norm_num)).hasDerivAt).comp x hR
  have he : (fun t => deriv w (R t)) =ᶠ[𝓝 x] H := by
    filter_upwards [Ioo_mem_nhds hx.1 hx.2] with t ht
    exact (hasDerivAt_morseCollarExpHeight hAmp hs hr hv ht (hEq t ht)).deriv
  have hH : HasDerivAt H (-amplitude * deriv ρ x * r x / v x) x := by
    have hρ := ((contDiff_morseRho A B).differentiable (by simp) x).hasDerivAt
    have hR₀ := (hr.differentiable (by simp) x).hasDerivAt
    have hvD := (hV.differentiable (by simp) x).hasDerivAt
    apply ((((hρ.const_mul (-amplitude)).mul hR₀).div hvD hvp.ne')).congr_deriv
    change ((-amplitude * deriv ρ x * r x + -amplitude * ρ x * v x) * v x -
      -amplitude * ρ x * r x * deriv v x) / v x ^ 2 =
      -amplitude * deriv ρ x * r x / v x
    change ρ x = 0 at hRoot
    rw [hRoot]
    field_simp [hvp.ne']
    ring
  have hD : deriv (deriv w) (R x) * (s * v x) = -amplitude * deriv ρ x * r x / v x :=
    hComp.deriv.symm.trans (he.deriv_eq.trans hH.deriv)
  change deriv (deriv w) (R x) = -amplitude * deriv ρ x * r x / (s * v x ^ 2)
  apply (eq_div_iff (mul_ne_zero hs.ne' (pow_ne_zero _ hvp.ne'))).mpr
  calc
    _ = (deriv (deriv w) (R x) * (s * v x)) * v x := by ring
    _ = _ := by rw [hD, div_mul_cancel₀ _ hvp.ne']

/-- In the actual physical profile on a positive model interval, the
only stationary radii correspond to the true two turning points.
Both roots are simple, and the derivative has the opposite sign of
the true Morse coefficient. -/
theorem morseCollarExpHeight_critical {A B amplitude s a b x : ℝ} {r : ℝ → ℝ}
    (hB : 0 < B) (hAB : 4 * B < A)
    (hAmp : 0 < amplitude) (hs : 0 < s) (hr : ContDiff ℝ ∞ r)
    (hv : ∀ t ∈ Ioo a b, 0 < deriv r t) (hx : x ∈ Ioo a b)
    (hrx : 0 < r x)
    (hEq : ∀ t ∈ Ioo a b, deriv (deriv r) t = -morseRho A B t * r t) :
    let w := morseCollarExpHeight r amplitude s a b
    (deriv w (s * r x) = 0 ↔ x = morseLeftTurn A B ∨ x = morseRightTurn A B) ∧
    (deriv w (s * r x) < 0 ↔ 0 < morseRho A B x) ∧
    (0 < deriv w (s * r x) ↔ morseRho A B x < 0) ∧
    (deriv w (s * r x) = 0 → deriv (deriv w) (s * r x) ≠ 0) := by
  let w := morseCollarExpHeight r amplitude s a b
  have h := (hasDerivAt_morseCollarExpHeight hAmp hs hr hv hx (hEq x hx)).deriv
  change deriv w (s * r x) = -amplitude * morseRho A B x * r x / deriv r x at h
  have hz : deriv w (s * r x) = 0 ↔ morseRho A B x = 0 := by
    rw [h]
    constructor
    · intro he
      have he' := (div_eq_iff (hv x hx).ne').mp he
      rw [zero_mul] at he'
      exact (mul_eq_zero.mp ((mul_eq_zero.mp he').resolve_right hrx.ne')).resolve_left
        (neg_ne_zero.mpr hAmp.ne')
    · intro he
      rw [he, mul_zero, zero_mul, zero_div]
  refine ⟨hz.trans (morseRho_zero_iff_turn hB hAB x), ?_, ?_, ?_⟩
  · rw [h, div_lt_iff₀ (hv x hx), zero_mul]
    constructor
    · intro hlt
      by_contra hn
      have hp : 0 ≤ -amplitude * morseRho A B x * r x :=
        mul_nonneg (mul_nonneg_of_nonpos_of_nonpos (neg_nonpos.mpr hAmp.le) (le_of_not_gt hn)) hrx.le
      exact (not_lt_of_ge hp) hlt
    · intro hpos
      exact mul_neg_of_neg_of_pos (mul_neg_of_neg_of_pos (neg_neg_of_pos hAmp) hpos) hrx
  · rw [h, lt_div_iff₀ (hv x hx), zero_mul]
    constructor
    · intro hpos
      by_contra hn
      have hp : -amplitude * morseRho A B x * r x ≤ 0 :=
        mul_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hAmp.le)
          (le_of_not_gt hn)) hrx.le
      exact (not_lt_of_ge hp) hpos
    · intro hneg
      exact mul_pos (mul_pos_of_neg_of_neg (neg_neg_of_pos hAmp) hneg) hrx
  · intro hw
    have hrho : morseRho A B x = 0 := hz.mp hw
    have hρ' : deriv (morseRho A B) x ≠ 0 := by
      rcases (morseRho_zero_iff_turn hB hAB x).mp hrho with he | he
      · rw [he]
        exact (morseRho_deriv_left_turn_pos hB hAB).ne'
      · rw [he]
        exact (morseRho_deriv_right_turn_neg hB hAB).ne
    rw [morseCollarExpHeight_second_deriv_at_root hAmp hs hr hv hx hEq hrho]
    exact div_ne_zero (mul_ne_zero (mul_ne_zero (neg_ne_zero.mpr hAmp.ne') hρ') hrx.ne')
      (mul_ne_zero hs.ne' (pow_ne_zero _ (hv x hx).ne'))

end ContinuousFlexibility.Radial
