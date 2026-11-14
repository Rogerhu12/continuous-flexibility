module

public import Mathlib.Analysis.Calculus.Deriv.MeanValue
public import Mathlib.Analysis.Calculus.Deriv.Slope
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# Transfer estimates for the transition inputs

Elementary ODE transfer bounds from `paper/flexible-surface-rewrite/06-global-reference-inverse.tex`
(the transfer estimate inside `eq:transition-inputs-new`).

* `gronwall_integral_exp`: Gronwall with an integral exponent, in both directions.
* `transfer_positive_piece`, `transfer_positive_piece_optimal`: on a positive piece the state
  `(u, z)` with `u' = α z`, `z' = β u` has transfer bounded by `exp (2 √(∫α ∫β))`.
* `negative_energy_hasDerivAt`, `negative_energy_abs_deriv_le`, `negative_energy_transfer`:
  the energy `E = u'² + (1 + j² ρ) u²` of `u'' + j² ρ u = 0`.
* `negative_integral_log_le`: the one-peak bound `∫ j²|ρ'|/(1+j²ρ) ≤ 2 log (1 + j² ρ(Xm))`.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Radial

open Set intervalIntegral

/-! ### Gronwall with integral exponent -/

theorem gronwall_forward_aux {κ E E' : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b) (hκ : Continuous κ)
    (hE : ∀ r ∈ Icc a b, HasDerivAt E (E' r) r)
    (hbound : ∀ r ∈ Icc a b, E' r ≤ κ r * E r) :
    E b ≤ E a * Real.exp (∫ x in a..b, κ x) := by
  have hG : ∀ x, HasDerivAt (fun y => ∫ t in a..y, κ t) (κ x) x :=
    fun x => (hκ.integral_hasStrictDerivAt a x).hasDerivAt
  have hg : ∀ x ∈ Icc a b, HasDerivAt (fun y => E y * Real.exp (-∫ t in a..y, κ t))
      (E' x * Real.exp (-∫ t in a..x, κ t)
        + E x * (Real.exp (-∫ t in a..x, κ t) * (-κ x))) x :=
    fun x hx => (hE x hx).mul ((hG x).neg.exp)
  have hanti : AntitoneOn (fun y => E y * Real.exp (-∫ t in a..y, κ t)) (Icc a b) := by
    apply antitoneOn_of_deriv_nonpos (convex_Icc a b)
    · intro x hx
      exact (hg x hx).continuousAt.continuousWithinAt
    · intro x hx
      rw [interior_Icc] at hx
      exact (hg x (Ioo_subset_Icc_self hx)).differentiableAt.differentiableWithinAt
    · intro x hx
      rw [interior_Icc] at hx
      have hx' := Ioo_subset_Icc_self hx
      rw [(hg x hx').deriv]
      have h1 := hbound x hx'
      have h2 := (Real.exp_pos (-∫ t in a..x, κ t)).le
      nlinarith [mul_nonneg (sub_nonneg.2 h1) h2]
  have h := hanti ⟨le_refl a, hab⟩ ⟨hab, le_refl b⟩ hab
  simp only [intervalIntegral.integral_same, neg_zero, Real.exp_zero, mul_one] at h
  calc E b = E b * Real.exp (-∫ t in a..b, κ t) * Real.exp (∫ t in a..b, κ t) := by
        rw [mul_assoc, ← Real.exp_add]; simp
    _ ≤ E a * Real.exp (∫ t in a..b, κ t) :=
        mul_le_mul_of_nonneg_right h (Real.exp_pos _).le

theorem gronwall_backward_aux {κ E E' : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b) (hκ : Continuous κ)
    (hE : ∀ r ∈ Icc a b, HasDerivAt E (E' r) r)
    (hbound : ∀ r ∈ Icc a b, -(κ r * E r) ≤ E' r) :
    E a ≤ E b * Real.exp (∫ x in a..b, κ x) := by
  have hG : ∀ x, HasDerivAt (fun y => ∫ t in a..y, κ t) (κ x) x :=
    fun x => (hκ.integral_hasStrictDerivAt a x).hasDerivAt
  have hg : ∀ x ∈ Icc a b, HasDerivAt (fun y => E y * Real.exp (∫ t in a..y, κ t))
      (E' x * Real.exp (∫ t in a..x, κ t)
        + E x * (Real.exp (∫ t in a..x, κ t) * κ x)) x :=
    fun x hx => (hE x hx).mul (hG x).exp
  have hmono : MonotoneOn (fun y => E y * Real.exp (∫ t in a..y, κ t)) (Icc a b) := by
    apply monotoneOn_of_deriv_nonneg (convex_Icc a b)
    · intro x hx
      exact (hg x hx).continuousAt.continuousWithinAt
    · intro x hx
      rw [interior_Icc] at hx
      exact (hg x (Ioo_subset_Icc_self hx)).differentiableAt.differentiableWithinAt
    · intro x hx
      rw [interior_Icc] at hx
      have hx' := Ioo_subset_Icc_self hx
      rw [(hg x hx').deriv]
      have h1 := hbound x hx'
      have h2 := (Real.exp_pos (∫ t in a..x, κ t)).le
      nlinarith [mul_nonneg (by linarith : 0 ≤ E' x + κ x * E x) h2]
  have h := hmono ⟨le_refl a, hab⟩ ⟨hab, le_refl b⟩ hab
  simpa only [intervalIntegral.integral_same, Real.exp_zero, mul_one] using h

/-- Gronwall with an integral exponent, in both directions.  The coefficient `κ` is only
required to be continuous on `Icc r₀ r₁`; nonnegativity of `E` is not needed. -/
theorem gronwall_integral_exp {κ E E' : ℝ → ℝ} {r₀ r₁ : ℝ} (hr : r₀ ≤ r₁)
    (hκc : ContinuousOn κ (Icc r₀ r₁)) (hκ : ∀ r ∈ Icc r₀ r₁, 0 ≤ κ r)
    (hE : ∀ r ∈ Icc r₀ r₁, HasDerivAt E (E' r) r)
    (hbound : ∀ r ∈ Icc r₀ r₁, |E' r| ≤ κ r * E r)
    {s t : ℝ} (hs : s ∈ Icc r₀ r₁) (ht : t ∈ Icc r₀ r₁) :
    E t ≤ E s * Real.exp |∫ x in s..t, κ x| := by
  have hproj : ∀ x ∈ Icc r₀ r₁, max r₀ (min x r₁) = x := fun x hx => by
    rw [min_eq_left hx.2, max_eq_right hx.1]
  have hKc : Continuous (fun x => κ (max r₀ (min x r₁))) :=
    hκc.comp_continuous (continuous_const.max (continuous_id.min continuous_const))
      (fun x => ⟨le_max_left _ _, max_le hr (min_le_right _ _)⟩)
  have hint : ∀ a ∈ Icc r₀ r₁, ∀ b ∈ Icc r₀ r₁,
      ∫ x in a..b, κ (max r₀ (min x r₁)) = ∫ x in a..b, κ x := by
    intro a ha b hb
    apply intervalIntegral.integral_congr
    intro x hx
    have hx' := uIcc_subset_Icc ha hb hx
    show κ (max r₀ (min x r₁)) = κ x
    rw [hproj x hx']
  have hmem : ∀ a b : ℝ, a ∈ Icc r₀ r₁ → b ∈ Icc r₀ r₁ → ∀ r ∈ Icc a b, r ∈ Icc r₀ r₁ :=
    fun a b ha hb r hr' => ⟨ha.1.trans hr'.1, hr'.2.trans hb.2⟩
  rcases le_total s t with h | h
  · have key := gronwall_forward_aux h hKc
      (fun r hr' => hE r (hmem s t hs ht r hr'))
      (fun r hr' => by
        have hr2 := hmem s t hs ht r hr'
        show E' r ≤ κ (max r₀ (min r r₁)) * E r
        rw [hproj r hr2]
        exact (le_abs_self _).trans (hbound r hr2))
    rw [hint s hs t ht] at key
    have hnn : 0 ≤ ∫ x in s..t, κ x :=
      intervalIntegral.integral_nonneg h (fun x hx => hκ x (hmem s t hs ht x hx))
    rw [abs_of_nonneg hnn]
    exact key
  · have key := gronwall_backward_aux h hKc
      (fun r hr' => hE r (hmem t s ht hs r hr'))
      (fun r hr' => by
        have hr2 := hmem t s ht hs r hr'
        show -(κ (max r₀ (min r r₁)) * E r) ≤ E' r
        rw [hproj r hr2]
        exact (abs_le.1 (hbound r hr2)).1)
    rw [hint t ht s hs] at key
    have hnn : 0 ≤ ∫ x in t..s, κ x :=
      intervalIntegral.integral_nonneg h (fun x hx => hκ x (hmem t s ht hs x hx))
    rw [intervalIntegral.integral_symm t s, abs_neg, abs_of_nonneg hnn]
    exact key

/-! ### Positive piece -/

theorem pos_piece_abs_le (a b u z μ : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hμ : 0 < μ) :
    |2 * (a + μ ^ 2 * b) * (u * z)| ≤ (a / μ + μ * b) * (u * u + μ ^ 2 * (z * z)) := by
  have hc : μ * μ⁻¹ = 1 := mul_inv_cancel₀ hμ.ne'
  have h1 : (a / μ + μ * b) * (u * u + μ ^ 2 * (z * z)) - 2 * (a + μ ^ 2 * b) * (u * z)
      = (a / μ + μ * b) * (u - μ * z) ^ 2 := by
    linear_combination (2 * a * u * z) * hc
  have h2 : (a / μ + μ * b) * (u * u + μ ^ 2 * (z * z)) + 2 * (a + μ ^ 2 * b) * (u * z)
      = (a / μ + μ * b) * (u + μ * z) ^ 2 := by
    linear_combination (-2 * a * u * z) * hc
  have hk : 0 ≤ a / μ + μ * b := add_nonneg (div_nonneg ha hμ.le) (mul_nonneg hμ.le hb)
  rw [abs_le]
  constructor
  · nlinarith [mul_nonneg hk (sq_nonneg (u + μ * z))]
  · nlinarith [mul_nonneg hk (sq_nonneg (u - μ * z))]

/-- Balanced positive-piece transfer: with `u' = α z`, `z' = β u`, `α, β ≥ 0`, and any weight
`μ > 0`, the weighted energy `u² + μ² z²` grows by at most `exp |∫ (α/μ + μ β)|`. -/
theorem transfer_positive_piece {u z α β : ℝ → ℝ} {r₀ r₁ μ : ℝ} (hr : r₀ ≤ r₁) (hμ : 0 < μ)
    (hα : ContinuousOn α (Icc r₀ r₁)) (hβ : ContinuousOn β (Icc r₀ r₁))
    (hα0 : ∀ r ∈ Icc r₀ r₁, 0 ≤ α r) (hβ0 : ∀ r ∈ Icc r₀ r₁, 0 ≤ β r)
    (hd : ∀ r ∈ Icc r₀ r₁, HasDerivAt u (α r * z r) r ∧ HasDerivAt z (β r * u r) r)
    {s t : ℝ} (hs : s ∈ Icc r₀ r₁) (ht : t ∈ Icc r₀ r₁) :
    u t ^ 2 + μ ^ 2 * z t ^ 2 ≤
      (u s ^ 2 + μ ^ 2 * z s ^ 2) * Real.exp |∫ x in s..t, (α x / μ + μ * β x)| := by
  have hκc : ContinuousOn (fun x => α x / μ + μ * β x) (Icc r₀ r₁) :=
    (hα.div_const μ).add (continuousOn_const.mul hβ)
  have hκ : ∀ r ∈ Icc r₀ r₁, 0 ≤ α r / μ + μ * β r := fun r hr' =>
    add_nonneg (div_nonneg (hα0 r hr') hμ.le) (mul_nonneg hμ.le (hβ0 r hr'))
  have hE : ∀ r ∈ Icc r₀ r₁,
      HasDerivAt (fun r => u r * u r + μ ^ 2 * (z r * z r))
        (2 * (α r + μ ^ 2 * β r) * (u r * z r)) r := by
    intro r hr'
    have h := ((hd r hr').1.mul (hd r hr').1).add
      (((hd r hr').2.mul (hd r hr').2).const_mul (μ ^ 2))
    exact h.congr_deriv (by ring)
  have hbound : ∀ r ∈ Icc r₀ r₁,
      |2 * (α r + μ ^ 2 * β r) * (u r * z r)|
        ≤ (α r / μ + μ * β r) * (u r * u r + μ ^ 2 * (z r * z r)) :=
    fun r hr' => pos_piece_abs_le (α r) (β r) (u r) (z r) μ (hα0 r hr') (hβ0 r hr') hμ
  have key := gronwall_integral_exp (κ := fun x => α x / μ + μ * β x)
    (E := fun r => u r * u r + μ ^ 2 * (z r * z r))
    (E' := fun r => 2 * (α r + μ ^ 2 * β r) * (u r * z r)) hr hκc hκ hE hbound hs ht
  have e : ∀ r, u r * u r + μ ^ 2 * (z r * z r) = u r ^ 2 + μ ^ 2 * z r ^ 2 :=
    fun r => by ring
  simpa only [e] using key

theorem optimal_weight_alg (Ia Ib μ : ℝ) (hIa : 0 < Ia) (hIb : 0 < Ib)
    (hμ : μ = Real.sqrt (Ia / Ib)) :
    0 < μ ∧ Ia / μ + μ * Ib = 2 * Real.sqrt (Ia * Ib) := by
  have hμpos : 0 < μ := by rw [hμ]; exact Real.sqrt_pos.2 (div_pos hIa hIb)
  have hsq : μ ^ 2 = Ia / Ib := by rw [hμ]; exact Real.sq_sqrt (div_pos hIa hIb).le
  have hIaeq : Ia = μ ^ 2 * Ib := (div_eq_iff hIb.ne').1 hsq.symm
  have h1 : Ia / μ = μ * Ib := by
    rw [div_eq_iff hμpos.ne']
    rw [hIaeq]; ring
  have h2 : Ia * Ib = (μ * Ib) ^ 2 := by rw [hIaeq]; ring
  refine ⟨hμpos, ?_⟩
  rw [h1, h2, Real.sqrt_sq (mul_pos hμpos hIb).le]
  ring

/-- Optimal-weight corollary: transfer in either direction is bounded by
`exp (2 √(∫α ∫β))`, with `μ = √(∫α / ∫β)`. -/
theorem transfer_positive_piece_optimal {u z α β : ℝ → ℝ} {r₀ r₁ μ : ℝ} (hr : r₀ ≤ r₁)
    (hα : ContinuousOn α (Icc r₀ r₁)) (hβ : ContinuousOn β (Icc r₀ r₁))
    (hα0 : ∀ r ∈ Icc r₀ r₁, 0 ≤ α r) (hβ0 : ∀ r ∈ Icc r₀ r₁, 0 ≤ β r)
    (hd : ∀ r ∈ Icc r₀ r₁, HasDerivAt u (α r * z r) r ∧ HasDerivAt z (β r * u r) r)
    (hIa : 0 < ∫ x in r₀..r₁, α x) (hIb : 0 < ∫ x in r₀..r₁, β x)
    (hμ : μ = Real.sqrt ((∫ x in r₀..r₁, α x) / ∫ x in r₀..r₁, β x)) :
    u r₁ ^ 2 + μ ^ 2 * z r₁ ^ 2 ≤
        (u r₀ ^ 2 + μ ^ 2 * z r₀ ^ 2) *
          Real.exp (2 * Real.sqrt ((∫ x in r₀..r₁, α x) * ∫ x in r₀..r₁, β x)) ∧
      u r₀ ^ 2 + μ ^ 2 * z r₀ ^ 2 ≤
        (u r₁ ^ 2 + μ ^ 2 * z r₁ ^ 2) *
          Real.exp (2 * Real.sqrt ((∫ x in r₀..r₁, α x) * ∫ x in r₀..r₁, β x)) := by
  obtain ⟨hμpos, halg⟩ := optimal_weight_alg _ _ μ hIa hIb hμ
  have hαi : IntervalIntegrable (fun x => α x / μ) MeasureTheory.volume r₀ r₁ :=
    (hα.div_const μ).intervalIntegrable_of_Icc hr
  have hβi : IntervalIntegrable (fun x => μ * β x) MeasureTheory.volume r₀ r₁ :=
    (continuousOn_const.mul hβ).intervalIntegrable_of_Icc hr
  have hI : ∫ x in r₀..r₁, (α x / μ + μ * β x)
      = 2 * Real.sqrt ((∫ x in r₀..r₁, α x) * ∫ x in r₀..r₁, β x) := by
    rw [intervalIntegral.integral_add hαi hβi, intervalIntegral.integral_div,
      intervalIntegral.integral_const_mul]
    exact halg
  have hnn : 0 ≤ 2 * Real.sqrt ((∫ x in r₀..r₁, α x) * ∫ x in r₀..r₁, β x) := by positivity
  constructor
  · have key := transfer_positive_piece hr hμpos hα hβ hα0 hβ0 hd
      (s := r₀) (t := r₁) ⟨le_refl _, hr⟩ ⟨hr, le_refl _⟩
    rw [hI, abs_of_nonneg hnn] at key
    exact key
  · have key := transfer_positive_piece hr hμpos hα hβ hα0 hβ0 hd
      (s := r₁) (t := r₀) ⟨hr, le_refl _⟩ ⟨le_refl _, hr⟩
    rw [intervalIntegral.integral_symm r₀ r₁, abs_neg, hI, abs_of_nonneg hnn] at key
    exact key

/-! ### Negative component -/

theorem negative_energy_hasDerivAt {u u' ρ ρ' : ℝ → ℝ} {j X : ℝ}
    (hu : HasDerivAt u (u' X) X) (hu' : HasDerivAt u' (-(j ^ 2 * ρ X * u X)) X)
    (hρ : HasDerivAt ρ (ρ' X) X) :
    HasDerivAt (fun Y => u' Y ^ 2 + (1 + j ^ 2 * ρ Y) * u Y ^ 2)
      (2 * u X * u' X + j ^ 2 * ρ' X * u X ^ 2) X := by
  have h := (hu'.mul hu').add (((hρ.const_mul (j ^ 2)).const_add 1).mul (hu.mul hu))
  have hf : (fun Y => u' Y ^ 2 + (1 + j ^ 2 * ρ Y) * u Y ^ 2)
      = fun Y => u' Y * u' Y + (1 + j ^ 2 * ρ Y) * (u Y * u Y) := by
    funext Y; ring
  rw [hf]
  exact h.congr_deriv (by simp only [Pi.mul_apply]; ring)

theorem negative_energy_alg (u v P d D : ℝ) (hP : 0 ≤ P) (hD : 1 ≤ D) :
    |2 * u * v + P * d * u ^ 2| ≤ (1 + P * |d| / D) * (v ^ 2 + D * u ^ 2) := by
  have hD0 : 0 < D := by linarith
  have hq : 0 ≤ P * |d| / D := div_nonneg (mul_nonneg hP (abs_nonneg _)) hD0.le
  have h1 : |2 * u * v| ≤ v ^ 2 + D * u ^ 2 := by
    rw [abs_le]
    constructor <;>
      nlinarith [sq_nonneg (u + v), sq_nonneg (u - v), mul_nonneg (sub_nonneg.2 hD) (sq_nonneg u)]
  have h2 : |P * d * u ^ 2| ≤ P * |d| / D * (v ^ 2 + D * u ^ 2) := by
    have h3 : |P * d * u ^ 2| = P * |d| * u ^ 2 := by
      rw [abs_mul, abs_mul, abs_of_nonneg hP, abs_of_nonneg (sq_nonneg u)]
    rw [h3]
    have e : P * |d| * u ^ 2 = P * |d| / D * (D * u ^ 2) := by
      rw [div_mul_eq_mul_div, eq_div_iff hD0.ne']; ring
    rw [e]
    exact mul_le_mul_of_nonneg_left (by nlinarith [sq_nonneg v]) hq
  calc |2 * u * v + P * d * u ^ 2| ≤ |2 * u * v| + |P * d * u ^ 2| := abs_add_le _ _
    _ ≤ (1 + P * |d| / D) * (v ^ 2 + D * u ^ 2) := by nlinarith

theorem negative_energy_abs_deriv_le {u u' ρ ρ' : ℝ → ℝ} {j X : ℝ} (hρ0 : 0 ≤ ρ X) :
    |2 * u X * u' X + j ^ 2 * ρ' X * u X ^ 2|
      ≤ (1 + j ^ 2 * |ρ' X| / (1 + j ^ 2 * ρ X)) *
          (u' X ^ 2 + (1 + j ^ 2 * ρ X) * u X ^ 2) :=
  negative_energy_alg (u X) (u' X) (j ^ 2) (ρ' X) (1 + j ^ 2 * ρ X) (sq_nonneg j)
    (by have := mul_nonneg (sq_nonneg j) hρ0; linarith)

theorem continuousOn_of_hasDerivAt' {f f' : ℝ → ℝ} {s : Set ℝ}
    (h : ∀ x ∈ s, HasDerivAt f (f' x) x) : ContinuousOn f s :=
  fun x hx => (h x hx).continuousAt.continuousWithinAt

theorem continuousOn_ratio {ρ σ : ℝ → ℝ} {j : ℝ} {s : Set ℝ} (hρc : ContinuousOn ρ s)
    (hρ0 : ∀ X ∈ s, 0 ≤ ρ X) (hσ : ContinuousOn σ s) :
    ContinuousOn (fun x => j ^ 2 * σ x / (1 + j ^ 2 * ρ x)) s :=
  (continuousOn_const.mul hσ).div (continuousOn_const.add (continuousOn_const.mul hρc))
    (fun X hX => (show (0 : ℝ) < 1 + j ^ 2 * ρ X by
      have := mul_nonneg (sq_nonneg j) (hρ0 X hX); linarith).ne')

/-- Energy transfer on the negative component for `u'' + j² ρ u = 0`. -/
theorem negative_energy_transfer {u u' ρ ρ' : ℝ → ℝ} {j X₀ X₁ : ℝ} (hX : X₀ ≤ X₁)
    (hu : ∀ X ∈ Icc X₀ X₁, HasDerivAt u (u' X) X)
    (hu' : ∀ X ∈ Icc X₀ X₁, HasDerivAt u' (-(j ^ 2 * ρ X * u X)) X)
    (hρ : ∀ X ∈ Icc X₀ X₁, HasDerivAt ρ (ρ' X) X)
    (hρ0 : ∀ X ∈ Icc X₀ X₁, 0 ≤ ρ X) (hρ' : ContinuousOn ρ' (Icc X₀ X₁))
    {s t : ℝ} (hs : s ∈ Icc X₀ X₁) (ht : t ∈ Icc X₀ X₁) :
    u' t ^ 2 + (1 + j ^ 2 * ρ t) * u t ^ 2 ≤
      (u' s ^ 2 + (1 + j ^ 2 * ρ s) * u s ^ 2) *
        Real.exp |∫ X in s..t, (1 + j ^ 2 * |ρ' X| / (1 + j ^ 2 * ρ X))| := by
  have hρc : ContinuousOn ρ (Icc X₀ X₁) := continuousOn_of_hasDerivAt' hρ
  have habs : ContinuousOn (fun X => |ρ' X|) (Icc X₀ X₁) := continuous_abs.comp_continuousOn hρ'
  have hκc : ContinuousOn (fun X => 1 + j ^ 2 * |ρ' X| / (1 + j ^ 2 * ρ X)) (Icc X₀ X₁) :=
    continuousOn_const.add (continuousOn_ratio hρc hρ0 habs)
  have hκ : ∀ X ∈ Icc X₀ X₁, 0 ≤ 1 + j ^ 2 * |ρ' X| / (1 + j ^ 2 * ρ X) := by
    intro X hX'
    have hD : 0 < 1 + j ^ 2 * ρ X := by
      have := mul_nonneg (sq_nonneg j) (hρ0 X hX'); linarith
    exact add_nonneg zero_le_one (div_nonneg (mul_nonneg (sq_nonneg j) (abs_nonneg _)) hD.le)
  exact gronwall_integral_exp (κ := fun X => 1 + j ^ 2 * |ρ' X| / (1 + j ^ 2 * ρ X))
    (E := fun Y => u' Y ^ 2 + (1 + j ^ 2 * ρ Y) * u Y ^ 2)
    (E' := fun X => 2 * u X * u' X + j ^ 2 * ρ' X * u X ^ 2) hX hκc hκ
    (fun X hX' => negative_energy_hasDerivAt (hu X hX') (hu' X hX') (hρ X hX'))
    (fun X hX' => negative_energy_abs_deriv_le (hρ0 X hX')) hs ht

/-! ### One-peak bound -/

theorem log_piece_mono {ρ ρ' : ℝ → ℝ} {j a b : ℝ} (hab : a ≤ b)
    (hρ : ∀ X ∈ Icc a b, HasDerivAt ρ (ρ' X) X) (hρ0 : ∀ X ∈ Icc a b, 0 ≤ ρ X)
    (hρ' : ContinuousOn ρ' (Icc a b)) (hmono : MonotoneOn ρ (Icc a b)) :
    ∫ X in a..b, j ^ 2 * |ρ' X| / (1 + j ^ 2 * ρ X)
      = Real.log (1 + j ^ 2 * ρ b) - Real.log (1 + j ^ 2 * ρ a) := by
  have hD : ∀ X ∈ Icc a b, 0 < 1 + j ^ 2 * ρ X := fun X hX => by
    have := mul_nonneg (sq_nonneg j) (hρ0 X hX); linarith
  have hF : ∀ x ∈ uIcc a b, HasDerivAt (fun y => Real.log (1 + j ^ 2 * ρ y))
      (j ^ 2 * ρ' x / (1 + j ^ 2 * ρ x)) x := by
    intro x hx
    rw [uIcc_of_le hab] at hx
    exact (((hρ x hx).const_mul (j ^ 2)).const_add 1).log (hD x hx).ne'
  have hint : IntervalIntegrable (fun x => j ^ 2 * ρ' x / (1 + j ^ 2 * ρ x))
      MeasureTheory.volume a b :=
    (continuousOn_ratio (continuousOn_of_hasDerivAt' hρ) hρ0 hρ').intervalIntegrable_of_Icc hab
  rcases hab.eq_or_lt with h | h
  · subst h; simp
  · have hsign : ∀ x ∈ Icc a b, 0 ≤ ρ' x := fun x hx => by
      have h1 := hmono.derivWithin_nonneg (x := x)
      rwa [((hρ x hx).hasDerivWithinAt).derivWithin (uniqueDiffOn_Icc h x hx)] at h1
    calc ∫ X in a..b, j ^ 2 * |ρ' X| / (1 + j ^ 2 * ρ X)
        = ∫ X in a..b, j ^ 2 * ρ' X / (1 + j ^ 2 * ρ X) := by
          apply intervalIntegral.integral_congr
          intro x hx
          rw [uIcc_of_le hab] at hx
          show j ^ 2 * |ρ' x| / (1 + j ^ 2 * ρ x) = j ^ 2 * ρ' x / (1 + j ^ 2 * ρ x)
          rw [abs_of_nonneg (hsign x hx)]
      _ = Real.log (1 + j ^ 2 * ρ b) - Real.log (1 + j ^ 2 * ρ a) :=
          intervalIntegral.integral_eq_sub_of_hasDerivAt hF hint

theorem log_piece_anti {ρ ρ' : ℝ → ℝ} {j a b : ℝ} (hab : a ≤ b)
    (hρ : ∀ X ∈ Icc a b, HasDerivAt ρ (ρ' X) X) (hρ0 : ∀ X ∈ Icc a b, 0 ≤ ρ X)
    (hρ' : ContinuousOn ρ' (Icc a b)) (hanti : AntitoneOn ρ (Icc a b)) :
    ∫ X in a..b, j ^ 2 * |ρ' X| / (1 + j ^ 2 * ρ X)
      = Real.log (1 + j ^ 2 * ρ a) - Real.log (1 + j ^ 2 * ρ b) := by
  have hD : ∀ X ∈ Icc a b, 0 < 1 + j ^ 2 * ρ X := fun X hX => by
    have := mul_nonneg (sq_nonneg j) (hρ0 X hX); linarith
  have hF : ∀ x ∈ uIcc a b, HasDerivAt (fun y => Real.log (1 + j ^ 2 * ρ y))
      (j ^ 2 * ρ' x / (1 + j ^ 2 * ρ x)) x := by
    intro x hx
    rw [uIcc_of_le hab] at hx
    exact (((hρ x hx).const_mul (j ^ 2)).const_add 1).log (hD x hx).ne'
  have hint : IntervalIntegrable (fun x => j ^ 2 * ρ' x / (1 + j ^ 2 * ρ x))
      MeasureTheory.volume a b :=
    (continuousOn_ratio (continuousOn_of_hasDerivAt' hρ) hρ0 hρ').intervalIntegrable_of_Icc hab
  rcases hab.eq_or_lt with h | h
  · subst h; simp
  · have hsign : ∀ x ∈ Icc a b, ρ' x ≤ 0 := fun x hx => by
      have h1 := hanti.derivWithin_nonpos (x := x)
      rwa [((hρ x hx).hasDerivWithinAt).derivWithin (uniqueDiffOn_Icc h x hx)] at h1
    calc ∫ X in a..b, j ^ 2 * |ρ' X| / (1 + j ^ 2 * ρ X)
        = ∫ X in a..b, -(j ^ 2 * ρ' X / (1 + j ^ 2 * ρ X)) := by
          apply intervalIntegral.integral_congr
          intro x hx
          rw [uIcc_of_le hab] at hx
          show j ^ 2 * |ρ' x| / (1 + j ^ 2 * ρ x) = -(j ^ 2 * ρ' x / (1 + j ^ 2 * ρ x))
          rw [abs_of_nonpos (hsign x hx)]
          ring
      _ = -∫ X in a..b, j ^ 2 * ρ' X / (1 + j ^ 2 * ρ X) := intervalIntegral.integral_neg
      _ = Real.log (1 + j ^ 2 * ρ a) - Real.log (1 + j ^ 2 * ρ b) := by
          rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hF hint]; ring

/-- One-peak bound: if `ρ ≥ 0` is monotone up to `Xm` and antitone after it, then the
integrated second term is at most `2 log (1 + j² ρ(Xm))`. -/
theorem negative_integral_log_le {ρ ρ' : ℝ → ℝ} {j X₀ X₁ Xm : ℝ}
    (hρ : ∀ X ∈ Icc X₀ X₁, HasDerivAt ρ (ρ' X) X) (hρ0 : ∀ X ∈ Icc X₀ X₁, 0 ≤ ρ X)
    (hρ' : ContinuousOn ρ' (Icc X₀ X₁)) (hXm : Xm ∈ Icc X₀ X₁)
    (hmono : MonotoneOn ρ (Icc X₀ Xm)) (hanti : AntitoneOn ρ (Icc Xm X₁)) :
    ∫ X in X₀..X₁, j ^ 2 * |ρ' X| / (1 + j ^ 2 * ρ X) ≤ 2 * Real.log (1 + j ^ 2 * ρ Xm) := by
  have hsub1 : Icc X₀ Xm ⊆ Icc X₀ X₁ := Icc_subset_Icc_right hXm.2
  have hsub2 : Icc Xm X₁ ⊆ Icc X₀ X₁ := Icc_subset_Icc_left hXm.1
  have p1 := log_piece_mono (j := j) hXm.1 (fun X hX => hρ X (hsub1 hX))
    (fun X hX => hρ0 X (hsub1 hX)) (hρ'.mono hsub1) hmono
  have p2 := log_piece_anti (j := j) hXm.2 (fun X hX => hρ X (hsub2 hX))
    (fun X hX => hρ0 X (hsub2 hX)) (hρ'.mono hsub2) hanti
  have hc : ContinuousOn (fun X => j ^ 2 * |ρ' X| / (1 + j ^ 2 * ρ X)) (Icc X₀ X₁) :=
    continuousOn_ratio (continuousOn_of_hasDerivAt' hρ) hρ0 (continuous_abs.comp_continuousOn hρ')
  have i1 : IntervalIntegrable (fun X => j ^ 2 * |ρ' X| / (1 + j ^ 2 * ρ X))
      MeasureTheory.volume X₀ Xm := (hc.mono hsub1).intervalIntegrable_of_Icc hXm.1
  have i2 : IntervalIntegrable (fun X => j ^ 2 * |ρ' X| / (1 + j ^ 2 * ρ X))
      MeasureTheory.volume Xm X₁ := (hc.mono hsub2).intervalIntegrable_of_Icc hXm.2
  have hX : X₀ ≤ X₁ := hXm.1.trans hXm.2
  have l0 : 0 ≤ Real.log (1 + j ^ 2 * ρ X₀) :=
    Real.log_nonneg (by
      have := mul_nonneg (sq_nonneg j) (hρ0 X₀ ⟨le_refl _, hX⟩); linarith)
  have l1 : 0 ≤ Real.log (1 + j ^ 2 * ρ X₁) :=
    Real.log_nonneg (by
      have := mul_nonneg (sq_nonneg j) (hρ0 X₁ ⟨hX, le_refl _⟩); linarith)
  rw [← intervalIntegral.integral_add_adjacent_intervals i1 i2, p1, p2]
  linarith

end ContinuousFlexibility.Radial
