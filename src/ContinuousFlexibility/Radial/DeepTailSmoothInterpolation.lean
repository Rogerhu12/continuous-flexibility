import ContinuousFlexibility.Radial.MorseChainLocalGluing
import ContinuousFlexibility.Radial.DeepTailEdgeComparison
import Mathlib.Analysis.Calculus.FDeriv.Extend
import Mathlib.Analysis.Calculus.ContDiff.Deriv

/-!
# Smooth interpolation from matching height and flux

The actual interpolant is the existing `morseOutwardGlue`.  Matching values
and derivatives permit differentiation across every interior node; the
smooth divergence system then supplies all higher derivatives.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open Set Filter
open scoped Topology ContDiff

/-- An interior derivative with a continuous limit extends to the whole
closed interval.  One closure argument treats both endpoints. -/
theorem hasDerivWithinAt_Icc_of_continuous_derivative {a b : ℝ} {f g : ℝ → ℝ}
    (hab : a < b) (hf : ContinuousOn f (Icc a b)) (hg : ContinuousOn g (Icc a b))
    (hd : ∀ x ∈ Ioo a b, HasDerivAt f (g x) x) :
    ∀ x ∈ Icc a b, HasDerivWithinAt f (g x) (Icc a b) x := by
  intro x hx
  have hlim : Tendsto (fun y => fderiv ℝ f y) (𝓝[Ioo a b] x)
      (𝓝 ((1 : ℝ →L[ℝ] ℝ).smulRight (g x))) := by
    have hlim' : Tendsto (fun y => (1 : ℝ →L[ℝ] ℝ).smulRight (g y))
        (𝓝[Ioo a b] x) (𝓝 ((1 : ℝ →L[ℝ] ℝ).smulRight (g x))) := by
      exact Tendsto.comp
        (isBoundedBilinearMap_smulRight : IsBoundedBilinearMap ℝ _).continuous_right.continuousAt
        ((hg x hx).mono Ioo_subset_Icc_self)
    apply hlim'.congr'
    filter_upwards [self_mem_nhdsWithin] with y hy
    exact (hd y hy).hasFDerivAt.fderiv.symm
  rw [hasDerivWithinAt_iff_hasFDerivWithinAt, ← closure_Ioo hab.ne]
  apply hasFDerivWithinAt_closure_of_tendsto_fderiv
    (fun y hy => (hd y hy).differentiableAt.differentiableWithinAt)
    (convex_Ioo a b) isOpen_Ioo ?_ hlim
  intro y hy
  rw [closure_Ioo hab.ne] at hy
  exact (hf y hy).mono Ioo_subset_Icc_self

/-- Matching endpoint values give the same selected piece on a closed edge. -/
theorem morseOutwardGlue_apply_closed {node : ℕ → ℝ} {piece : ℕ → ℝ → ℝ}
    (hmono : StrictMono node)
    (hmatch : ∀ n, piece n (node (n + 1)) = piece (n + 1) (node (n + 1)))
    {n : ℕ} {x : ℝ} (hx : x ∈ Icc (node n) (node (n + 1))) :
    morseOutwardGlue node piece x = piece n x := by
  rcases lt_or_eq_of_le hx.2 with hlt | heq
  · exact morseOutwardGlue_apply_block hmono ⟨hx.1, hlt⟩
  · rw [heq, morseOutwardGlue_apply_block hmono
      (show node (n + 1) ∈ Ico (node (n + 1)) (node (n + 1 + 1)) from
        ⟨le_rfl, hmono (Nat.lt_succ_self (n + 1))⟩)]
    exact (hmatch n).symm

/-- Near the first node, the inward convention and the first outward edge
select the same piece. No regularity of later pieces is needed. -/
theorem morseOutwardGlue_eventually_first {node : ℕ → ℝ} {piece : ℕ → ℝ → ℝ}
    (hmono : StrictMono node) :
    morseOutwardGlue node piece =ᶠ[𝓝 (node 0)] piece 0 := by
  filter_upwards [Iio_mem_nhds (hmono (Nat.lt_succ_self 0))] with x hx
  by_cases h : x < node 0
  · simp only [morseOutwardGlue, if_pos h]
  · exact morseOutwardGlue_apply_block hmono ⟨le_of_not_gt h, hx⟩

/-- The actual entrance is `C¹` when the first Poisson piece is globally
`C¹`; no all-order extension of the density through the entrance is used. -/
theorem contDiffAt_one_morseOutwardGlue_first {node : ℕ → ℝ} {piece : ℕ → ℝ → ℝ}
    (hmono : StrictMono node) (hpiece : Differentiable ℝ (piece 0))
    (hdpiece : Continuous (deriv (piece 0))) :
    ContDiffAt ℝ 1 (morseOutwardGlue node piece) (node 0) :=
  (contDiff_one_iff_deriv.mpr ⟨hpiece, hdpiece⟩).contDiffAt.congr_of_eventuallyEq
    (morseOutwardGlue_eventually_first hmono)

/-- Piecewise differentiation across all nodes, using only derivatives
within each closed edge and matching first derivative values. -/
theorem hasDerivAt_morseOutwardGlue {node : ℕ → ℝ} {endpoint : ℝ}
    {piece dpiece : ℕ → ℝ → ℝ} (hmono : StrictMono node)
    (hlim : Tendsto node atTop (𝓝 endpoint))
    (hmatch : ∀ n, piece n (node (n + 1)) = piece (n + 1) (node (n + 1)))
    (hdmatch : ∀ n, dpiece n (node (n + 1)) = dpiece (n + 1) (node (n + 1)))
    (hd : ∀ n x, x ∈ Icc (node n) (node (n + 1)) →
      HasDerivWithinAt (piece n) (dpiece n x) (Icc (node n) (node (n + 1))) x) :
    ∀ x ∈ Ioo (node 0) endpoint,
      HasDerivAt (morseOutwardGlue node piece) (morseOutwardGlue node dpiece x) x := by
  have hwithin (n : ℕ) (x : ℝ) (hx : x ∈ Icc (node n) (node (n + 1))) :
      HasDerivWithinAt (morseOutwardGlue node piece)
        (morseOutwardGlue node dpiece x) (Icc (node n) (node (n + 1))) x := by
    have heq : morseOutwardGlue node piece =ᶠ[𝓝[Icc (node n) (node (n + 1))] x]
        piece n := by
      filter_upwards [self_mem_nhdsWithin] with y hy
      exact morseOutwardGlue_apply_closed hmono hmatch hy
    have h := (hd n x hx).congr_of_eventuallyEq heq
      (morseOutwardGlue_apply_closed hmono hmatch hx)
    exact h.congr_deriv (morseOutwardGlue_apply_closed hmono hdmatch hx).symm
  intro x hx
  obtain ⟨n, hn⟩ := morse_outward_block_exists hlim hx.1.le hx.2
  rcases eq_or_lt_of_le hn.1 with heq | hlt
  · subst x
    cases n with
    | zero => exact (lt_irrefl _ hx.1).elim
    | succ n =>
      have hleft : node n < node (n + 1) := hmono (Nat.lt_succ_self n)
      have hright : node (n + 1) < node (n + 1 + 1) :=
        hmono (Nat.lt_succ_self (n + 1))
      have hL := hwithin n (node (n + 1)) ⟨hleft.le, le_rfl⟩
      have hR := hwithin (n + 1) (node (n + 1)) ⟨le_rfl, hright.le⟩
      apply (hL.union hR).hasDerivAt
      rw [Icc_union_Icc_eq_Icc hleft.le hright.le]
      exact Icc_mem_nhds hleft hright
  · exact (hwithin n x ⟨hn.1, hn.2.le⟩).hasDerivAt (Icc_mem_nhds hlt hn.2)

/-- A smooth positive density makes every actual first-order height/flux
solution smooth.  The argument raises finite orders simultaneously. -/
theorem contDiffOn_of_tailFluxSystem {p u q : ℝ → ℝ} {Λ : ℝ} {s : Set ℝ}
    (hs : IsOpen s) (hp : ContDiffOn ℝ ∞ p s) (hp₀ : ∀ x ∈ s, p x ≠ 0)
    (huD : ∀ x ∈ s, HasDerivAt u (q x / p x) x)
    (hqD : ∀ x ∈ s, HasDerivAt q (-(Λ * p x * u x)) x) :
    ContDiffOn ℝ ∞ u s ∧ ContDiffOn ℝ ∞ q s := by
  have hud : DifferentiableOn ℝ u s :=
    fun x hx => (huD x hx).differentiableAt.differentiableWithinAt
  have hqd : DifferentiableOn ℝ q s :=
    fun x hx => (hqD x hx).differentiableAt.differentiableWithinAt
  have hfinite : ∀ n : ℕ, ContDiffOn ℝ n u s ∧ ContDiffOn ℝ n q s := by
    intro n
    induction n with
    | zero => exact ⟨contDiffOn_zero.mpr hud.continuousOn, contDiffOn_zero.mpr hqd.continuousOn⟩
    | succ n ih =>
      have hpn : ContDiffOn ℝ n p s := hp.of_le (by simp)
      have hdu : ContDiffOn ℝ n (deriv u) s :=
        (ih.2.div hpn hp₀).congr (fun x hx => (huD x hx).deriv)
      have hdq : ContDiffOn ℝ n (deriv q) s :=
        ((contDiffOn_const.mul hpn).mul ih.1).neg.congr (fun x hx => (hqD x hx).deriv)
      have hsu : ContDiffOn ℝ ((n : ℕ∞ω) + 1) u s :=
        (contDiffOn_succ_iff_deriv_of_isOpen hs).mpr ⟨hud, by simp, hdu⟩
      have hsq : ContDiffOn ℝ ((n : ℕ∞ω) + 1) q s :=
        (contDiffOn_succ_iff_deriv_of_isOpen hs).mpr ⟨hqd, by simp, hdq⟩
      exact ⟨by simpa only [Nat.cast_add, Nat.cast_one] using hsu,
        by simpa only [Nat.cast_add, Nat.cast_one] using hsq⟩
  exact ⟨contDiffOn_infty.mpr (fun n => (hfinite n).1),
    contDiffOn_infty.mpr (fun n => (hfinite n).2)⟩

/-- Matching the actual weighted endpoint fluxes produces a smooth solution
on the open tail.  The first piece is used only for the inward continuation;
no equation outside the actual edges is imposed on that continuation. -/
theorem smooth_morseOutwardGlue_of_fluxMatch
    {node : ℕ → ℝ} {endpoint Λ : ℝ} {p : ℝ → ℝ} {piece : ℕ → ℝ → ℝ}
    (hmono : StrictMono node) (hlim : Tendsto node atTop (𝓝 endpoint))
    (hp : ContDiffOn ℝ ∞ p (Ico (node 0) endpoint))
    (hp_pos : ∀ x ∈ Ico (node 0) endpoint, 0 < p x)
    (hpiece : ∀ n, Differentiable ℝ (piece n))
    (hdpiece : ∀ n, Continuous (deriv (piece n)))
    (hode : ∀ n x, x ∈ Ioo (node n) (node (n + 1)) →
      HasDerivAt (fun y => p y * deriv (piece n) y) (-(Λ * p x * piece n x)) x)
    (hmatch : ∀ n, piece n (node (n + 1)) = piece (n + 1) (node (n + 1)))
    (hflux : ∀ n,
      p (node (n + 1)) * deriv (piece n) (node (n + 1)) =
        p (node (n + 1)) * deriv (piece (n + 1)) (node (n + 1))) :
    let u : ℝ → ℝ := morseOutwardGlue node piece
    ContDiffOn ℝ ∞ u (Ioo (node 0) endpoint) ∧
      (∀ x ∈ Ioo (node 0) endpoint,
        deriv (fun y => p y * deriv u y) x + Λ * p x * u x = 0) ∧
      (∀ n x, x ∈ Icc (node n) (node (n + 1)) → u x = piece n x) ∧
      (∀ n, ContinuousOn u (Icc (node n) (node (n + 1)))) ∧
      (∀ n x, x ∈ Icc (node n) (node (n + 1)) → node 0 < x →
        deriv u x = deriv (piece n) x) := by
  let U : ℝ → ℝ := morseOutwardGlue node piece
  let dU : ℝ → ℝ := morseOutwardGlue node (fun n => deriv (piece n))
  let Q : ℝ → ℝ := morseOutwardGlue node (fun n x => p x * deriv (piece n) x)
  have hnode (n : ℕ) : node n < endpoint := by
    have hle : node (n + 1) ≤ endpoint := by
      apply ge_of_tendsto hlim
      filter_upwards [eventually_ge_atTop (n + 1)] with k hk
      exact hmono.monotone hk
    exact (hmono (Nat.lt_succ_self n)).trans_le hle
  have hsub (n : ℕ) : Icc (node n) (node (n + 1)) ⊆ Ico (node 0) endpoint := by
    intro x hx
    exact ⟨(hmono.monotone (Nat.zero_le n)).trans hx.1, hx.2.trans_lt (hnode (n + 1))⟩
  have hpc (n : ℕ) : ContinuousOn p (Icc (node n) (node (n + 1))) :=
    hp.continuousOn.mono (hsub n)
  have hdmatch (n : ℕ) :
      deriv (piece n) (node (n + 1)) = deriv (piece (n + 1)) (node (n + 1)) :=
    mul_left_cancel₀
      (hp_pos _ (hsub n ⟨(hmono (Nat.lt_succ_self n)).le, le_rfl⟩)).ne' (hflux n)
  have huD₀ : ∀ x ∈ Ioo (node 0) endpoint, HasDerivAt U (dU x) x :=
    hasDerivAt_morseOutwardGlue hmono hlim hmatch hdmatch
      (fun n x _ => (hpiece n x).hasDerivAt.hasDerivWithinAt)
  have hforceMatch (n : ℕ) :
      -(Λ * p (node (n + 1)) * piece n (node (n + 1))) =
        -(Λ * p (node (n + 1)) * piece (n + 1) (node (n + 1))) := by
    rw [hmatch n]
  have hQwithin : ∀ n x, x ∈ Icc (node n) (node (n + 1)) →
      HasDerivWithinAt (fun y => p y * deriv (piece n) y)
        (-(Λ * p x * piece n x)) (Icc (node n) (node (n + 1))) x := by
    intro n
    exact hasDerivWithinAt_Icc_of_continuous_derivative (hmono (Nat.lt_succ_self n))
      ((hpc n).mul (hdpiece n).continuousOn)
      (((continuousOn_const.mul (hpc n)).mul (hpiece n).continuous.continuousOn).neg)
      (hode n)
  have hQD₀ := hasDerivAt_morseOutwardGlue
    (piece := fun n x => p x * deriv (piece n) x)
    (dpiece := fun n x => -(Λ * p x * piece n x))
    hmono hlim hflux hforceMatch hQwithin
  have hQeq (x : ℝ) (hx : x ∈ Ioo (node 0) endpoint) : Q x = p x * dU x := by
    obtain ⟨n, hn⟩ := morse_outward_block_exists hlim hx.1.le hx.2
    dsimp only [Q, dU]
    rw [morseOutwardGlue_apply_block hmono hn, morseOutwardGlue_apply_block hmono hn]
  have huD : ∀ x ∈ Ioo (node 0) endpoint, HasDerivAt U (Q x / p x) x := by
    intro x hx
    apply (huD₀ x hx).congr_deriv
    rw [hQeq x hx]
    field_simp [(hp_pos x ⟨hx.1.le, hx.2⟩).ne'] <;> ring
  have hQD : ∀ x ∈ Ioo (node 0) endpoint, HasDerivAt Q (-(Λ * p x * U x)) x := by
    intro x hx
    obtain ⟨n, hn⟩ := morse_outward_block_exists hlim hx.1.le hx.2
    apply (hQD₀ x hx).congr_deriv
    rw [morseOutwardGlue_apply_block hmono hn]
    dsimp only [U]
    rw [morseOutwardGlue_apply_block hmono hn]
  have hsmooth := contDiffOn_of_tailFluxSystem isOpen_Ioo
    (hp.mono Ioo_subset_Ico_self) (fun x hx => (hp_pos x (Ioo_subset_Ico_self hx)).ne') huD hQD
  refine ⟨hsmooth.1, ?_, ?_, ?_, ?_⟩
  · intro x hx
    have hgerm : (fun y => p y * deriv U y) =ᶠ[𝓝 x] Q := by
      filter_upwards [Ioo_mem_nhds hx.1 hx.2] with y hy
      rw [(huD₀ y hy).deriv]
      exact (hQeq y hy).symm
    rw [hgerm.deriv_eq, (hQD x hx).deriv]
    ring
  · intro n x hx
    exact morseOutwardGlue_apply_closed hmono hmatch hx
  · intro n
    exact (hpiece n).continuous.continuousOn.congr
      (fun x hx => morseOutwardGlue_apply_closed hmono hmatch hx)
  · intro n x hx hx₀
    exact (huD₀ x ⟨hx₀, (hsub n hx).2⟩).deriv.trans
      (morseOutwardGlue_apply_closed hmono hdmatch hx)

/-- The Poisson pieces use their existing interpolation definition.  The
sole coupling condition is equality of the two actual fluxes at each node. -/
theorem smooth_tailPoissonInterpolation
    {node : ℕ → ℝ} {endpoint Λ η : ℝ} {p : ℝ → ℝ}
    (hmono : StrictMono node) (hlim : Tendsto node atTop (𝓝 endpoint))
    (hp : ContDiffOn ℝ ∞ p (Ico (node 0) endpoint))
    (hp_pos : ∀ x ∈ Ico (node 0) endpoint, 0 < p x)
    (B : ∀ n, TailPhysicalPoissonData p (node n) (node (n + 1)) Λ η
      (hmono (Nat.lt_succ_self n)).le)
    (A : ℕ → ℝ)
    (hflux : ∀ n,
      p (node (n + 1)) * deriv ((B n).interpolate (A n) (A (n + 1))) (node (n + 1)) =
        p (node (n + 1)) *
          deriv ((B (n + 1)).interpolate (A (n + 1)) (A (n + 1 + 1))) (node (n + 1))) :
    let piece : ℕ → ℝ → ℝ := fun n => (B n).interpolate (A n) (A (n + 1))
    let u : ℝ → ℝ := morseOutwardGlue node piece
    ContDiffOn ℝ ∞ u (Ioo (node 0) endpoint) ∧
      (∀ x ∈ Ioo (node 0) endpoint,
        deriv (fun y => p y * deriv u y) x + Λ * p x * u x = 0) ∧
      (∀ n x, x ∈ Icc (node n) (node (n + 1)) → u x = piece n x) ∧
      (∀ n, ContinuousOn u (Icc (node n) (node (n + 1)))) ∧
      (∀ n x, x ∈ Icc (node n) (node (n + 1)) → node 0 < x →
        deriv u x = deriv (piece n) x) :=
  smooth_morseOutwardGlue_of_fluxMatch hmono hlim hp hp_pos
    (fun n => (B n).interpolate_differentiable (A n) (A (n + 1)))
    (fun n => (B n).interpolate_derivative_continuous (A n) (A (n + 1)))
    (fun n _ hx => (B n).interpolate_equation (A n) (A (n + 1)) hx)
    (fun n => ((B n).interpolate_right (A n) (A (n + 1))).trans
      ((B (n + 1)).interpolate_left (A (n + 1)) (A (n + 1 + 1))).symm)
    hflux

end ContinuousFlexibility.Radial
