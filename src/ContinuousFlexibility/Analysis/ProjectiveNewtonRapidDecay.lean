module

public import ContinuousFlexibility.Analysis.ProjectiveNewtonSeed

/-!
# Improving the Newton residual decay on a fixed parameter interval

At a higher finite grade the state may grow, but its growth is measured at
the next smoothing index. The resulting gain in the tail exponent improves
the low residual bound. A new finite-grade constant can require discarding a
finite prefix, which is absorbed by the coefficient of the improved rate.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter
open scoped Topology

set_option backward.isDefEq.respectTransparency false

theorem newtonSmoothingIndex_monotone (N₀ : ℕ) : Monotone (newtonSmoothingIndex N₀) := by
  apply monotone_nat_of_le_succ
  intro n
  have hN : (0 : ℝ) ≤ newtonSmoothingIndex N₀ n := Nat.cast_nonneg _
  have h₁ : (newtonSmoothingIndex N₀ n : ℝ) ≤
      (3 / 2 : ℝ) * newtonSmoothingIndex N₀ n := by linarith only [hN]
  exact_mod_cast h₁.trans (newtonSmoothingIndex_succ_bounds N₀ n).1

theorem tendsto_newtonSmoothingIndex_atTop {N₀ : ℕ} (hN₀ : 0 < N₀) :
    Tendsto (newtonSmoothingIndex N₀) atTop atTop := by
  apply tendsto_atTop.2
  intro m
  filter_upwards [eventually_ge_atTop m] with n hn
  exact (hn.trans (Nat.le_add_left n N₀)).trans (newtonSmoothingIndex_ge_add hN₀ n)

/-- Control the high state at the next scale by the low residual decay.
The high correction bound only uses the forward smoothing estimate. -/
theorem newton_high_grade_budget
    {N₀ : ℕ} (hN₀ : 0 < N₀) (r x : ℕ → ℝ)
    {K ρ M α γ G : ℝ} (hK : 0 ≤ K) (hM : 0 ≤ M) (hγ : 2 ≤ γ)
    (hcoef : K * ρ ≤ M / 2) (hG : G - α = (3 / 2 : ℝ) * γ)
    (hinit : x 0 ≤ M * Real.exp (γ * N₀))
    (hr : ∀ n, r n ≤ ρ * Real.exp (-α * newtonSmoothingIndex N₀ n))
    (hstep : ∀ n, x (n + 1) ≤ x n + K * Real.exp (G * newtonSmoothingIndex N₀ n) * r n) :
    ∀ n, x n ≤ M * Real.exp (γ * newtonSmoothingIndex N₀ n) := by
  intro n
  induction n with
  | zero => exact hinit
  | succ n ih =>
    let N := newtonSmoothingIndex N₀ n
    let Nnext := newtonSmoothingIndex N₀ (n + 1)
    have hNnat : 1 ≤ N := by
      have h := newtonSmoothingIndex_ge_add hN₀ n
      omega
    have hN : (1 : ℝ) ≤ N := by exact_mod_cast hNnat
    have hhalf : 1 ≤ γ / 2 := by linarith only [hγ]
    have hγ₀ : 0 ≤ γ := by linarith only [hγ]
    have hprod : 1 ≤ γ / 2 * N := by
      simpa only [one_mul] using mul_le_mul hhalf hN zero_le_one (by linarith only [hhalf])
    have htwo : (2 : ℝ) ≤ Real.exp (γ / 2 * N) :=
      (by linarith only [hprod] : (2 : ℝ) ≤ γ / 2 * N + 1).trans (Real.add_one_le_exp _)
    have hsmall : Real.exp (γ * N) ≤ Real.exp ((3 / 2 : ℝ) * γ * N) / 2 := by
      have h := mul_le_mul_of_nonneg_right htwo (Real.exp_pos (γ * N)).le
      rw [← Real.exp_add, show γ / 2 * N + γ * N = (3 / 2 : ℝ) * γ * N by ring] at h
      linarith only [h]
    have hcorr : K * Real.exp (G * N) * (ρ * Real.exp (-α * N)) =
        K * ρ * Real.exp ((3 / 2 : ℝ) * γ * N) := by
      calc
        _ = K * ρ * (Real.exp (G * N) * Real.exp (-α * N)) := by ring
        _ = _ := by rw [← Real.exp_add, show G * N + -α * N = (G - α) * N by ring, hG]
    have hscale : Real.exp ((3 / 2 : ℝ) * γ * N) ≤ Real.exp (γ * Nnext) := by
      apply Real.exp_le_exp.mpr
      rw [show (3 / 2 : ℝ) * γ * N = γ * ((3 / 2 : ℝ) * N) by ring]
      exact mul_le_mul_of_nonneg_left (newtonSmoothingIndex_succ_bounds N₀ n).1 hγ₀
    calc
      _ ≤ M * Real.exp (γ * N) + K * Real.exp (G * N) * (ρ * Real.exp (-α * N)) :=
        (hstep n).trans (add_le_add ih
          (mul_le_mul_of_nonneg_left (hr n) (mul_nonneg hK (Real.exp_pos _).le)))
      _ ≤ M * (Real.exp ((3 / 2 : ℝ) * γ * N) / 2) +
          (M / 2) * Real.exp ((3 / 2 : ℝ) * γ * N) := by
        rw [hcorr]
        exact add_le_add (mul_le_mul_of_nonneg_left hsmall hM)
          (mul_le_mul_of_nonneg_right hcoef (Real.exp_pos _).le)
      _ = M * Real.exp ((3 / 2 : ℝ) * γ * N) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hscale hM

/-- A recurrence valid after a finite index still improves the decay on the
whole fixed parameter set. Only the new coefficient absorbs the prefix. -/
theorem exists_newton_residual_constant_of_eventual_recurrence
    {T : Type*} (I : Set T) (r x : ℕ → T → ℝ) (N₀ n₀ : ℕ)
    {α γ A β C M ρ : ℝ} (hC : 0 ≤ C) (hM : 0 ≤ M)
    (hA : 0 ≤ 2 * α - A) (hβ : 2 * α - A ≤ β - γ)
    (hr₀ : ∀ n τ, τ ∈ I → 0 ≤ r n τ ∧ r n τ ≤ 1)
    (hr : ∀ n τ, τ ∈ I → r n τ ≤ ρ * Real.exp (-α * newtonSmoothingIndex N₀ n))
    (hx : ∀ n τ, τ ∈ I → x n τ ≤ M * Real.exp (γ * newtonSmoothingIndex N₀ n))
    (hrec : ∀ n ≥ n₀, ∀ τ ∈ I,
      r (n + 1) τ ≤ C * (Real.exp (A * newtonSmoothingIndex N₀ n) * (r n τ) ^ 2 +
        Real.exp (-β * newtonSmoothingIndex N₀ n) * x n τ)) :
    let α' := (2 * α - A) / (3 / 2)
    ∃ C' : ℝ, 0 ≤ C' ∧
      ∀ n τ, τ ∈ I → r n τ ≤ C' * Real.exp (-α' * newtonSmoothingIndex N₀ n) := by
  let N := newtonSmoothingIndex N₀
  let α' := (2 * α - A) / (3 / 2)
  have hα' : 0 ≤ α' := div_nonneg hA (by norm_num)
  let D₀ := Real.exp (α' * N n₀)
  let D₁ := C * (ρ ^ 2 + M) * Real.exp α'
  have hD₀ : 0 ≤ D₀ := (Real.exp_pos _).le
  have hD₁ : 0 ≤ D₁ :=
    mul_nonneg (mul_nonneg hC (add_nonneg (sq_nonneg _) hM)) (Real.exp_pos _).le
  refine ⟨D₀ + D₁, add_nonneg hD₀ hD₁, ?_⟩
  intro n τ hτ
  by_cases hn : n ≤ n₀
  · have hN : (N n : ℝ) ≤ N n₀ := by exact_mod_cast newtonSmoothingIndex_monotone N₀ hn
    have hone : (1 : ℝ) ≤ D₀ * Real.exp (-α' * N n) := by
      dsimp only [D₀]
      rw [← Real.exp_add]
      apply Real.one_le_exp
      have hpos := mul_nonneg hα' (sub_nonneg.mpr hN)
      linarith only [hpos]
    exact ((hr₀ n τ hτ).2.trans hone).trans
      (mul_le_mul_of_nonneg_right (le_add_of_nonneg_right hD₁) (Real.exp_pos _).le)
  · cases n with
    | zero => exact (hn (Nat.zero_le _)).elim
    | succ k =>
      have hk : n₀ ≤ k := Nat.lt_succ_iff.mp (lt_of_not_ge hn)
      have hnext := newton_residual_rate_improvement hC hM (hr₀ k τ hτ).1 hA hβ
        (newtonSmoothingIndex_succ_bounds N₀ k).2 (hx k τ hτ) (hr k τ hτ) (hrec k hk τ hτ)
      exact hnext.trans
        (mul_le_mul_of_nonneg_right (le_add_of_nonneg_left hD₀) (Real.exp_pos _).le)

theorem newton_summable_exponential
    {N₀ : ℕ} (hN₀ : 0 < N₀) {δ : ℝ} (hδ : 0 < δ) :
    Summable (fun n : ℕ => Real.exp (-δ * (newtonSmoothingIndex N₀ n : ℝ))) := by
  apply Real.summable_exp_nat_mul_of_ge (neg_lt_zero.mpr hδ)
  intro n
  exact_mod_cast (Nat.le_add_left n N₀).trans (newtonSmoothingIndex_ge_add hN₀ n)

private theorem rapid_pairGrading_apply
    {X : Type*} [AddCommGroup X] [Module ℝ X]
    (p : ℕ → Seminorm ℝ X) (s : ℕ) (z : X × ℝ) :
    Statements.pairGrading p Statements.realGrading s z = p s z.1 + |z.2| := by
  change p s z.1 + ‖z.2‖ = p s z.1 + |z.2|
  rw [Real.norm_eq_abs]

private theorem rapid_state_size_step_le
    {X : Type*} [AddCommGroup X] [Module ℝ X]
    (p : ℕ → Seminorm ℝ X) (s : ℕ) (z : X × ℝ) (d : X) :
    1 + Statements.pairGrading p Statements.realGrading s (z.1 - d, z.2) ≤
      1 + Statements.pairGrading p Statements.realGrading s z + p s d := by
  simp only [rapid_pairGrading_apply]
  calc
    _ ≤ 1 + ((p s z.1 + p s d) + |z.2|) :=
      add_le_add le_rfl (add_le_add (map_sub_le_add (p s) _ _) le_rfl)
    _ = _ := by ring

/-- The same seeded iterates have arbitrarily fast residual and correction
decay. The higher grade and its constants may change with the requested rate;
the parameter interval, the smoothing families, and the indices stay fixed. -/
theorem projectiveNewton_rapid_decay_of_seed
    {X : Type*} [TopologicalSpace X] [AddCommGroup X] [Module ℝ X]
    [IsTopologicalAddGroup X] [ContinuousSMul ℝ X]
    {F : ℕ → Type*} [∀ n, NormedAddCommGroup (F n)] [∀ n, NormedSpace ℝ (F n)]
    {bond : ∀ n, F (n + 1) →L[ℝ] F n}
    (p : ℕ → Seminorm ℝ X) (hp : Monotone p) (x₀ : X)
    (b₀ b l σ N₀ : ℕ) (hb₀ : b₀ ≤ b) (hN₀ : 0 < N₀)
    (ε₀ ε μ q₀ : ℝ) (hμ : 0 < μ) (hμ₀ : 4 * μ ≤ ε₀) (hμε : 4 * μ ≤ ε)
    (hμ₁ : 4 * μ ≤ 1) (hqμ : q₀ ≤ μ)
    {U : Set (X × ℝ)} (hU : U = {z | p b₀ (z.1 - x₀) < ε₀ ∧ |z.2| < ε₀})
    (R : X × ℝ → ProjectiveLimit F bond)
    (V : X × ℝ → ProjectiveLimit F bond →ₗ[ℝ] X)
    (Q : X × ℝ → ProjectiveLimit F bond →ₗ[ℝ] ProjectiveLimit F bond →ₗ[ℝ] ProjectiveLimit F bond)
    (J : Statements.SmoothDirections U R)
    (hV : ∀ z ∈ U, ∀ y, HasProjectiveLineDerivAt (fun x => R (x, z.2))
      (y + Q z (R z) y) z.1 (V z y))
    (SX : ℕ → X →L[ℝ] X) (SY : ℕ → ProjectiveLimit F bond →L[ℝ] ProjectiveLimit F bond) :
    let a := Statements.pairGrading p Statements.realGrading
    let q := gradedSeminorm F bond
    let B := b + l
    let A := B + l
    let N := newtonSmoothingIndex N₀
    let z := fun n τ => projectiveSmoothedNewtonIterates R V SX N (x₀, τ) n
    let u := fun n τ => V (z n τ) (R (z n τ))
    let r := fun n τ => q B (R (z n τ))
    let α₀ : ℝ := 4 * (l : ℝ) + 4 * (σ : ℝ) + 2
    (∀ s : ℕ, b ≤ s → ∃ C : ℝ, 0 ≤ C ∧ ∀ w ∈ U, a b (w - (x₀, 0)) < ε →
      (q s (R w) ≤ C * (1 + a (s + l) w)) ∧
      (∀ d : X × ℝ,
        (q s (projectiveJetHeadLinear J.D 0 w Fin.elim0 d) ≤
          C * ((1 + a (s + l) w) * a b d + a (s + l) d)) ∧
        (q s (J.D 2 w (Fin.cons d (Fin.cons d Fin.elim0))) ≤
          C * ((1 + a (s + l) w) * (a b d) ^ 2 + 2 * (a (s + l) d * a b d)))) ∧
      (∀ y, p s (V w y) ≤ C * (q (s + l) y + (1 + a (s + l) w) * q b y)) ∧
      (∀ v y, q s (Q w v y) ≤ C * ((1 + a (s + l) w) * (q b v * q b y) +
        (q (s + l) v * q b y + q b v * q (s + l) y)))) →
    (∀ h : ℕ, 2 * l ≤ h → ∃ Kₛ : ℝ, 0 ≤ Kₛ ∧
      ∀ (i : ℕ) (d : X) (v : ProjectiveLimit F bond),
        let G := b + h
        let H := b + h + 2 * l
        let β : ℝ := (h : ℝ) - 2 * (l : ℝ) - σ
        (p b (SX i d) ≤ Kₛ * Real.exp ((σ : ℝ) * i) * p b d ∧
          p A (SX i d) ≤ Kₛ * Real.exp ((2 * (l : ℝ) + σ) * i) * p b d ∧
          p H (SX i d) ≤ Kₛ * Real.exp (((h : ℝ) + 2 * (l : ℝ) + σ) * i) * p b d ∧
          p b (d - SX i d) ≤ Kₛ * Real.exp (-β * i) * p G d ∧
          p A (d - SX i d) ≤ Kₛ * Real.exp (-β * i) * p G d) ∧
        (q A (SY i v) ≤ Kₛ * Real.exp (((l : ℝ) + σ) * i) * q B v ∧
          q A (v - SY i v) ≤ Kₛ * Real.exp (-β * i) * q G v)) →
    (∀ τ : ℝ, |τ| < q₀ → ∀ n : ℕ,
      z n τ ∈ U ∧ p A ((z n τ).1 - x₀) < μ ∧ a b (z n τ - (x₀, 0)) < ε ∧
        1 + a A (z n τ) ≤ 2 + p A x₀ ∧ r n τ ≤ Real.exp (-α₀ * N n)) →
    (∀ δ : ℝ, ∃ C : ℝ, 0 ≤ C ∧ ∀ n τ, |τ| < q₀ → r n τ ≤ C * Real.exp (-δ * N n)) ∧
    (∀ s : ℕ, ∀ δ : ℝ, ∃ C : ℝ, 0 ≤ C ∧ ∀ n τ, |τ| < q₀ →
      p s (SX (N n) (u n τ)) ≤ C * Real.exp (-δ * N n)) := by
  subst U
  dsimp only
  intro hBounds hSmooth hSeed
  let U : Set (X × ℝ) := {w | p b₀ (w.1 - x₀) < ε₀ ∧ |w.2| < ε₀}
  let I : Set ℝ := {τ | |τ| < q₀}
  let a := Statements.pairGrading p Statements.realGrading
  let q := gradedSeminorm F bond
  let B := b + l
  let A := B + l
  let N := newtonSmoothingIndex N₀
  let z := fun n τ => projectiveSmoothedNewtonIterates R V SX N (x₀, τ) n
  let u := fun n τ => V (z n τ) (R (z n τ))
  let r := fun n τ => q B (R (z n τ))
  let α₀ : ℝ := 4 * (l : ℝ) + 4 * (σ : ℝ) + 2
  let aQuad : ℝ := 2 * (l : ℝ) + 2 * (σ : ℝ)
  let Mlow := 2 + p A x₀
  have hbB : b ≤ B := Nat.le_add_right _ _
  have hbA : b ≤ A := hbB.trans (Nat.le_add_right _ _)
  have ha : Monotone a := pairGrading_monotone hp monotone_const
  have hq : Monotone q := gradedSeminorm_monotone F bond
  have hMlow : 0 ≤ Mlow := add_nonneg (by norm_num) (apply_nonneg _ _)
  have hl₀ : (0 : ℝ) ≤ l := Nat.cast_nonneg l
  have hσ₀ : (0 : ℝ) ≤ σ := Nat.cast_nonneg σ
  have hα₀ : 0 ≤ α₀ := by dsimp only [α₀]; positivity
  have hα₀' : 2 * aQuad < α₀ := by dsimp only [aQuad, α₀]; linarith
  have hσα₀ : (σ : ℝ) < α₀ := by dsimp only [α₀]; linarith only [hl₀, hσ₀]
  have hparam (n : ℕ) (τ : ℝ) (hτ : τ ∈ I) : |(z n τ).2| < μ := by
    rw [show (z n τ).2 = τ from projectiveSmoothedNewtonIterates_parameter R V SX N (x₀, τ) n]
    exact (show |τ| < q₀ from hτ).trans_le hqμ
  have hr₀ (n : ℕ) (τ : ℝ) (_hτ : τ ∈ I) : 0 ≤ r n τ := apply_nonneg _ _
  have hr₁ (n : ℕ) (τ : ℝ) (hτ : τ ∈ I) : r n τ ≤ 1 := by
    have hr := (hSeed τ hτ n).2.2.2.2
    refine hr.trans ?_
    rw [← Real.exp_zero]
    exact Real.exp_le_exp.mpr (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hα₀) (Nat.cast_nonneg _))
  obtain ⟨Cb, hCb, Hb⟩ := hBounds b le_rfl
  obtain ⟨C, hC, HB⟩ := hBounds B hbB
  have himprove (α : ℝ) (hα : 0 ≤ α) (hαA : 0 ≤ 2 * α - aQuad)
      (ρ : ℝ) (hρ : 0 ≤ ρ) (hrate : ∀ n τ, τ ∈ I → r n τ ≤ ρ * Real.exp (-α * N n)) :
      ∃ D : ℝ, 0 ≤ D ∧ ∀ n τ, τ ∈ I →
        r n τ ≤ D * Real.exp (-((2 * α - aQuad) / (3 / 2)) * N n) := by
    obtain ⟨h, hh, hγ, hGexp, htail⟩ := exists_newton_high_grade_for_rate l σ hα
    let G := b + h
    let H := b + h + 2 * l
    let Gexp : ℝ := (h : ℝ) + 2 * (l : ℝ) + σ
    let γ : ℝ := (Gexp - α) / (3 / 2)
    let β : ℝ := (h : ℝ) - 2 * (l : ℝ) - σ
    let size := fun n τ => 1 + a H (z n τ)
    have hbG : b ≤ G := Nat.le_add_right _ _
    obtain ⟨Cg, hCg, Hg⟩ := hBounds G hbG
    obtain ⟨Ch, hCh, Hh⟩ := hBounds (G + l) (hbG.trans (Nat.le_add_right _ _))
    let Cv := Cb + Cg + Ch
    have hCv : 0 ≤ Cv := add_nonneg (add_nonneg hCb hCg) hCh
    have hCb' : Cb ≤ Cv := by dsimp only [Cv]; linarith only [hCg, hCh]
    have hCg' : Cg ≤ Cv := by dsimp only [Cv]; linarith only [hCb, hCh]
    have hCh' : Ch ≤ Cv := by dsimp only [Cv]; linarith only [hCb, hCg]
    let Kᵥ := 1 + Cv + Cv * (Mlow + 1) + Cv * (Cv + 1)
    have hKv₁ : 1 ≤ Kᵥ := by
      dsimp only [Kᵥ]
      linarith only [hCv, mul_nonneg hCv (add_nonneg hMlow zero_le_one),
        mul_nonneg hCv (add_nonneg hCv zero_le_one)]
    obtain ⟨Kₛ, hKₛ, hSh⟩ := hSmooth h hh
    let K := Kₛ * Kᵥ
    have hK : 0 ≤ K := mul_nonneg hKₛ (zero_le_one.trans hKv₁)
    let Crec := (C * (Mlow + 2 * K) + C * (Mlow + 3) * K ^ 2 / 2) + C * (Mlow + 3) * K
    have hCrec : 0 ≤ Crec := by dsimp only [Crec]; positivity
    have hcor (n : ℕ) (τ : ℝ) (hτ : τ ∈ I) :
        p b (u n τ) ≤ Kᵥ * r n τ ∧ p G (u n τ) ≤ Kᵥ * size n τ ∧
          q G (R (z n τ)) ≤ Kᵥ * size n τ := by
      let w := z n τ
      obtain ⟨hw, _, hwnear, hwsize, _⟩ := hSeed τ hτ n
      have hpos (s : ℕ) : 0 ≤ 1 + a s w := add_nonneg zero_le_one (apply_nonneg _ _)
      have hbr (s : ℕ) : 0 ≤ q (s + l) (R w) + (1 + a (s + l) w) * q b (R w) :=
        add_nonneg (apply_nonneg _ _) (mul_nonneg (hpos _) (apply_nonneg _ _))
      have hbnd := ((Hb w hw hwnear).2.2.1 (R w)).trans (mul_le_mul_of_nonneg_right hCb' (hbr b))
      have hgnd := ((Hg w hw hwnear).2.2.1 (R w)).trans (mul_le_mul_of_nonneg_right hCg' (hbr G))
      have hH : G + l + l = H := by dsimp only [G, H]; omega
      have hR : q (G + l) (R w) ≤ Cv * (1 + a H w) := by
        rw [← hH]
        exact ((Hh w hw hwnear).1).trans (mul_le_mul_of_nonneg_right hCh' (hpos _))
      exact (newton_correction_bounds_of_tame a p q ha hq w (u n τ) (R w) b l h Cv Mlow
        hCv hMlow hwsize (hr₁ n τ hτ) hbnd hgnd hR).2
    have hsize_step (n : ℕ) (τ : ℝ) (hτ : τ ∈ I) :
        size (n + 1) τ ≤ size n τ + K * Real.exp (Gexp * N n) * r n τ := by
      let d := SX (N n) (u n τ)
      have hd : p H d ≤ K * Real.exp (Gexp * N n) * r n τ := by
        have hforward := (hSh (N n) (u n τ) (R (z n τ))).1.2.2.1
        calc
          _ ≤ Kₛ * Real.exp (Gexp * N n) * (Kᵥ * r n τ) :=
            hforward.trans (mul_le_mul_of_nonneg_left (hcor n τ hτ).1
              (mul_nonneg hKₛ (Real.exp_pos _).le))
          _ = _ := by dsimp only [K]; ring
      exact (rapid_state_size_step_le p H (z n τ) d).trans (add_le_add le_rfl hd)
    let M := 2 + p H x₀ + 2 * K * ρ
    have hpH : 0 ≤ p H x₀ := apply_nonneg _ _
    have hKρ : 0 ≤ K * ρ := mul_nonneg hK hρ
    have hM : 0 ≤ M := by dsimp only [M]; linarith only [hpH, hKρ]
    have hcoef : K * ρ ≤ M / 2 := by dsimp only [M]; linarith only [hpH]
    have hγ₀ : 0 ≤ γ := by linarith only [show 2 ≤ γ from hγ]
    have hx (n : ℕ) (τ : ℝ) (hτ : τ ∈ I) : size n τ ≤ M * Real.exp (γ * N n) := by
      have hinit : size 0 τ ≤ M * Real.exp (γ * N₀) := by
        change 1 + a H (x₀, τ) ≤ _
        have hbound : 1 + a H (x₀, τ) ≤ M := by
          rw [show a H (x₀, τ) = p H x₀ + |τ| from rapid_pairGrading_apply p H (x₀, τ)]
          dsimp only [M]
          linarith only [(show |τ| < q₀ from hτ).trans_le hqμ, hμ₁, hKρ]
        exact hbound.trans (by
          simpa only [mul_one] using mul_le_mul_of_nonneg_left
            (Real.one_le_exp (mul_nonneg hγ₀ (Nat.cast_nonneg N₀))) hM)
      exact newton_high_grade_budget hN₀ (fun j => r j τ) (fun j => size j τ)
        hK hM hγ hcoef hGexp hinit (fun j => hrate j τ hτ) (fun j => hsize_step j τ hτ) n
    have hDlim : Tendsto (fun n : ℕ => K * Real.exp (-(α₀ - (σ : ℝ)) * N n)) atTop (𝓝 0) := by
      simpa only [mul_zero] using
        ((newton_summable_exponential hN₀ (sub_pos.mpr hσα₀)).tendsto_atTop_zero).const_mul K
    obtain ⟨n₀, hn₀⟩ := eventually_atTop.1 (hDlim.eventually_lt_const hμ)
    have hrec (n : ℕ) (hn : n₀ ≤ n) (τ : ℝ) (hτ : τ ∈ I) :
        r (n + 1) τ ≤ Crec * (Real.exp (aQuad * N n) * (r n τ) ^ 2 +
          Real.exp (-β * N n) * size n τ) := by
      let w := z n τ
      let Db := K * Real.exp ((σ : ℝ) * N n) * r n τ
      obtain ⟨hw, hdisp, hnear, hsize, hrseed⟩ := hSeed τ hτ n
      have hDb : Db < μ := by
        calc
          Db ≤ K * Real.exp ((σ : ℝ) * N n) * Real.exp (-α₀ * N n) :=
            mul_le_mul_of_nonneg_left hrseed (mul_nonneg hK (Real.exp_pos _).le)
          _ = K * (Real.exp ((σ : ℝ) * N n) * Real.exp (-α₀ * N n)) := mul_assoc _ _ _
          _ = K * Real.exp (-(α₀ - (σ : ℝ)) * N n) := by
            rw [← Real.exp_add, show (σ : ℝ) * N n + -α₀ * N n = -(α₀ - (σ : ℝ)) * N n by ring]
          _ < μ := hn₀ n hn
      have hτμ : |w.2| < μ := hparam n τ hτ
      have hτ₀ : |w.2| < ε₀ := by linarith only [hτμ, hμ, hμ₀]
      have hdisp_b : p b (w.1 - x₀) < μ := (hp hbA _).trans_lt hdisp
      have hrect : p b (w.1 - x₀) + Db < ε₀ := by linarith only [hdisp_b, hDb, hμ, hμ₀]
      have hcenter : a b (w - (x₀, 0)) = p b (w.1 - x₀) + |w.2| := by
        rw [show a b (w - (x₀, 0)) = _ from rapid_pairGrading_apply p b (w - (x₀, 0))]
        change p b (w.1 - x₀) + |w.2 - 0| = _
        rw [sub_zero]
      have hball : a b (w - (x₀, 0)) + Db < ε := by
        rw [hcenter]
        linarith only [hdisp_b, hτμ, hDb, hμ, hμε]
      have hDb₁ : Db ≤ 1 := by linarith only [hDb, hμ₁]
      obtain ⟨hvb, hvg, hrg⟩ := hcor n τ hτ
      have hQdiag : q B (Q w (R w) (R w)) ≤
          C * ((1 + a A w) * (q b (R w)) ^ 2 + 2 * (q A (R w) * q b (R w))) := by
        calc
          _ ≤ C * ((1 + a A w) * (q b (R w) * q b (R w)) +
              (q A (R w) * q b (R w) + q b (R w) * q A (R w))) :=
            (HB w hw hnear).2.2.2 (R w) (R w)
          _ = _ := by ring
      obtain ⟨_, _, _, _, hrnext⟩ := projectiveSmoothedNewtonStep_twoGradeRecurrence
        J p hp x₀ w b₀ b l h σ (N n) hb₀ ε₀ ε C Kₛ Kᵥ Mlow
        hC hKₛ hKv₁ hMlow Subset.rfl V Q (hV w hw) (SX (N n)) (SY (N n))
        (fun v hv hvnear => (HB v hv hvnear).2.1) hvb hvg hrg hQdiag
        (hSh (N n) (u n τ) (R w)).1 (hSh (N n) (u n τ) (R w)).2
        hτ₀ hrect hball hsize (hr₁ n τ hτ) hDb₁
      exact hrnext
    have htail' : 2 * α - aQuad + 1 ≤ β - γ := htail
    have hβ : 2 * α - aQuad ≤ β - γ := (le_add_of_nonneg_right zero_le_one).trans htail'
    exact exists_newton_residual_constant_of_eventual_recurrence I r size N₀ n₀
      hCrec hM hαA hβ (fun n τ hτ => ⟨hr₀ n τ hτ, hr₁ n τ hτ⟩) hrate hx hrec
  have hrate_ge (m : ℕ) : α₀ ≤ newtonImprovedRate aQuad α₀ m := by
    have hpw : (1 : ℝ) ≤ (4 / 3 : ℝ) ^ m := by
      simpa only [one_pow] using pow_le_pow_left₀ (show (0 : ℝ) ≤ 1 from zero_le_one)
        (show (1 : ℝ) ≤ 4 / 3 by norm_num) m
    have hmul := mul_le_mul_of_nonneg_right hpw (sub_nonneg.mpr hα₀'.le)
    dsimp only [newtonImprovedRate]
    linarith only [hmul]
  have hrate (m : ℕ) : ∃ ρ : ℝ, 0 ≤ ρ ∧ ∀ n τ, τ ∈ I →
      r n τ ≤ ρ * Real.exp (-newtonImprovedRate aQuad α₀ m * N n) := by
    induction m with
    | zero =>
      refine ⟨1, zero_le_one, ?_⟩
      intro n τ hτ
      simpa only [one_mul, newtonImprovedRate_zero] using (hSeed τ hτ n).2.2.2.2
    | succ m ih =>
      obtain ⟨ρ, hρ, hr⟩ := ih
      have hα : 0 ≤ newtonImprovedRate aQuad α₀ m := hα₀.trans (hrate_ge m)
      have hA₀ : 0 ≤ aQuad := by dsimp only [aQuad]; positivity
      have hαA : 0 ≤ 2 * newtonImprovedRate aQuad α₀ m - aQuad := by
        linarith only [hrate_ge m, hα₀', hA₀]
      obtain ⟨D, hD, hnext⟩ := himprove (newtonImprovedRate aQuad α₀ m) hα hαA ρ hρ hr
      refine ⟨D, hD, ?_⟩
      intro n τ hτ
      rw [newtonImprovedRate_succ]
      exact hnext n τ hτ
  have hrapid (δ : ℝ) : ∃ ρ : ℝ, 0 ≤ ρ ∧ ∀ n τ, τ ∈ I →
      r n τ ≤ ρ * Real.exp (-δ * N n) := by
    obtain ⟨m, hm⟩ := ((tendsto_atTop.1 (tendsto_newtonImprovedRate_atTop hα₀')) δ).exists
    obtain ⟨ρ, hρ, hr⟩ := hrate m
    refine ⟨ρ, hρ, ?_⟩
    intro n τ hτ
    exact (hr n τ hτ).trans (mul_le_mul_of_nonneg_left
      (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right (neg_le_neg hm) (Nat.cast_nonneg (N n)))) hρ)
  refine ⟨hrapid, ?_⟩
  intro s δ
  let h := s + 2 * l
  let H := b + h + 2 * l
  let Gexp : ℝ := (h : ℝ) + 2 * (l : ℝ) + σ
  have hh : 2 * l ≤ h := Nat.le_add_left _ _
  have hsH : s ≤ H := by dsimp only [H, h]; omega
  obtain ⟨Kₛ, hKₛ, hSh⟩ := hSmooth h hh
  obtain ⟨ρ, hρ, hr⟩ := hrapid (δ + Gexp)
  let Klow := Cb * (Mlow + 1)
  have hKlow : 0 ≤ Klow := mul_nonneg hCb (add_nonneg hMlow zero_le_one)
  let K := Kₛ * Klow
  have hK : 0 ≤ K := mul_nonneg hKₛ hKlow
  refine ⟨K * ρ, mul_nonneg hK hρ, ?_⟩
  intro n τ hτ
  let w := z n τ
  let d := SX (N n) (u n τ)
  obtain ⟨hw, _, hnear, hsize, _⟩ := hSeed τ hτ n
  have hB : 1 + a B w ≤ Mlow :=
    (add_le_add le_rfl (ha (Nat.le_add_right B l) w)).trans hsize
  have hqb : q b (R w) ≤ r n τ := hq hbB _
  have hlow : p b (u n τ) ≤ Klow * r n τ := by
    calc
      _ ≤ Cb * (r n τ + (1 + a B w) * q b (R w)) := (Hb w hw hnear).2.2.1 (R w)
      _ ≤ Cb * (r n τ + Mlow * r n τ) :=
        mul_le_mul_of_nonneg_left
          (add_le_add le_rfl (mul_le_mul hB hqb (apply_nonneg _ _) hMlow)) hCb
      _ = _ := by dsimp only [Klow]; ring
  have hforward := (hSh (N n) (u n τ) (R w)).1.2.2.1
  calc
    _ ≤ p H d := hp hsH d
    _ ≤ Kₛ * Real.exp (Gexp * N n) * (Klow * r n τ) :=
      hforward.trans (mul_le_mul_of_nonneg_left hlow (mul_nonneg hKₛ (Real.exp_pos _).le))
    _ = K * Real.exp (Gexp * N n) * r n τ := by dsimp only [K]; ring
    _ ≤ K * Real.exp (Gexp * N n) * (ρ * Real.exp (-(δ + Gexp) * N n)) :=
      mul_le_mul_of_nonneg_left (hr n τ hτ) (mul_nonneg hK (Real.exp_pos _).le)
    _ = (K * ρ) * (Real.exp (Gexp * N n) * Real.exp (-(δ + Gexp) * N n)) := by ring
    _ = _ := by
      rw [← Real.exp_add, show Gexp * N n + -(δ + Gexp) * N n = -δ * N n by ring]

/-- The actual increments have summable majorants in every source grade
on a single interval. A prescribed minimum base can include the separating
base of the residual grading. -/
theorem exists_projectiveNewton_summable_iterates
    {X : Type*} [TopologicalSpace X] [AddCommGroup X] [Module ℝ X] [T2Space X]
    [IsTopologicalAddGroup X] [ContinuousSMul ℝ X]
    {F : ℕ → Type*} [∀ n, NormedAddCommGroup (F n)] [∀ n, NormedSpace ℝ (F n)]
    {bond : ∀ n, F (n + 1) →L[ℝ] F n}
    (p : ℕ → Seminorm ℝ X) (hp : Monotone p) (x₀ : X)
    (b₀ bMin : ℕ) (ε₀ : ℝ) (hε₀ : 0 < ε₀)
    {U : Set (X × ℝ)} (hU : U = {z | p b₀ (z.1 - x₀) < ε₀ ∧ |z.2| < ε₀})
    (R : X × ℝ → ProjectiveLimit F bond)
    (V : X × ℝ → ProjectiveLimit F bond →ₗ[ℝ] X)
    (Q : X × ℝ → ProjectiveLimit F bond →ₗ[ℝ] ProjectiveLimit F bond →ₗ[ℝ] ProjectiveLimit F bond)
    (hzero : R (x₀, 0) = 0)
    (hRight : ∀ z ∈ U, ∀ y, HasProjectiveLineDerivAt (fun x => R (x, z.2))
      (y + Q z (R z) y) z.1 (V z y)) :
    let a := Statements.pairGrading p Statements.realGrading
    let q := gradedSeminorm F bond
    Statements.HasSmoothing p → Statements.HasSmoothing q →
    Statements.SmoothTameOn a q U R →
    Statements.SmoothTameOn (Statements.pairGrading a q) p (U ×ˢ univ)
      (fun z : (X × ℝ) × ProjectiveLimit F bond => V z.1 z.2) →
    Statements.SmoothTameOn (Statements.pairGrading (Statements.pairGrading a q) q)
      q ((U ×ˢ univ) ×ˢ univ)
      (fun z : ((X × ℝ) × ProjectiveLimit F bond) × ProjectiveLimit F bond => Q z.1.1 z.1.2 z.2) →
    ∃ SX : ℕ → X →L[ℝ] X, ∃ b l σ N₀ : ℕ, ∃ q₀ μ : ℝ,
      bMin ≤ b ∧ b₀ ≤ b ∧ 0 < N₀ ∧ 0 < q₀ ∧ q₀ ≤ μ ∧ 0 < μ ∧ 4 * μ ≤ ε₀ ∧
      (∀ τ : ℝ, |τ| < q₀ → ∀ n : ℕ,
        let N := newtonSmoothingIndex N₀
        let z := projectiveSmoothedNewtonIterates R V SX N (x₀, τ) n
        let α₀ : ℝ := 4 * (l : ℝ) + 4 * (σ : ℝ) + 2
        z ∈ U ∧ z.2 = τ ∧ p (b + l + l) (z.1 - x₀) < μ ∧
          q (b + l) (R z) ≤ Real.exp (-α₀ * N n)) ∧
      ∃ D : ℕ → ℕ → ℝ, (∀ s, Summable (D s)) ∧ (∀ s n, 0 ≤ D s n) ∧
        ∀ s n (τ : ℝ), |τ| < q₀ →
          let z := projectiveSmoothedNewtonIterates R V SX (newtonSmoothingIndex N₀) (x₀, τ)
          p s ((z (n + 1)).1 - (z n).1) ≤ D s n := by
  dsimp only
  intro hSX hSY hR hV hQ
  let a := Statements.pairGrading p Statements.realGrading
  let q := gradedSeminorm F bond
  have ha : Monotone a := pairGrading_monotone hp monotone_const
  have hq : Monotone q := gradedSeminorm_monotone F bond
  have hz₀ : (x₀, (0 : ℝ)) ∈ U := by
    rw [hU]
    change p b₀ (x₀ - x₀) < ε₀ ∧ |(0 : ℝ)| < ε₀
    simpa only [sub_self, map_zero, abs_zero] using And.intro hε₀ hε₀
  obtain ⟨bS, σ, SX, SY, _, _, hSmooth⟩ := exists_twoGradeNewtonSmoothingBounds hSX hSY
  obtain ⟨J, b, l, ε, hb, hε, hBounds⟩ :=
    exists_common_newton_tame_data ha hq (max bMin (max b₀ bS)) hR hV hQ hz₀
  have hbMin : bMin ≤ b := (le_max_left _ _).trans hb
  have hb₀ : b₀ ≤ b := (le_max_left _ _).trans ((le_max_right _ _).trans hb)
  have hbS : bS ≤ b := (le_max_right _ _).trans ((le_max_right _ _).trans hb)
  obtain ⟨Kₛ, hKₛ, hSmooth'⟩ := hSmooth b l (20 * l + 15 * σ + 8) hbS (by omega)
  obtain ⟨q₀, μ, hq₀, hqμ, hμ, hμε₀, hμε, hμ₁, N₀, _, hN₀, _, hseed⟩ :=
    projectiveNewton_seed_of_common_bounds p hp x₀ b₀ b l σ hb₀ ε₀ ε hε₀ hε
      hU R V Q J hzero hRight SX SY Kₛ hKₛ hBounds hSmooth'
  have hrapid := projectiveNewton_rapid_decay_of_seed p hp x₀ b₀ b l σ N₀ hb₀ hN₀
    ε₀ ε μ q₀ hμ hμε₀ hμε hμ₁ hqμ hU R V Q J hRight SX SY hBounds
    (fun h hh => hSmooth b l h hbS hh)
    (fun τ hτ n => by
      obtain ⟨hz, _, hdisp, hnear, hlow, hr, _⟩ := hseed τ hτ n
      exact ⟨hz, hdisp, hnear, hlow, hr⟩)
  choose C hC hCorrection using fun s => hrapid.2 s 1
  let N := newtonSmoothingIndex N₀
  let D := fun s n => C s * Real.exp (-(1 : ℝ) * N n)
  refine ⟨SX, b, l, σ, N₀, q₀, μ, hbMin, hb₀, hN₀, hq₀, hqμ, hμ, hμε₀, ?_,
    D, ?_, ?_, ?_⟩
  · intro τ hτ n
    obtain ⟨hz, hparam, hdisp, _, _, hr, _⟩ := hseed τ hτ n
    exact ⟨hz, hparam, hdisp, hr⟩
  · intro s
    exact (newton_summable_exponential hN₀ zero_lt_one).mul_left (C s)
  · intro s n
    exact mul_nonneg (hC s) (Real.exp_pos _).le
  · intro s n τ hτ
    let z := projectiveSmoothedNewtonIterates R V SX N (x₀, τ)
    let d := SX (N n) (V (z n) (R (z n)))
    change p s ((z n).1 - d - (z n).1) ≤ D s n
    rw [show (z n).1 - d - (z n).1 = -d by abel, map_neg_eq_map]
    exact hCorrection s n τ hτ

end ContinuousFlexibility.Analysis
