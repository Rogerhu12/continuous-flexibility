module

public import ContinuousFlexibility.Analysis.ProjectiveNewtonSchedule
public import ContinuousFlexibility.Analysis.ProjectiveNewtonTameData

/-!
# The initial parameter interval and the Newton domain

The finite correction budget proves the domain conditions before the
recurrence is used at each step. The initial scale and the parameter
interval are chosen once for the entire family of iterates.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter
open scoped Topology BigOperators

set_option backward.isDefEq.respectTransparency false

private theorem pair_realGrading_apply
    {X : Type*} [AddCommGroup X] [Module ℝ X]
    (p : ℕ → Seminorm ℝ X) (s : ℕ) (z : X × ℝ) :
    Statements.pairGrading p Statements.realGrading s z = p s z.1 + |z.2| := by
  change p s z.1 + ‖z.2‖ = p s z.1 + |z.2|
  rw [Real.norm_eq_abs]

private theorem pair_realGrading_sub_center
    {X : Type*} [AddCommGroup X] [Module ℝ X]
    (p : ℕ → Seminorm ℝ X) (s : ℕ) (z : X × ℝ) (x₀ : X) :
    Statements.pairGrading p Statements.realGrading s (z - (x₀, 0)) =
      p s (z.1 - x₀) + |z.2| := by
  rw [pair_realGrading_apply]
  change p s (z.1 - x₀) + |z.2 - 0| = _
  rw [sub_zero]

private theorem newton_state_margins
    {X : Type*} [AddCommGroup X] [Module ℝ X]
    (p : ℕ → Seminorm ℝ X) (hp : Monotone p) (x₀ : X) (z : X × ℝ)
    {b₀ b A : ℕ} (hb₀ : b₀ ≤ b) (hbA : b ≤ A)
    {ε₀ ε μ d : ℝ} (hμ₀ : 2 * μ ≤ ε₀) (hμε : 2 * μ ≤ ε) (hμ₁ : 2 * μ ≤ 1)
    (hd : 0 ≤ d) (hparam : |z.2| < μ) (hdisp : p A (z.1 - x₀) + d < μ) :
    z ∈ {w : X × ℝ | p b₀ (w.1 - x₀) < ε₀ ∧ |w.2| < ε₀} ∧
      Statements.pairGrading p Statements.realGrading b (z - (x₀, 0)) < ε ∧
      1 + Statements.pairGrading p Statements.realGrading A z ≤ 2 + p A x₀ ∧
      p b (z.1 - x₀) + d < ε₀ ∧
      Statements.pairGrading p Statements.realGrading b (z - (x₀, 0)) + d < ε ∧ d ≤ 1 := by
  have hμ : 0 ≤ μ := (abs_nonneg _).trans hparam.le
  have hlow := hp hbA (z.1 - x₀)
  have horig := hp hb₀ (z.1 - x₀)
  have hnorm : p A z.1 ≤ p A x₀ + p A (z.1 - x₀) := by
    calc
      _ = p A (x₀ + (z.1 - x₀)) := congrArg (fun x => p A x) (by abel)
      _ ≤ _ := map_add_le_add (p A) _ _
  have hd₀ := apply_nonneg (p A) (z.1 - x₀)
  rw [pair_realGrading_sub_center, pair_realGrading_apply]
  refine ⟨⟨?_, ?_⟩, ?_, ?_, ?_, ?_, ?_⟩
  · linarith only [horig, hlow, hdisp, hd, hμ, hμ₀]
  · linarith only [hparam, hμ, hμ₀]
  · linarith only [hlow, hdisp, hd, hparam, hμε]
  · linarith only [hnorm, hdisp, hd, hparam, hμ₁]
  · linarith only [hlow, hdisp, hμ, hμ₀]
  · linarith only [hlow, hdisp, hparam, hμε]
  · linarith only [hd₀, hdisp, hμ, hμ₁]

/-- A conditional correction bound is sufficient on a finite prefix. The
earlier corrections give the domain conditions for the current correction. -/
theorem projectiveNewton_prefix_control
    {X Y : Type*} [TopologicalSpace X] [AddCommGroup X] [Module ℝ X]
    [AddCommGroup Y] [Module ℝ Y]
    (R : X × ℝ → Y) (V : X × ℝ → Y →ₗ[ℝ] X) (S : ℕ → X →L[ℝ] X) (N : ℕ → ℕ)
    (p : ℕ → Seminorm ℝ X) (hp : Monotone p) (x₀ : X) (τ : ℝ)
    {b₀ b A : ℕ} (hb₀ : b₀ ≤ b) (hbA : b ≤ A)
    {ε₀ ε μ : ℝ} (hμ₀ : 2 * μ ≤ ε₀) (hμε : 2 * μ ≤ ε) (hμ₁ : 2 * μ ≤ 1)
    (hparam : |τ| < μ) (D : ℕ → ℝ) (n : ℕ)
    (hprefix : ∀ k ≤ n + 1, (∑ i ∈ Finset.range k, D i) < μ) :
    let U : Set (X × ℝ) := {z | p b₀ (z.1 - x₀) < ε₀ ∧ |z.2| < ε₀}
    let a := Statements.pairGrading p Statements.realGrading
    let z := projectiveSmoothedNewtonIterates R V S N (x₀, τ)
    let d := fun k => S (N k) (V (z k) (R (z k)))
    (∀ k ≤ n, z k ∈ U → a b (z k - (x₀, 0)) < ε →
      1 + a A (z k) ≤ 2 + p A x₀ → p A (d k) ≤ D k) →
    (∀ k ≤ n + 1, z k ∈ U ∧ a b (z k - (x₀, 0)) < ε ∧
      1 + a A (z k) ≤ 2 + p A x₀) ∧
    (∀ k ≤ n, p A (d k) ≤ D k) := by
  dsimp only
  intro hcorrection
  let U : Set (X × ℝ) := {z | p b₀ (z.1 - x₀) < ε₀ ∧ |z.2| < ε₀}
  let a := Statements.pairGrading p Statements.realGrading
  let z := projectiveSmoothedNewtonIterates R V S N (x₀, τ)
  let d := fun k => S (N k) (V (z k) (R (z k)))
  have hstate (k : ℕ) (hk : k ≤ n + 1) (hprev : ∀ j < k, p A (d j) ≤ D j) :
      z k ∈ U ∧ a b (z k - (x₀, 0)) < ε ∧ 1 + a A (z k) ≤ 2 + p A x₀ := by
    have hdisp : p A ((z k).1 - x₀) < μ :=
      (projectiveSmoothedNewtonIterates_displacement_le R V S N (x₀, τ)
        (p A) D k hprev).trans_lt (hprefix k hk)
    have ht : |(z k).2| < μ := by
      rw [show (z k).2 = τ from projectiveSmoothedNewtonIterates_parameter R V S N (x₀, τ) k]
      exact hparam
    obtain ⟨hz, htame, hsize, _, _, _⟩ := newton_state_margins p hp x₀ (z k) hb₀ hbA
      hμ₀ hμε hμ₁ (show (0 : ℝ) ≤ 0 from le_rfl) ht (by simpa only [add_zero] using hdisp)
    exact ⟨hz, htame, hsize⟩
  have hc : ∀ k ≤ n, p A (d k) ≤ D k := by
    intro k
    induction k using Nat.strong_induction_on with
    | h k ih =>
      intro hk
      have hprev (j : ℕ) (hj : j < k) : p A (d j) ≤ D j := ih j hj ((Nat.le_of_lt hj).trans hk)
      obtain ⟨hz, htame, hsize⟩ := hstate k (hk.trans (Nat.le_succ n)) hprev
      exact hcorrection k hk hz htame hsize
  exact ⟨fun k hk => hstate k hk (fun j hj => hc j (Nat.lt_succ_iff.mp (hj.trans_le hk))), hc⟩

/-- At the reference zero, a single residual grade is small throughout
one real parameter interval. -/
theorem exists_initial_residual_radius
    {X : Type*} [TopologicalSpace X] [AddCommGroup X] [Module ℝ X]
    {F : ℕ → Type*} [∀ n, NormedAddCommGroup (F n)] [∀ n, NormedSpace ℝ (F n)]
    {bond : ∀ n, F (n + 1) →L[ℝ] F n}
    {R : X × ℝ → ProjectiveLimit F bond} {U : Set (X × ℝ)}
    (J : Statements.SmoothDirections U R) (x₀ : X) (hz₀ : (x₀, 0) ∈ U)
    (hzero : R (x₀, 0) = 0) (B : ℕ) {η : ℝ} (hη : 0 < η) :
    ∃ d : ℝ, 0 < d ∧ ∀ τ : ℝ, |τ| < d →
      gradedSeminorm F bond B (R (x₀, τ)) ≤ η := by
  have hpair : Continuous (fun z : X × ℝ => (z, (Fin.elim0 : Fin 0 → X × ℝ))) :=
    continuous_id.prodMk continuous_const
  have hmap : MapsTo (fun z : X × ℝ => (z, (Fin.elim0 : Fin 0 → X × ℝ))) U (U ×ˢ univ) :=
    fun z hz => ⟨hz, mem_univ _⟩
  have hR : ContinuousOn R U :=
    ((J.continuous 0).comp' hpair.continuousOn hmap).congr (fun z hz => (J.zero z hz).symm)
  have hR₀ : ContinuousAt R (x₀, 0) :=
    (hR (x₀, 0) hz₀).continuousAt (J.open_domain.mem_nhds hz₀)
  have hline : Continuous (fun τ : ℝ => (x₀, τ)) := continuous_const.prodMk continuous_id
  have hcont : ContinuousAt (fun τ : ℝ => gradedSeminorm F bond B (R (x₀, τ))) 0 :=
    (continuous_gradedSeminorm F bond B).continuousAt.comp (hR₀.comp hline.continuousAt)
  have hlim : Tendsto (fun τ : ℝ => gradedSeminorm F bond B (R (x₀, τ))) (𝓝 0)
      (𝓝 (gradedSeminorm F bond B (R (x₀, 0)))) := hcont
  have hinit : gradedSeminorm F bond B (R (x₀, 0)) < η := by
    simpa only [hzero, map_zero] using hη
  obtain ⟨d, hd, hd'⟩ := Metric.eventually_nhds_iff.mp (hlim.eventually_lt_const hinit)
  refine ⟨d, hd, fun τ hτ => (hd' (y := τ) ?_).le⟩
  simpa only [Real.dist_eq, sub_zero] using hτ

/-- Initialize the actual fixed-parameter iterates from the common tame
bounds and the two smoothing families. The interval and the scale sequence
are chosen before any individual parameter or iteration index. -/
theorem projectiveNewton_seed_of_common_bounds
    {X : Type*} [TopologicalSpace X] [AddCommGroup X] [Module ℝ X]
    [IsTopologicalAddGroup X] [ContinuousSMul ℝ X]
    {F : ℕ → Type*} [∀ n, NormedAddCommGroup (F n)] [∀ n, NormedSpace ℝ (F n)]
    {bond : ∀ n, F (n + 1) →L[ℝ] F n}
    (p : ℕ → Seminorm ℝ X) (hp : Monotone p) (x₀ : X)
    (b₀ b l σ : ℕ) (hb₀ : b₀ ≤ b) (ε₀ ε : ℝ) (hε₀ : 0 < ε₀) (hε : 0 < ε)
    {U : Set (X × ℝ)} (hU : U = {z | p b₀ (z.1 - x₀) < ε₀ ∧ |z.2| < ε₀})
    (R : X × ℝ → ProjectiveLimit F bond)
    (V : X × ℝ → ProjectiveLimit F bond →ₗ[ℝ] X)
    (Q : X × ℝ → ProjectiveLimit F bond →ₗ[ℝ] ProjectiveLimit F bond →ₗ[ℝ] ProjectiveLimit F bond)
    (J : Statements.SmoothDirections U R) (hzero : R (x₀, 0) = 0)
    (hV : ∀ z ∈ U, ∀ y, HasProjectiveLineDerivAt (fun x => R (x, z.2))
      (y + Q z (R z) y) z.1 (V z y))
    (SX : ℕ → X →L[ℝ] X) (SY : ℕ → ProjectiveLimit F bond →L[ℝ] ProjectiveLimit F bond)
    (Kₛ : ℝ) (hKₛ : 0 ≤ Kₛ) :
    let a := Statements.pairGrading p Statements.realGrading
    let q := gradedSeminorm F bond
    let h := 20 * l + 15 * σ + 8
    let B := b + l
    let A := B + l
    let G := b + h
    let H := b + h + 2 * l
    let β : ℝ := (h : ℝ) - 2 * (l : ℝ) - σ
    let α : ℝ := 4 * (l : ℝ) + 4 * (σ : ℝ) + 2
    let γ : ℝ := 12 * (l : ℝ) + 8 * (σ : ℝ) + 4
    (∀ s : ℕ, b ≤ s → ∃ C : ℝ, 0 ≤ C ∧ ∀ z ∈ U, a b (z - (x₀, 0)) < ε →
      (q s (R z) ≤ C * (1 + a (s + l) z)) ∧
      (∀ d : X × ℝ,
        (q s (projectiveJetHeadLinear J.D 0 z Fin.elim0 d) ≤
          C * ((1 + a (s + l) z) * a b d + a (s + l) d)) ∧
        (q s (J.D 2 z (Fin.cons d (Fin.cons d Fin.elim0))) ≤
          C * ((1 + a (s + l) z) * (a b d) ^ 2 + 2 * (a (s + l) d * a b d)))) ∧
      (∀ y, p s (V z y) ≤ C * (q (s + l) y + (1 + a (s + l) z) * q b y)) ∧
      (∀ r y, q s (Q z r y) ≤ C * ((1 + a (s + l) z) * (q b r * q b y) +
        (q (s + l) r * q b y + q b r * q (s + l) y)))) →
    (∀ (N : ℕ) (u : X) (r : ProjectiveLimit F bond),
      (p b (SX N u) ≤ Kₛ * Real.exp ((σ : ℝ) * N) * p b u ∧
        p A (SX N u) ≤ Kₛ * Real.exp ((2 * (l : ℝ) + σ) * N) * p b u ∧
        p H (SX N u) ≤ Kₛ * Real.exp (((h : ℝ) + 2 * (l : ℝ) + σ) * N) * p b u ∧
        p b (u - SX N u) ≤ Kₛ * Real.exp (-β * N) * p G u ∧
        p A (u - SX N u) ≤ Kₛ * Real.exp (-β * N) * p G u) ∧
      (q A (SY N r) ≤ Kₛ * Real.exp (((l : ℝ) + σ) * N) * q B r ∧
        q A (r - SY N r) ≤ Kₛ * Real.exp (-β * N) * q G r)) →
    ∃ q₀ μ : ℝ, 0 < q₀ ∧ q₀ ≤ μ ∧ 0 < μ ∧ 4 * μ ≤ ε₀ ∧ 4 * μ ≤ ε ∧ 4 * μ ≤ 1 ∧
      ∃ N₀ : ℕ, ∃ Mhigh : ℝ, 0 < N₀ ∧ 0 ≤ Mhigh ∧
        ∀ τ : ℝ, |τ| < q₀ → ∀ n : ℕ,
          let N := newtonSmoothingIndex N₀
          let z := projectiveSmoothedNewtonIterates R V SX N (x₀, τ) n
          z ∈ U ∧ z.2 = τ ∧ p A (z.1 - x₀) < μ ∧ a b (z - (x₀, 0)) < ε ∧
            1 + a A z ≤ 2 + p A x₀ ∧ q B (R z) ≤ Real.exp (-α * N n) ∧
            1 + a H z ≤ Mhigh * Real.exp (γ * N n) := by
  subst U
  dsimp only
  intro hBounds hSmooth
  let U : Set (X × ℝ) := {z | p b₀ (z.1 - x₀) < ε₀ ∧ |z.2| < ε₀}
  let a := Statements.pairGrading p Statements.realGrading
  let q := gradedSeminorm F bond
  let h := 20 * l + 15 * σ + 8
  let B := b + l
  let A := B + l
  let G := b + h
  let H := b + h + 2 * l
  let α : ℝ := 4 * (l : ℝ) + 4 * (σ : ℝ) + 2
  let γ : ℝ := 12 * (l : ℝ) + 8 * (σ : ℝ) + 4
  let δ : ℝ := 2 * (l : ℝ) + 3 * (σ : ℝ) + 2
  let Mlow := 2 + p A x₀
  have hbB : b ≤ B := Nat.le_add_right _ _
  have hbA : b ≤ A := hbB.trans (Nat.le_add_right _ _)
  have hbG : b ≤ G := Nat.le_add_right _ _
  have ha : Monotone a := pairGrading_monotone hp monotone_const
  have hq : Monotone q := gradedSeminorm_monotone F bond
  have hMlow : 0 ≤ Mlow := add_nonneg (by norm_num) (apply_nonneg _ _)
  have hδ : 0 < δ := by dsimp only [δ]; positivity
  have hα : 0 ≤ α := by dsimp only [α]; positivity
  have hγ : 0 ≤ γ := by dsimp only [γ]; positivity
  obtain ⟨C, hC, HB⟩ := hBounds B hbB
  obtain ⟨Cb, hCb, Hb⟩ := hBounds b le_rfl
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
  let K := Kₛ * Kᵥ
  have hK : 0 ≤ K := mul_nonneg hKₛ (zero_le_one.trans hKv₁)
  let Crec := (C * (Mlow + 2 * K) + C * (Mlow + 3) * K ^ 2 / 2) + C * (Mlow + 3) * K
  have hCrec : 0 ≤ Crec := by dsimp only [Crec]; positivity
  let Mhigh := 2 + p H x₀ + 2 * K
  have hpH : 0 ≤ p H x₀ := apply_nonneg _ _
  have hMhigh : 0 ≤ Mhigh := by dsimp only [Mhigh]; linarith only [hpH, hK]
  have hcoef : K * 1 ≤ Mhigh / 2 := by dsimp only [Mhigh]; linarith only [hpH]
  let μ := min (1 / 4 : ℝ) (min (ε₀ / 4) (ε / 4))
  have hμ : 0 < μ := lt_min (by norm_num) (lt_min (div_pos hε₀ (by norm_num)) (div_pos hε (by norm_num)))
  have hμε₀ : 4 * μ ≤ ε₀ := by
    have hm : μ ≤ ε₀ / 4 := (min_le_right _ _).trans (min_le_left _ _)
    linarith only [hm]
  have hμε : 4 * μ ≤ ε := by
    have hm : μ ≤ ε / 4 := (min_le_right _ _).trans (min_le_right _ _)
    linarith only [hm]
  have hμ₁ : 4 * μ ≤ 1 := by
    have hm : μ ≤ 1 / 4 := min_le_left _ _
    linarith only [hm]
  have hm₀ : 2 * μ ≤ ε₀ := by linarith only [hμ, hμε₀]
  have hme : 2 * μ ≤ ε := by linarith only [hμ, hμε]
  have hm₁ : 2 * μ ≤ 1 := by linarith only [hμ, hμ₁]
  obtain ⟨N₀, hN₀, hthreshold, hprefix⟩ :=
    exists_newton_starting_index Crec K Mhigh α 1 δ μ zero_lt_one hδ hμ
  let N := newtonSmoothingIndex N₀
  let D := fun n => K * Real.exp (-δ * N n)
  have hsum (n : ℕ) : (∑ k ∈ Finset.range n, D k) < μ := by
    calc
      _ = K * ∑ k ∈ Finset.range n, Real.exp (-δ * N k) := by
        simp only [D, Finset.mul_sum]
      _ ≤ K * (Real.exp (-δ * N₀) * (1 - Real.exp (-δ))⁻¹) :=
        mul_le_mul_of_nonneg_left (newton_exponential_prefix_le hN₀ hδ n) hK
      _ < μ := by simpa only [mul_one, mul_assoc] using hprefix
  have hz₀ : (x₀, (0 : ℝ)) ∈ U := by
    change p b₀ (x₀ - x₀) < ε₀ ∧ |(0 : ℝ)| < ε₀
    simpa only [sub_self, map_zero, abs_zero] using And.intro hε₀ hε₀
  obtain ⟨d, hd, hinit⟩ :=
    exists_initial_residual_radius J x₀ hz₀ hzero B (Real.exp_pos (-α * N₀))
  let q₀ := min μ d
  refine ⟨q₀, μ, lt_min hμ hd, min_le_left _ _, hμ, hμε₀, hμε, hμ₁,
    N₀, Mhigh, hN₀, hMhigh, ?_⟩
  intro τ hτ
  have hτμ : |τ| < μ := hτ.trans_le (min_le_left _ _)
  have hτd : |τ| < d := hτ.trans_le (min_le_right _ _)
  let z := projectiveSmoothedNewtonIterates R V SX N (x₀, τ)
  let u := fun n => V (z n) (R (z n))
  let r := fun n => q B (R (z n))
  let size := fun n => 1 + a H (z n)
  have hr₀ (n : ℕ) : 0 ≤ r n := apply_nonneg _ _
  have hrone {n : ℕ} (hr : r n ≤ Real.exp (-α * N n)) : r n ≤ 1 := by
    refine hr.trans ?_
    rw [← Real.exp_zero]
    exact Real.exp_le_exp.mpr (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hα) (Nat.cast_nonneg _))
  have hcor (w : X × ℝ) (hw : w ∈ U) (hwnear : a b (w - (x₀, 0)) < ε)
      (hwsize : 1 + a A w ≤ Mlow) (hwr : q B (R w) ≤ 1) :
      p b (V w (R w)) ≤ Kᵥ * q B (R w) ∧
        p G (V w (R w)) ≤ Kᵥ * (1 + a H w) ∧ q G (R w) ≤ Kᵥ * (1 + a H w) := by
    have hpos (s : ℕ) : 0 ≤ 1 + a s w := add_nonneg zero_le_one (apply_nonneg _ _)
    have hbr (s : ℕ) : 0 ≤ q (s + l) (R w) + (1 + a (s + l) w) * q b (R w) :=
      add_nonneg (apply_nonneg _ _) (mul_nonneg (hpos _) (apply_nonneg _ _))
    have hbnd := ((Hb w hw hwnear).2.2.1 (R w)).trans (mul_le_mul_of_nonneg_right hCb' (hbr b))
    have hgnd := ((Hg w hw hwnear).2.2.1 (R w)).trans (mul_le_mul_of_nonneg_right hCg' (hbr G))
    have hH : G + l + l = H := by dsimp only [G, H]; omega
    have hR : q (G + l) (R w) ≤ Cv * (1 + a H w) := by
      rw [← hH]
      exact ((Hh w hw hwnear).1).trans (mul_le_mul_of_nonneg_right hCh' (hpos _))
    exact (newton_correction_bounds_of_tame a p q ha hq w (V w (R w)) (R w) b l h Cv Mlow
      hCv hMlow hwsize hwr hbnd hgnd hR).2
  have hDhigh (k : ℕ) (hr : r k ≤ Real.exp (-α * N k)) :
      K * Real.exp ((2 * (l : ℝ) + σ) * N k) * r k ≤ D k := by
    calc
      _ ≤ K * Real.exp ((2 * (l : ℝ) + σ) * N k) * Real.exp (-α * N k) :=
        mul_le_mul_of_nonneg_left hr (mul_nonneg hK (Real.exp_pos _).le)
      _ = K * (Real.exp ((2 * (l : ℝ) + σ) * N k) * Real.exp (-α * N k)) := mul_assoc _ _ _
      _ = _ := by
        dsimp only [D]
        rw [← Real.exp_add]
        rw [show (2 * (l : ℝ) + σ) * N k + -α * N k = -δ * N k by
          dsimp only [α, δ]
          ring]
  have hDbase (k : ℕ) (hr : r k ≤ Real.exp (-α * N k)) :
      K * Real.exp ((σ : ℝ) * N k) * r k ≤ D k := by
    have he : Real.exp ((σ : ℝ) * N k) ≤ Real.exp ((2 * (l : ℝ) + σ) * N k) :=
      Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right
        (by linarith only [show (0 : ℝ) ≤ l from Nat.cast_nonneg l]) (Nat.cast_nonneg _))
    exact (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left he hK) (hr₀ k)).trans
      (hDhigh k hr)
  have hprefix_control (n : ℕ) (hRate : ∀ k ≤ n, r k ≤ Real.exp (-α * N k)) :
      (∀ k ≤ n + 1, z k ∈ U ∧ a b (z k - (x₀, 0)) < ε ∧ 1 + a A (z k) ≤ Mlow) ∧
        (∀ k ≤ n, p A (SX (N k) (u k)) ≤ D k) := by
    apply projectiveNewton_prefix_control R V SX N p hp x₀ τ hb₀ hbA
      hm₀ hme hm₁ hτμ D n (fun k _ => hsum k)
    intro k hk hz htame hsize
    have hvb := (hcor (z k) hz htame hsize (hrone (hRate k hk))).1
    have hforward := (hSmooth (N k) (u k) (R (z k))).1.2.1
    calc
      _ ≤ Kₛ * Real.exp ((2 * (l : ℝ) + σ) * N k) * (Kᵥ * r k) :=
        hforward.trans (mul_le_mul_of_nonneg_left hvb (mul_nonneg hKₛ (Real.exp_pos _).le))
      _ = K * Real.exp ((2 * (l : ℝ) + σ) * N k) * r k := by dsimp only [K]; ring
      _ ≤ _ := hDhigh k (hRate k hk)
  have hrec (n : ℕ)
      (hpref : ∀ k ≤ n, r k ≤ 1 * Real.exp (-α * N k) ∧ size k ≤ Mhigh * Real.exp (γ * N k)) :
      r (n + 1) ≤ Crec * (Real.exp ((2 * (l : ℝ) + 2 * (σ : ℝ)) * N n) * (r n) ^ 2 +
        Real.exp (-((h : ℝ) - 2 * (l : ℝ) - σ) * N n) * size n) ∧
      size (n + 1) ≤ size n + K * Real.exp (((h : ℝ) + 2 * (l : ℝ) + σ) * N n) * r n := by
    have hr (k : ℕ) (hk : k ≤ n) : r k ≤ Real.exp (-α * N k) := by
      simpa only [one_mul] using (hpref k hk).1
    obtain ⟨hstate, hinc⟩ := hprefix_control n hr
    obtain ⟨hz, hnear, hsize⟩ := hstate n (Nat.le_succ n)
    have hrn := hr n le_rfl
    obtain ⟨hvb, hvg, hrg⟩ := hcor (z n) hz hnear hsize (hrone hrn)
    let Db := K * Real.exp ((σ : ℝ) * N n) * r n
    have hDb₀ : 0 ≤ Db := mul_nonneg (mul_nonneg hK (Real.exp_pos _).le) (hr₀ n)
    have hdisp : p A ((z n).1 - x₀) ≤ ∑ k ∈ Finset.range n, D k :=
      projectiveSmoothedNewtonIterates_displacement_le R V SX N (x₀, τ)
        (p A) D n (fun k hk => hinc k hk.le)
    have hdispDb : p A ((z n).1 - x₀) + Db < μ := by
      have hsum' : (∑ k ∈ Finset.range n, D k) + D n < μ := by
        simpa only [Finset.sum_range_succ] using hsum (n + 1)
      exact (add_le_add hdisp (hDbase n hrn)).trans_lt hsum'
    have hτn : |(z n).2| < μ := by
      rw [show (z n).2 = τ from projectiveSmoothedNewtonIterates_parameter R V SX N (x₀, τ) n]
      exact hτμ
    obtain ⟨hz', _, _, hrect, hball, hDb₁⟩ := newton_state_margins p hp x₀ (z n) hb₀ hbA
      hm₀ hme hm₁ hDb₀ hτn hdispDb
    have hparam : |(z n).2| < ε₀ := hz'.2
    have hQdiag : q B (Q (z n) (R (z n)) (R (z n))) ≤
        C * ((1 + a A (z n)) * (q b (R (z n))) ^ 2 + 2 * (q A (R (z n)) * q b (R (z n)))) := by
      calc
        _ ≤ C * ((1 + a A (z n)) * (q b (R (z n)) * q b (R (z n))) +
            (q A (R (z n)) * q b (R (z n)) + q b (R (z n)) * q A (R (z n)))) :=
          (HB (z n) hz hnear).2.2.2 (R (z n)) (R (z n))
        _ = _ := by ring
    obtain ⟨_, _, _, hxnext, hrnext⟩ := projectiveSmoothedNewtonStep_twoGradeRecurrence
      J p hp x₀ (z n) b₀ b l h σ (N n) hb₀ ε₀ ε C Kₛ Kᵥ Mlow
      hC hKₛ hKv₁ hMlow Subset.rfl V Q (hV (z n) hz) (SX (N n)) (SY (N n))
      (fun w hw hwnear => (HB w hw hwnear).2.1) hvb hvg hrg hQdiag
      (hSmooth (N n) (u n) (R (z n))).1 (hSmooth (N n) (u n) (R (z n))).2
      hparam hrect hball hsize (hrone hrn) hDb₁
    exact ⟨hrnext, hxnext⟩
  have hrinit : r 0 ≤ 1 * Real.exp (-α * N₀) := by
    change q B (R (x₀, τ)) ≤ 1 * Real.exp (-α * N₀)
    simpa only [one_mul] using hinit τ hτd
  have hxinit : size 0 ≤ Mhigh * Real.exp (γ * N₀) := by
    have hbound : 1 + a H (x₀, τ) ≤ Mhigh := by
      rw [show a H (x₀, τ) = p H x₀ + |τ| from pair_realGrading_apply p H (x₀, τ)]
      dsimp only [Mhigh]
      linarith only [hτμ, hμ₁, hK]
    exact hbound.trans (by
      simpa only [mul_one] using mul_le_mul_of_nonneg_left
        (Real.one_le_exp (mul_nonneg hγ (Nat.cast_nonneg N₀))) hMhigh)
  have hbudget (n : ℕ) :
      r n ≤ 1 * Real.exp (-α * N n) ∧ size n ≤ Mhigh * Real.exp (γ * N n) :=
    newton_budget_induction l σ N₀ hN₀ r size Crec K Mhigh 1 hCrec hK hMhigh zero_le_one
      hcoef hr₀ hthreshold hrinit hxinit hrec n
  intro n
  have hr (k : ℕ) : r k ≤ Real.exp (-α * N k) := by simpa only [one_mul] using (hbudget k).1
  obtain ⟨hstate, hinc⟩ := hprefix_control n (fun k _ => hr k)
  obtain ⟨hz, hnear, hsize⟩ := hstate n (Nat.le_succ n)
  have hdisp : p A ((z n).1 - x₀) < μ :=
    (projectiveSmoothedNewtonIterates_displacement_le R V SX N (x₀, τ)
      (p A) D n (fun k hk => hinc k hk.le)).trans_lt (hsum n)
  exact ⟨hz, projectiveSmoothedNewtonIterates_parameter R V SX N (x₀, τ) n,
    hdisp, hnear, hsize, hr n, (hbudget n).2⟩

/-- The original smoothing, smooth tame, and quadratic-error hypotheses
give one initial parameter interval for the actual Newton iterates. -/
theorem exists_projectiveNewton_seed
    {X : Type*} [TopologicalSpace X] [AddCommGroup X] [Module ℝ X] [T2Space X]
    [IsTopologicalAddGroup X] [ContinuousSMul ℝ X]
    {F : ℕ → Type*} [∀ n, NormedAddCommGroup (F n)] [∀ n, NormedSpace ℝ (F n)]
    {bond : ∀ n, F (n + 1) →L[ℝ] F n}
    (p : ℕ → Seminorm ℝ X) (hp : Monotone p) (x₀ : X)
    (b₀ : ℕ) (ε₀ : ℝ) (hε₀ : 0 < ε₀)
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
    ∃ SX : ℕ → X →L[ℝ] X, ∃ SY : ℕ → ProjectiveLimit F bond →L[ℝ] ProjectiveLimit F bond,
      (∀ u, Tendsto (fun N => SX N u) atTop (𝓝 u)) ∧
      (∀ r, Tendsto (fun N => SY N r) atTop (𝓝 r)) ∧
      ∃ b l σ N₀ : ℕ, ∃ ε q₀ μ Mhigh : ℝ,
        b₀ ≤ b ∧ 0 < N₀ ∧ 0 < ε ∧ 0 < q₀ ∧ q₀ ≤ μ ∧ 0 < μ ∧
        4 * μ ≤ ε₀ ∧ 4 * μ ≤ ε ∧ 4 * μ ≤ 1 ∧ 0 ≤ Mhigh ∧
        ∀ τ : ℝ, |τ| < q₀ → ∀ n : ℕ,
          let N := newtonSmoothingIndex N₀
          let z := projectiveSmoothedNewtonIterates R V SX N (x₀, τ) n
          let h := 20 * l + 15 * σ + 8
          let α : ℝ := 4 * (l : ℝ) + 4 * (σ : ℝ) + 2
          let γ : ℝ := 12 * (l : ℝ) + 8 * (σ : ℝ) + 4
          z ∈ U ∧ z.2 = τ ∧ p (b + l + l) (z.1 - x₀) < μ ∧ a b (z - (x₀, 0)) < ε ∧
            1 + a (b + l + l) z ≤ 2 + p (b + l + l) x₀ ∧
            q (b + l) (R z) ≤ Real.exp (-α * N n) ∧
            1 + a (b + h + 2 * l) z ≤ Mhigh * Real.exp (γ * N n) := by
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
  obtain ⟨bS, σ, SX, SY, hlimX, hlimY, hSmooth⟩ :=
    exists_twoGradeNewtonSmoothingBounds hSX hSY
  obtain ⟨J, b, l, ε, hb, hε, hBounds⟩ :=
    exists_common_newton_tame_data ha hq (max b₀ bS) hR hV hQ hz₀
  have hb₀ : b₀ ≤ b := (le_max_left _ _).trans hb
  have hbS : bS ≤ b := (le_max_right _ _).trans hb
  obtain ⟨Kₛ, hKₛ, hSmooth'⟩ := hSmooth b l (20 * l + 15 * σ + 8) hbS (by omega)
  obtain ⟨q₀, μ, hq₀, hqμ, hμ, hμε₀, hμε, hμ₁, N₀, Mhigh, hN₀, hMhigh, hseed⟩ :=
    projectiveNewton_seed_of_common_bounds p hp x₀ b₀ b l σ hb₀ ε₀ ε hε₀ hε
      hU R V Q J hzero hRight SX SY Kₛ hKₛ hBounds hSmooth'
  exact ⟨SX, SY, hlimX, hlimY, b, l, σ, N₀, ε, q₀, μ, Mhigh, hb₀, hN₀, hε,
    hq₀, hqμ, hμ, hμε₀, hμε, hμ₁, hMhigh, hseed⟩

end ContinuousFlexibility.Analysis
