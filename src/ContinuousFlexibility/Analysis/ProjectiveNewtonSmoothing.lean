import ContinuousFlexibility.Analysis.ProjectiveNewtonTameBounds

/-!
# Smoothing bounds for the actual Newton update

One smoothing family controls the increment and its smoothing defect at two
grades. The estimates retain the fixed smoothing loss and the real parameter.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter
open scoped Topology

set_option backward.isDefEq.respectTransparency false

private theorem smoothing_bound_weaken {x A K a b u : ℝ}
    (hx : x ≤ A * a * u) (hAK : A ≤ K) (hK : 0 ≤ K)
    (ha : 0 ≤ a) (hab : a ≤ b) (hu : 0 ≤ u) : x ≤ K * b * u :=
  hx.trans (mul_le_mul_of_nonneg_right (mul_le_mul hAK hab ha hK) hu)

/-- The forward bounds start at any grade `m` below the output grades.
The tail starts at the grade `a + loss + ν`. -/
theorem exists_newton_smoothing_bounds
    {X : Type*} [TopologicalSpace X] [AddCommGroup X] [Module ℝ X]
    {p : ℕ → Seminorm ℝ X} (hS : Statements.HasSmoothing p) :
    ∃ base loss : ℕ, ∃ S : ℕ → X →L[ℝ] X,
      (∀ u, Tendsto (fun N => S N u) atTop (𝓝 u)) ∧
      ∀ m b a ν : ℕ, base ≤ m → m ≤ b → b ≤ a →
        ∃ K : ℝ, 0 ≤ K ∧ ∀ (N : ℕ) (u : X),
          p b (S N u) ≤ K * Real.exp (((b : ℝ) - m + loss) * N) * p m u ∧
          p a (S N u) ≤ K * Real.exp (((a : ℝ) - m + loss) * N) * p m u ∧
          p b (u - S N u) ≤ K * Real.exp (-(ν : ℝ) * N) * p (a + loss + ν) u ∧
          p a (u - S N u) ≤ K * Real.exp (-(ν : ℝ) * N) * p (a + loss + ν) u := by
  obtain ⟨base, loss, S, hforward, htail, hlim⟩ := hS
  refine ⟨base, loss, S, hlim, ?_⟩
  intro m b a ν hm hmb hba
  let h := a + loss + ν
  have hah : a ≤ h := by dsimp only [h]; omega
  obtain ⟨C₁, hC₁, H₁⟩ := hforward m b hm hmb
  obtain ⟨C₂, _, H₂⟩ := hforward m a hm (hmb.trans hba)
  obtain ⟨C₃, _, H₃⟩ := htail b h (hm.trans hmb) (hba.trans hah)
  obtain ⟨C₄, _, H₄⟩ := htail a h ((hm.trans hmb).trans hba) hah
  let K := max (max C₁ C₂) (max C₃ C₄)
  have hK₁ : C₁ ≤ K := (le_max_left C₁ C₂).trans (le_max_left _ _)
  have hK₂ : C₂ ≤ K := (le_max_right C₁ C₂).trans (le_max_left _ _)
  have hK₃ : C₃ ≤ K := (le_max_left C₃ C₄).trans (le_max_right _ _)
  have hK₄ : C₄ ≤ K := (le_max_right C₃ C₄).trans (le_max_right _ _)
  have hK : 0 ≤ K := hC₁.trans hK₁
  have hgap : (h : ℝ) - a - loss = ν := by
    simp only [h, Nat.cast_add]
    ring
  have hgap' : (ν : ℝ) ≤ (h : ℝ) - b - loss := by
    have hab : (b : ℝ) ≤ a := by exact_mod_cast hba
    linarith only [hab, hgap]
  refine ⟨K, hK, ?_⟩
  intro N u
  have htailB : Real.exp (-((h : ℝ) - b - loss) * N) ≤ Real.exp (-(ν : ℝ) * N) :=
    Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right (neg_le_neg hgap') (Nat.cast_nonneg N))
  refine ⟨smoothing_bound_weaken (H₁ N u) hK₁ hK (Real.exp_pos _).le le_rfl
      (apply_nonneg _ _),
    smoothing_bound_weaken (H₂ N u) hK₂ hK (Real.exp_pos _).le le_rfl (apply_nonneg _ _),
    smoothing_bound_weaken (H₃ N u) hK₃ hK (Real.exp_pos _).le htailB (apply_nonneg _ _), ?_⟩
  exact smoothing_bound_weaken (H₄ N u) hK₄ hK (Real.exp_pos _).le
    (by rw [hgap]) (apply_nonneg _ _)

/-- A base-grade margin keeps the smoothed Newton segment in the original
cylindrical domain with the parameter fixed. -/
theorem newton_segment_mem_of_seminorm_margin
    {X : Type*} [AddCommGroup X] [Module ℝ X]
    (p : Seminorm ℝ X) (x₀ : X) (z : X × ℝ) (u : X) {ε : ℝ}
    (hparam : |z.2| < ε) (hmargin : p (z.1 - x₀) + p u < ε) :
    ∀ t ∈ Icc (0 : ℝ) 1,
      z + t • ((-u, 0) : X × ℝ) ∈ {w | p (w.1 - x₀) < ε ∧ |w.2| < ε} := by
  intro t ht
  change p ((z.1 + t • -u) - x₀) < ε ∧ |z.2 + t • (0 : ℝ)| < ε
  constructor
  · have hu : p (t • -u) ≤ p u := by
      rw [map_smul_eq_mul, Real.norm_of_nonneg ht.1, map_neg_eq_map]
      exact mul_le_of_le_one_left (apply_nonneg p u) ht.2
    rw [show z.1 + t • -u - x₀ = (z.1 - x₀) + t • -u by abel]
    exact ((map_add_le_add p _ _).trans (add_le_add le_rfl hu)).trans_lt hmargin
  · simpa only [smul_zero, add_zero] using hparam

private theorem pair_realGrading_zero
    {X : Type*} [AddCommGroup X] [Module ℝ X]
    (p : ℕ → Seminorm ℝ X) (n : ℕ) (x : X) :
    Statements.pairGrading p Statements.realGrading n (x, 0) = p n x := by
  change p n x + Statements.realGrading n 0 = p n x
  rw [map_zero, add_zero]

/-- The two-grade correction bounds control the actual residual and keep
the full update segment in the original domain. -/
theorem projectiveSmoothedNewtonStep_residual_le_of_bounds
    {X : Type*} [TopologicalSpace X] [AddCommGroup X] [Module ℝ X]
    [IsTopologicalAddGroup X] [ContinuousSMul ℝ X]
    {F : ℕ → Type*} [∀ n, NormedAddCommGroup (F n)] [∀ n, NormedSpace ℝ (F n)]
    {bond : ∀ n, F (n + 1) →L[ℝ] F n} {f : X × ℝ → ProjectiveLimit F bond}
    {U : Set (X × ℝ)} (J : Statements.SmoothDirections U f)
    (p : ℕ → Seminorm ℝ X) (hp : Monotone p) (x₀ : X) (z : X × ℝ)
    (b₀ b l s : ℕ) (hb₀ : b₀ ≤ b) (ε₀ ε C : ℝ) (hC : 0 ≤ C)
    (hU : {w : X × ℝ | p b₀ (w.1 - x₀) < ε₀ ∧ |w.2| < ε₀} ⊆ U)
    (V : ProjectiveLimit F bond →ₗ[ℝ] X)
    (Q : ProjectiveLimit F bond →ₗ[ℝ] ProjectiveLimit F bond →ₗ[ℝ] ProjectiveLimit F bond)
    (hV : ∀ y, HasProjectiveLineDerivAt (fun x => f (x, z.2))
      (y + Q (f z) y) z.1 (V y))
    (S : X →L[ℝ] X) (Dbase Dhigh E Qbound : ℝ) :
    let a := Statements.pairGrading p Statements.realGrading
    let u := V (f z)
    (∀ w ∈ U, a b (w - (x₀, 0)) < ε → ∀ d : X × ℝ,
      (gradedSeminorm F bond s (projectiveJetHeadLinear J.D 0 w Fin.elim0 d) ≤
        C * ((1 + a (s + l) w) * a b d + a (s + l) d)) ∧
      (gradedSeminorm F bond s (J.D 2 w (Fin.cons d (Fin.cons d Fin.elim0))) ≤
        C * ((1 + a (s + l) w) * (a b d) ^ 2 + 2 * (a (s + l) d * a b d)))) →
    p b (S u) ≤ Dbase → p (s + l) (S u) ≤ Dhigh →
    p b (u - S u) ≤ E → p (s + l) (u - S u) ≤ E →
    |z.2| < ε₀ → p b (z.1 - x₀) + Dbase < ε₀ →
    a b (z - (x₀, 0)) + Dbase < ε →
    gradedSeminorm F bond s (Q (f z) (f z)) ≤ Qbound →
    gradedSeminorm F bond s (f (z.1 - S u, z.2)) ≤ Qbound +
      C * (2 + a (s + l) z) * E +
      (C * ((1 + a (s + l) z + Dhigh) * Dbase ^ 2 + 2 * (Dhigh * Dbase))) / 2 := by
  dsimp only
  intro hjet hDbase hDhigh hEbase hEhigh hparam hrect hball hQ
  let a := Statements.pairGrading p Statements.realGrading
  let u := V (f z)
  let d : X × ℝ := (-S u, 0)
  let e : X × ℝ := (u - S u, 0)
  have hd₁ : a b d ≤ Dbase := by
    simpa only [a, d, pair_realGrading_zero, map_neg_eq_map] using hDbase
  have hd₂ : a (s + l) d ≤ Dhigh := by
    simpa only [a, d, pair_realGrading_zero, map_neg_eq_map] using hDhigh
  have he₁ : a b e ≤ E := by simpa only [a, e, pair_realGrading_zero] using hEbase
  have he₂ : a (s + l) e ≤ E := by simpa only [a, e, pair_realGrading_zero] using hEhigh
  have hseg : ∀ t ∈ Icc (0 : ℝ) 1, z + t • d ∈ U := by
    have hm : p b₀ (z.1 - x₀) + p b₀ (S u) < ε₀ :=
      (add_le_add (hp hb₀ _) ((hp hb₀ _).trans hDbase)).trans_lt hrect
    intro t ht
    exact hU (newton_segment_mem_of_seminorm_margin (p b₀) x₀ z (S u) hparam hm t ht)
  have hlow : a b (z - (x₀, 0)) + a b d < ε :=
    (add_le_add le_rfl hd₁).trans_lt hball
  have hstep := projectiveSmoothedNewtonStep_tame_residual_le
    J a (x₀, 0) z b l s ε C hC hjet V Q hV S hseg hlow
  have hstate : 0 ≤ 1 + a (s + l) z := add_nonneg zero_le_one (apply_nonneg _ _)
  have hdefect : C * ((1 + a (s + l) z) * a b e + a (s + l) e) ≤
      C * (2 + a (s + l) z) * E := by
    calc
      _ ≤ C * ((1 + a (s + l) z) * E + E) :=
        mul_le_mul_of_nonneg_left
          (add_le_add (mul_le_mul_of_nonneg_left he₁ hstate) he₂) hC
      _ = _ := by ring
  have hDhigh₀ : 0 ≤ Dhigh := (apply_nonneg _ _).trans hd₂
  have hfactor : 1 + a (s + l) z + a (s + l) d ≤ 1 + a (s + l) z + Dhigh :=
    add_le_add le_rfl hd₂
  have hquad := add_le_add
    (mul_le_mul hfactor (pow_le_pow_left₀ (apply_nonneg _ _) hd₁ 2)
      (sq_nonneg _) (add_nonneg hstate hDhigh₀))
    (mul_le_mul_of_nonneg_left
      (mul_le_mul hd₂ hd₁ (apply_nonneg _ _) hDhigh₀) (show (0 : ℝ) ≤ 2 by norm_num))
  exact hstep.trans (add_le_add (add_le_add hQ hdefect)
    (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hquad hC) (by norm_num)))

/-- Substitute the forward and tail bounds for one member of the actual
smoothing family. The input correction bounds may come from the homogeneous
estimate for the linear right inverse. -/
theorem projectiveSmoothedNewtonStep_scaled_residual_le
    {X : Type*} [TopologicalSpace X] [AddCommGroup X] [Module ℝ X]
    [IsTopologicalAddGroup X] [ContinuousSMul ℝ X]
    {F : ℕ → Type*} [∀ n, NormedAddCommGroup (F n)] [∀ n, NormedSpace ℝ (F n)]
    {bond : ∀ n, F (n + 1) →L[ℝ] F n} {f : X × ℝ → ProjectiveLimit F bond}
    {U : Set (X × ℝ)} (J : Statements.SmoothDirections U f)
    (p : ℕ → Seminorm ℝ X) (hp : Monotone p) (x₀ : X) (z : X × ℝ)
    (b₀ b l s : ℕ) (hb₀ : b₀ ≤ b) (ε₀ ε C : ℝ) (hC : 0 ≤ C)
    (hU : {w : X × ℝ | p b₀ (w.1 - x₀) < ε₀ ∧ |w.2| < ε₀} ⊆ U)
    (V : ProjectiveLimit F bond →ₗ[ℝ] X)
    (Q : ProjectiveLimit F bond →ₗ[ℝ] ProjectiveLimit F bond →ₗ[ℝ] ProjectiveLimit F bond)
    (hV : ∀ y, HasProjectiveLineDerivAt (fun x => f (x, z.2))
      (y + Q (f z) y) z.1 (V y))
    (S : ℕ → X →L[ℝ] X) (m loss ν N : ℕ) (K L H Qbound : ℝ) (hK : 0 ≤ K) :
    let a := Statements.pairGrading p Statements.realGrading
    let u := V (f z)
    let B := K * Real.exp (((b : ℝ) - m + loss) * N)
    let A := K * Real.exp ((((s + l : ℕ) : ℝ) - m + loss) * N)
    let T := K * Real.exp (-(ν : ℝ) * N)
    let Dbase := B * L
    let Dhigh := A * L
    let E := T * H
    (∀ w ∈ U, a b (w - (x₀, 0)) < ε → ∀ d : X × ℝ,
      (gradedSeminorm F bond s (projectiveJetHeadLinear J.D 0 w Fin.elim0 d) ≤
        C * ((1 + a (s + l) w) * a b d + a (s + l) d)) ∧
      (gradedSeminorm F bond s (J.D 2 w (Fin.cons d (Fin.cons d Fin.elim0))) ≤
        C * ((1 + a (s + l) w) * (a b d) ^ 2 + 2 * (a (s + l) d * a b d)))) →
    p b (S N u) ≤ B * p m u → p (s + l) (S N u) ≤ A * p m u →
    p b (u - S N u) ≤ T * p (s + l + loss + ν) u →
    p (s + l) (u - S N u) ≤ T * p (s + l + loss + ν) u →
    p m u ≤ L → p (s + l + loss + ν) u ≤ H →
    |z.2| < ε₀ → p b (z.1 - x₀) + Dbase < ε₀ →
    a b (z - (x₀, 0)) + Dbase < ε →
    gradedSeminorm F bond s (Q (f z) (f z)) ≤ Qbound →
    gradedSeminorm F bond s (f (z.1 - S N u, z.2)) ≤ Qbound +
      C * (2 + a (s + l) z) * E +
      (C * ((1 + a (s + l) z + Dhigh) * Dbase ^ 2 + 2 * (Dhigh * Dbase))) / 2 := by
  dsimp only
  intro hjet hDb hDa hEb hEa hL hH hparam hrect hball hQ
  exact projectiveSmoothedNewtonStep_residual_le_of_bounds J p hp x₀ z b₀ b l s hb₀
    ε₀ ε C hC hU V Q hV (S N) _ _ _ Qbound hjet
    (hDb.trans (mul_le_mul_of_nonneg_left hL (mul_nonneg hK (Real.exp_pos _).le)))
    (hDa.trans (mul_le_mul_of_nonneg_left hL (mul_nonneg hK (Real.exp_pos _).le)))
    (hEb.trans (mul_le_mul_of_nonneg_left hH (mul_nonneg hK (Real.exp_pos _).le)))
    (hEa.trans (mul_le_mul_of_nonneg_left hH (mul_nonneg hK (Real.exp_pos _).le)))
    hparam hrect hball hQ

end ContinuousFlexibility.Analysis
