module

public import ContinuousFlexibility.Analysis.ProjectiveNewtonEstimate
public import ContinuousFlexibility.Statements.Analysis

/-!
# Tame bounds for a smoothed Newton step

The first and second directional jets have estimates on one common low-order
neighborhood. A bound on the initial displacement and the chosen increment
then controls the second jet uniformly along the whole closed segment. These
bounds estimate both the smoothing defect and the Taylor remainder in the
actual Newton residual.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set
open scoped BigOperators

set_option backward.isDefEq.respectTransparency false

section TameBounds

variable {V W : Type*} [TopologicalSpace V] [AddCommGroup V] [Module ℝ V]
  [TopologicalSpace W] [AddCommGroup W] [Module ℝ W]

private theorem diagonal_tame_estimate
    {p : ℕ → Seminorm ℝ V} {q : ℕ → Seminorm ℝ W} {J : ProjectiveJetFamily V W}
    {k b l s : ℕ} {x : V} {C : ℝ}
    (h : ∀ v : Fin k → V, q s (J k x v) ≤ C *
      ((1 + p (s + l) x) * ∏ i, p b (v i) +
        ∑ i : Fin k, p (s + l) (v i) * ∏ j ∈ Finset.univ.erase i, p b (v j)))
    (d : V) : q s (J k x (fun _ => d)) ≤ C *
      ((1 + p (s + l) x) * (p b d) ^ k +
        (k : ℝ) * (p (s + l) d * (p b d) ^ (k - 1))) := by
  have hc (i : Fin k) : ((Finset.univ : Finset (Fin k)).erase i).card = k - 1 := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ i), Finset.card_univ, Fintype.card_fin]
  simpa only [Finset.prod_const, Finset.sum_const, hc, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul] using h (fun _ => d)

omit [TopologicalSpace V] in
private theorem diagonal_tame_weaken
    {p : ℕ → Seminorm ℝ V} (hp : Monotone p)
    {k b l B L s : ℕ} {x d : V} {a c C : ℝ}
    (hb : b ≤ B) (hl : l ≤ L) (hc : 0 ≤ c) (hC : c ≤ C)
    (ha : a ≤ c * ((1 + p (s + l) x) * (p b d) ^ k +
      (k : ℝ) * (p (s + l) d * (p b d) ^ (k - 1)))) :
    a ≤ C * ((1 + p (s + L) x) * (p B d) ^ k +
      (k : ℝ) * (p (s + L) d * (p B d) ^ (k - 1))) := by
  have hbase : p b d ≤ p B d := hp hb d
  have hstate : p (s + l) x ≤ p (s + L) x := hp (Nat.add_le_add_left hl s) x
  have hdir : p (s + l) d ≤ p (s + L) d := hp (Nat.add_le_add_left hl s) d
  have hb₀ : 0 ≤ p b d := apply_nonneg _ _
  have hB₀ : 0 ≤ p B d := apply_nonneg _ _
  have hstate₀ : 0 ≤ 1 + p (s + L) x := add_nonneg zero_le_one (apply_nonneg _ _)
  have hdir₀ : 0 ≤ p (s + L) d := apply_nonneg _ _
  have hpow (n : ℕ) : (p b d) ^ n ≤ (p B d) ^ n := pow_le_pow_left₀ hb₀ hbase n
  have hk : 0 ≤ (k : ℝ) := Nat.cast_nonneg k
  have hm := add_le_add
    (mul_le_mul (add_le_add (le_refl (1 : ℝ)) hstate) (hpow k) (pow_nonneg hb₀ k) hstate₀)
    (mul_le_mul_of_nonneg_left
      (mul_le_mul hdir (hpow (k - 1)) (pow_nonneg hb₀ _) hdir₀) hk)
  have hM := add_nonneg (mul_nonneg hstate₀ (pow_nonneg hB₀ k))
    (mul_nonneg hk (mul_nonneg hdir₀ (pow_nonneg hB₀ (k - 1))))
  exact ha.trans ((mul_le_mul_of_nonneg_left hm hc).trans (mul_le_mul_of_nonneg_right hC hM))

/-- The same jet tower has first and second diagonal estimates with one base,
one loss, and one positive radius. The constants may depend on the output level. -/
theorem exists_common_newton_tame_bounds
    {p : ℕ → Seminorm ℝ V} {q : ℕ → Seminorm ℝ W} {U : Set V} {f : V → W}
    (hT : Statements.SmoothTameOn p q U f) (hp : Monotone p) {x₀ : V} (hx₀ : x₀ ∈ U) :
    ∃ J : Statements.SmoothDirections U f, ∃ b l : ℕ, ∃ ε : ℝ, 0 < ε ∧
      ∀ s : ℕ, b ≤ s → ∃ C : ℝ, 0 ≤ C ∧ ∀ x ∈ U, p b (x - x₀) < ε → ∀ d : V,
        (q s (projectiveJetHeadLinear J.D 0 x Fin.elim0 d) ≤
          C * ((1 + p (s + l) x) * p b d + p (s + l) d)) ∧
        (q s (J.D 2 x (Fin.cons d (Fin.cons d Fin.elim0))) ≤
          C * ((1 + p (s + l) x) * (p b d) ^ 2 + 2 * (p (s + l) d * p b d))) := by
  obtain ⟨J, hJ⟩ := hT
  obtain ⟨l₁, b₁, ε₁, hε₁, H₁⟩ := hJ 1 x₀ hx₀
  obtain ⟨l₂, b₂, ε₂, hε₂, H₂⟩ := hJ 2 x₀ hx₀
  let b := max b₁ b₂
  let l := max l₁ l₂
  let ε := min ε₁ ε₂
  have hb₁ : b₁ ≤ b := le_max_left _ _
  have hb₂ : b₂ ≤ b := le_max_right _ _
  have hl₁ : l₁ ≤ l := le_max_left _ _
  have hl₂ : l₂ ≤ l := le_max_right _ _
  refine ⟨J, b, l, ε, lt_min hε₁ hε₂, ?_⟩
  intro s hs
  obtain ⟨C₁, hC₁, h₁⟩ := H₁ s (hb₁.trans hs)
  obtain ⟨C₂, hC₂, h₂⟩ := H₂ s (hb₂.trans hs)
  let C := max C₁ C₂
  have hle₁ : C₁ ≤ C := le_max_left _ _
  have hle₂ : C₂ ≤ C := le_max_right _ _
  refine ⟨C, hC₁.trans hle₁, ?_⟩
  intro x hx hxlow d
  have hx₁ : p b₁ (x - x₀) < ε₁ :=
    ((hp hb₁ (x - x₀)).trans_lt hxlow).trans_le (min_le_left _ _)
  have hx₂ : p b₂ (x - x₀) < ε₂ :=
    ((hp hb₂ (x - x₀)).trans_lt hxlow).trans_le (min_le_right _ _)
  have hd₁ := diagonal_tame_estimate (p := p) (q := q) (J := J.D)
    (k := 1) (b := b₁) (l := l₁) (s := s) (h₁ x hx hx₁) d
  have hd₂ := diagonal_tame_estimate (p := p) (q := q) (J := J.D)
    (k := 2) (b := b₂) (l := l₂) (s := s) (h₂ x hx hx₂) d
  have hw₁ := diagonal_tame_weaken hp hb₁ hl₁ hC₁ hle₁ hd₁
  have hw₂ := diagonal_tame_weaken hp hb₂ hl₂ hC₂ hle₂ hd₂
  have hv₁ : Fin.cons d Fin.elim0 = (fun _ : Fin 1 => d) := by
    funext i
    fin_cases i
    rfl
  have hv₂ : Fin.cons d (Fin.cons d Fin.elim0) = (fun _ : Fin 2 => d) := by
    funext i
    fin_cases i <;> rfl
  exact ⟨by simpa [projectiveJetHeadLinear_apply, hv₁] using hw₁,
    by simpa [hv₂] using hw₂⟩

omit [TopologicalSpace V] in
private theorem seminorm_segment_le (p : Seminorm ℝ V) (x d : V)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) : p (x + t • d) ≤ p x + p d := by
  have hsmul : p (t • d) ≤ p d := by
    rw [map_smul_eq_mul, Real.norm_of_nonneg ht.1]
    exact mul_le_of_le_one_left (apply_nonneg p d) ht.2
  exact (map_add_le_add p _ _).trans (add_le_add le_rfl hsmul)

/-- A strict base-grade bound on the initial displacement and the increment
controls the actual second jet along the entire segment. -/
theorem uniform_secondJet_le_on_segment
    {p : ℕ → Seminorm ℝ V} {q : ℕ → Seminorm ℝ W} {J : ProjectiveJetFamily V W}
    {U : Set V} {b l s : ℕ} {x₀ x d : V} {ε C : ℝ} (hC : 0 ≤ C)
    (h₂ : ∀ y ∈ U, p b (y - x₀) < ε → ∀ v : V,
      q s (J 2 y (Fin.cons v (Fin.cons v Fin.elim0))) ≤
        C * ((1 + p (s + l) y) * (p b v) ^ 2 + 2 * (p (s + l) v * p b v)))
    (hseg : ∀ t ∈ Icc (0 : ℝ) 1, x + t • d ∈ U)
    (hlow : p b (x - x₀) + p b d < ε) :
    ∀ t ∈ Icc (0 : ℝ) 1, q s (J 2 (x + t • d) (Fin.cons d (Fin.cons d Fin.elim0))) ≤
      C * ((1 + p (s + l) x + p (s + l) d) * (p b d) ^ 2 +
        2 * (p (s + l) d * p b d)) := by
  intro t ht
  have hp₀ : p b ((x + t • d) - x₀) < ε := by
    rw [show (x + t • d) - x₀ = (x - x₀) + t • d by abel]
    exact (seminorm_segment_le (p b) (x - x₀) d ht).trans_lt hlow
  have hp₁ : 1 + p (s + l) (x + t • d) ≤ 1 + p (s + l) x + p (s + l) d := by
    rw [add_assoc]
    exact add_le_add le_rfl (seminorm_segment_le (p (s + l)) x d ht)
  exact (h₂ (x + t • d) (hseg t ht) hp₀ d).trans
    (mul_le_mul_of_nonneg_left
      (add_le_add (mul_le_mul_of_nonneg_right hp₁ (sq_nonneg _)) le_rfl) hC)

end TameBounds

/-- The fixed-parameter smoothed step has a residual bound with a tame
first-jet defect and a tame second-jet remainder on the same base neighborhood. -/
theorem projectiveSmoothedNewtonStep_tame_residual_le
    {X : Type*} [TopologicalSpace X] [AddCommGroup X] [Module ℝ X]
    [IsTopologicalAddGroup X] [ContinuousSMul ℝ X]
    {F : ℕ → Type*} [∀ n, NormedAddCommGroup (F n)] [∀ n, NormedSpace ℝ (F n)]
    {bond : ∀ n, F (n + 1) →L[ℝ] F n} {f : X × ℝ → ProjectiveLimit F bond}
    {U : Set (X × ℝ)} (J : Statements.SmoothDirections U f)
    (p : ℕ → Seminorm ℝ (X × ℝ)) (z₀ z : X × ℝ) (b l s : ℕ) (ε C : ℝ) (hC : 0 ≤ C)
    (hjet : ∀ x ∈ U, p b (x - z₀) < ε → ∀ d : X × ℝ,
      (gradedSeminorm F bond s (projectiveJetHeadLinear J.D 0 x Fin.elim0 d) ≤
        C * ((1 + p (s + l) x) * p b d + p (s + l) d)) ∧
      (gradedSeminorm F bond s (J.D 2 x (Fin.cons d (Fin.cons d Fin.elim0))) ≤
        C * ((1 + p (s + l) x) * (p b d) ^ 2 + 2 * (p (s + l) d * p b d))))
    (V₀ : ProjectiveLimit F bond →ₗ[ℝ] X)
    (Q : ProjectiveLimit F bond →ₗ[ℝ] ProjectiveLimit F bond →ₗ[ℝ] ProjectiveLimit F bond)
    (hV : ∀ y, HasProjectiveLineDerivAt (fun x => f (x, z.2))
      (y + Q (f z) y) z.1 (V₀ y))
    (S : X →L[ℝ] X) :
    let d : X × ℝ := (-S (V₀ (f z)), 0)
    let e : X × ℝ := (V₀ (f z) - S (V₀ (f z)), 0)
    (∀ t ∈ Icc (0 : ℝ) 1, z + t • d ∈ U) →
    p b (z - z₀) + p b d < ε →
    gradedSeminorm F bond s (f (z.1 - S (V₀ (f z)), z.2)) ≤
      gradedSeminorm F bond s (Q (f z) (f z)) + C * ((1 + p (s + l) z) * p b e + p (s + l) e) +
      (C * ((1 + p (s + l) z + p (s + l) d) * (p b d) ^ 2 +
        2 * (p (s + l) d * p b d))) / 2 := by
  dsimp only
  intro hseg hlow
  let d : X × ℝ := (-S (V₀ (f z)), 0)
  let e : X × ℝ := (V₀ (f z) - S (V₀ (f z)), 0)
  have hJ : HasProjectiveJetsOn f J.D U :=
    ⟨J.zero, J.continuous, fun n x hx v vs => J.derivative n x hx vs v⟩
  have hM := uniform_secondJet_le_on_segment (p := p) (q := gradedSeminorm F bond)
    (J := J.D) (x := z) (d := d) (l := l) (s := s) hC
    (fun x hx hsmall v => (hjet x hx hsmall v).2) hseg hlow
  have hstep := projectiveSmoothedNewtonStep_residual_le J.open_domain hJ z V₀ Q hV S s hseg hM
  have hz : z ∈ U := by
    simpa only [zero_smul, add_zero] using hseg 0 ⟨le_rfl, zero_le_one⟩
  have hsmall : p b (z - z₀) < ε :=
    (le_add_of_nonneg_right (apply_nonneg (p b) d)).trans_lt hlow
  have hdefect := (hjet z hz hsmall e).1
  exact hstep.trans (add_le_add (add_le_add le_rfl hdefect) le_rfl)

end ContinuousFlexibility.Analysis
