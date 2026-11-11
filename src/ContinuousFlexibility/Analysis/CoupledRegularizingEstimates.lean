import ContinuousFlexibility.Analysis.CoupledUniformLinearFamily

/-!
# Estimates for control smoothing and the recovered inverse

A fixed-loss row composed with an all-order smoothing control column is
again regularizing when its one low parameter seminorm is bounded. The
control Banach estimate then supplies a tame bound for the recovered
constant-circle inverse at every order on the same neighborhood.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set
open ContinuousFlexibility.Statements

section Regularizing

variable {X Y Z Uc : Type*}
  [AddCommGroup X] [Module ℝ X] [AddCommGroup Y] [Module ℝ Y]
  [AddCommGroup Z] [Module ℝ Z] [NormedAddCommGroup Uc] [NormedSpace ℝ Uc]

theorem coupled_regularizing_composition_bound
    {p : ℕ → Seminorm ℝ X} {q : ℕ → Seminorm ℝ Y} {r : ℕ → Seminorm ℝ Z}
    (hp : Monotone p) {U : Set X} {A : X → Y →ₗ[ℝ] Z} {H : X → Uc →ₗ[ℝ] Y}
    {lossA lossH b : ℕ} {M : ℝ} (hM : 0 ≤ M)
    (hA : ∀ s, b ≤ s → ∃ c : ℝ, 0 ≤ c ∧ ∀ x ∈ U, ∀ y,
      r s (A x y) ≤ c * (q (s + lossA) y + (1 + p (s + lossA) x) * q b y))
    (hH : ∀ s, ∃ c : ℝ, 0 ≤ c ∧ ∀ x ∈ U, ∀ u,
      q s (H x u) ≤ c * (1 + p (s + lossH) x) * ‖u‖)
    (hlow : ∀ x ∈ U, p (b + lossH) x ≤ M) :
    ∀ s, b ≤ s → ∃ c : ℝ, 0 ≤ c ∧ ∀ x ∈ U, ∀ u,
      r s (A x (H x u)) ≤ c * (1 + p (s + (lossA + lossH)) x) * ‖u‖ := by
  intro s hs
  obtain ⟨cA, hcA, hAs⟩ := hA s hs
  obtain ⟨cH, hcH, hHs⟩ := hH (s + lossA)
  obtain ⟨cB, hcB, hHb⟩ := hH b
  refine ⟨cA * (cH + cB * (1 + M)), by positivity, fun x hx u => ?_⟩
  have hhigh : q (s + lossA) (H x u) ≤
      cH * (1 + p (s + (lossA + lossH)) x) * ‖u‖ := by
    simpa only [Nat.add_assoc] using hHs x hx u
  have hbase : q b (H x u) ≤ cB * (1 + M) * ‖u‖ :=
    (hHb x hx u).trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (add_le_add_left (hlow x hx) 1) hcB) (norm_nonneg _))
  have hparam : 1 + p (s + lossA) x ≤ 1 + p (s + (lossA + lossH)) x :=
    add_le_add_left (hp (by omega) x) 1
  have hparam0 : 0 ≤ 1 + p (s + (lossA + lossH)) x := by positivity
  calc
    r s (A x (H x u)) ≤ cA * (q (s + lossA) (H x u) +
        (1 + p (s + lossA) x) * q b (H x u)) := hAs x hx _
    _ ≤ cA * (cH * (1 + p (s + (lossA + lossH)) x) * ‖u‖ +
        (1 + p (s + (lossA + lossH)) x) * (cB * (1 + M) * ‖u‖)) :=
      mul_le_mul_of_nonneg_left (add_le_add hhigh
        (mul_le_mul hparam hbase (apply_nonneg _ _) hparam0)) hcA
    _ = cA * (cH + cB * (1 + M)) *
        (1 + p (s + (lossA + lossH)) x) * ‖u‖ := by ring

end Regularizing

section InverseBound

variable {X Y Uc : Type*}
  [TopologicalSpace X] [AddCommGroup X] [Module ℝ X]
  [TopologicalSpace Y] [AddCommGroup Y] [Module ℝ Y]
  [NormedAddCommGroup Uc] [NormedSpace ℝ Uc]

theorem coupled_inverseFamily_tame_of_regularizing_recovery
    {p : ℕ → Seminorm ℝ X} {q : ℕ → Seminorm ℝ Y}
    (hq : Monotone q) {U : Set X} {V : X → Y →ₗ[ℝ] Y}
    {control : X → Y → Uc} {response : X → Uc → Y}
    {loss b b0 : ℕ} {K : ℝ} (hK : 0 ≤ K)
    (hcontrol : ∀ x ∈ U, ∀ y, ‖control x y‖ ≤ K * q b0 y)
    (hrecovery : ∀ x ∈ U, ∀ y s,
      q s (V x y) ≤ 2 * q s y + 2 * q s (response x (control x y)))
    (hresponse : ∀ s, b ≤ s → ∃ c : ℝ, 0 ≤ c ∧ ∀ x ∈ U, ∀ u,
      q s (response x u) ≤ c * (1 + p (s + loss) x) * ‖u‖) :
    LinearFamilyTame p q q U V := by
  refine ⟨loss, max b b0, fun s hs => ?_⟩
  obtain ⟨c, hc, hcBound⟩ := hresponse s (le_of_max_le_left hs)
  refine ⟨2 + 2 * c * K, by positivity, fun x hx y => ?_⟩
  have hlow : ‖control x y‖ ≤ K * q (max b b0) y :=
    (hcontrol x hx y).trans
      (mul_le_mul_of_nonneg_left (hq (le_max_right _ _) y) hK)
  have hresp : q s (response x (control x y)) ≤
      c * (1 + p (s + loss) x) * (K * q (max b b0) y) :=
    (hcBound x hx _).trans (mul_le_mul_of_nonneg_left hlow (by positivity))
  have hhigh : q s y ≤ q (s + loss) y := hq (Nat.le_add_right _ _) y
  have ha : 0 ≤ q (s + loss) y := apply_nonneg _ _
  have hb : 0 ≤ (1 + p (s + loss) x) * q (max b b0) y := by positivity
  calc
    q s (V x y) ≤ 2 * q s y + 2 * q s (response x (control x y)) :=
      hrecovery x hx y s
    _ ≤ 2 * q (s + loss) y +
        2 * (c * (1 + p (s + loss) x) * (K * q (max b b0) y)) :=
      add_le_add (mul_le_mul_of_nonneg_left hhigh (by norm_num))
        (mul_le_mul_of_nonneg_left hresp (by norm_num))
    _ ≤ (2 + 2 * c * K) *
        (q (s + loss) y + (1 + p (s + loss) x) * q (max b b0) y) := by
      nlinarith only [mul_nonneg (mul_nonneg hc hK) ha, hb]

end InverseBound

end ContinuousFlexibility.Analysis
