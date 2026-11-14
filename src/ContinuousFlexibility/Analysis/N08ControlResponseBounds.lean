module

public import ContinuousFlexibility.Analysis.N08ControlColumnExtraction

/-!
# Composing a smoothing control column with the existing scalar inverse

The low source seminorm is uniformly bounded on one stronger state ball.
Consequently the inverse-family estimate retains one high state factor,
instead of multiplying two such factors. The result includes every output
order, including those below the base of the inverse estimate.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Statements

open Set ContinuousFlexibility.Analysis

section Generic

variable {X F Y B : Type*}
  [TopologicalSpace X] [AddCommGroup X] [Module ℝ X]
  [TopologicalSpace F] [AddCommGroup F] [Module ℝ F]
  [TopologicalSpace Y] [AddCommGroup Y] [Module ℝ Y]
  [NormedAddCommGroup B]
  {p : ℕ → Seminorm ℝ X} {q : ℕ → Seminorm ℝ F} {r : ℕ → Seminorm ℝ Y}
  {U : Set X} {G : X → F →ₗ[ℝ] Y} {H : X → B → F} {columnLoss : ℕ}

theorem n08_controlResponse_bound
    (hp : Monotone p) (hr : Monotone r)
    (hG : LinearFamilyTame p r q U G)
    (hH : ∀ s : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ x ∈ U, ∀ b : B,
      q s (H x b) ≤ C * (1 + p (s + columnLoss) x) * ‖b‖) :
    ∃ base loss : ℕ, ∀ s : ℕ, ∃ C : ℝ, 0 < C ∧
      ∀ x ∈ U, p base x < 1 → ∀ b : B,
        q s (H x b) + r s (G x (H x b)) ≤
          C * (1 + p (s + loss) x) * ‖b‖ := by
  obtain ⟨inverseLoss, inverseBase, hGb⟩ := hG
  obtain ⟨Cbase, hCbase, hbaseBound⟩ := hH inverseBase
  refine ⟨inverseBase + columnLoss, inverseBase + inverseLoss + columnLoss, ?_⟩
  intro s
  let t := max s inverseBase
  obtain ⟨Csource, hCsource, hsourceBound⟩ := hH s
  obtain ⟨Chigh, hChigh, hhighBound⟩ := hH (t + inverseLoss)
  obtain ⟨Cinv, hCinv, hinverseBound⟩ := hGb t (le_max_right _ _)
  let K := Csource + Cinv * (Chigh + 2 * Cbase)
  have hK : 0 ≤ K := by dsimp only [K]; positivity
  refine ⟨K + 1, by linarith, fun x hx hsmall b => ?_⟩
  let A := 1 + p (s + (inverseBase + inverseLoss + columnLoss)) x
  have hA : 0 ≤ A := add_nonneg zero_le_one (apply_nonneg _ _)
  have hnorm : 0 ≤ ‖b‖ := norm_nonneg b
  have hs : s + columnLoss ≤ s + (inverseBase + inverseLoss + columnLoss) := by omega
  have ht : t + inverseLoss + columnLoss ≤ s + (inverseBase + inverseLoss + columnLoss) := by
    dsimp only [t]
    omega
  have ht' : t + inverseLoss ≤ s + (inverseBase + inverseLoss + columnLoss) := by omega
  have hsA : 1 + p (s + columnLoss) x ≤ A :=
    add_le_add (le_refl 1) (hp hs x)
  have htA : 1 + p (t + inverseLoss + columnLoss) x ≤ A :=
    add_le_add (le_refl 1) (hp ht x)
  have htA' : 1 + p (t + inverseLoss) x ≤ A :=
    add_le_add (le_refl 1) (hp ht' x)
  have hlowA : 1 + p (inverseBase + columnLoss) x ≤ 2 := by linarith
  have hsource : q s (H x b) ≤ Csource * A * ‖b‖ :=
    (hsourceBound x hx b).trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hsA hCsource) hnorm)
  have hhigh : q (t + inverseLoss) (H x b) ≤ Chigh * A * ‖b‖ :=
    (hhighBound x hx b).trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left htA hChigh) hnorm)
  have hlow : q inverseBase (H x b) ≤ (2 * Cbase) * ‖b‖ := by
    calc
      _ ≤ Cbase * (1 + p (inverseBase + columnLoss) x) * ‖b‖ := hbaseBound x hx b
      _ ≤ Cbase * 2 * ‖b‖ := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hlowA hCbase) hnorm
      _ = _ := by ring
  have hproduct : (1 + p (t + inverseLoss) x) * q inverseBase (H x b) ≤
      A * ((2 * Cbase) * ‖b‖) :=
    mul_le_mul htA' hlow (apply_nonneg _ _) hA
  have hinv : r s (G x (H x b)) ≤ Cinv * (Chigh + 2 * Cbase) * A * ‖b‖ := by
    calc
      _ ≤ r t (G x (H x b)) := hr (le_max_left _ _) _
      _ ≤ Cinv * (q (t + inverseLoss) (H x b) +
          (1 + p (t + inverseLoss) x) * q inverseBase (H x b)) := hinverseBound x hx _
      _ ≤ Cinv * (Chigh * A * ‖b‖ + A * ((2 * Cbase) * ‖b‖)) :=
        mul_le_mul_of_nonneg_left (add_le_add hhigh hproduct) hCinv
      _ = _ := by ring
  calc
    _ ≤ Csource * A * ‖b‖ + Cinv * (Chigh + 2 * Cbase) * A * ‖b‖ :=
      add_le_add hsource hinv
    _ = K * A * ‖b‖ := by dsimp only [K]; ring
    _ ≤ (K + 1) * A * ‖b‖ := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (by linarith : K ≤ K + 1) hA) hnorm

end Generic

end ContinuousFlexibility.Statements
