import ContinuousFlexibility.Scalar.WeightedAngularJetProduct
import ContinuousFlexibility.Scalar.WeightedProductTower

/-!
# One-high-factor estimates for two odd angular jets

The actual product of first angular derivatives is represented through the
second derivative product rule. Each application of the second derivative
costs two orders. Enlarging the common low order by two and the common loss
by two controls all three terms with one high input.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open ContinuousFlexibility.Analysis
open scoped BigOperators

set_option backward.isDefEq.respectTransparency false

section Seminorm

variable {E : Type*} [AddCommGroup E] [Module ℝ E]

private theorem seminorm_half_two_sub_le
    (p : Seminorm ℝ E) (a b c : E) :
    p ((1 / 2 : ℝ) • (a - b - c)) ≤ p a + p b + p c := by
  calc
    _ = (1 / 2 : ℝ) * p (a - b - c) := by
      rw [map_smul_eq_mul]
      norm_num
    _ ≤ p (a - b - c) := by nlinarith [apply_nonneg p (a - b - c)]
    _ ≤ p (a - b) + p c := map_sub_le_add _ _ _
    _ ≤ p a + p b + p c := add_le_add (map_sub_le_add _ _ _) (le_refl _)

/-- The second derivative product identity preserves a one-high estimate,
with two additional fixed orders in its base and loss. -/
private theorem oneHigh_secondDerivative_product
    {p : ℕ → Seminorm ℝ E} (hp : Monotone p) (L : E → E) (M : E → E → E)
    {base loss : ℕ}
    (hL : ∀ s : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ x, p s (L x) ≤ C * p (s + 2) x)
    (hM : ∀ s : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ x y,
      p s (M x y) ≤ C * (p (s + loss) x * p base y + p base x * p (s + loss) y)) :
    ∀ s : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ x y,
      p s ((1 / 2 : ℝ) • (L (M x y) - M (L x) y - M x (L y))) ≤
        C * (p (s + (loss + 2)) x * p (base + 2) y +
          p (base + 2) x * p (s + (loss + 2)) y) := by
  intro s
  obtain ⟨C, hC, hCs⟩ := hM s
  obtain ⟨C₂, hC₂, hC₂s⟩ := hM (s + 2)
  obtain ⟨A, hA, hAs⟩ := hL s
  obtain ⟨B, hB, hBs⟩ := hL (s + loss)
  obtain ⟨Q, hQ, hQs⟩ := hL base
  let K : ℝ := B + Q
  have hK : 0 ≤ K := add_nonneg hB hQ
  have hBK : B ≤ K := le_add_of_nonneg_right hQ
  have hQK : Q ≤ K := le_add_of_nonneg_left hB
  refine ⟨A * C₂ + 2 * (C * K), by positivity, ?_⟩
  intro x y
  let N : ℝ := p (s + (loss + 2)) x * p (base + 2) y +
    p (base + 2) x * p (s + (loss + 2)) y
  have hlo (z : E) : p base z ≤ p (base + 2) z := hp (by omega) z
  have hhi (z : E) : p (s + loss) z ≤ p (s + (loss + 2)) z := hp (by omega) z
  have hDh (z : E) : p (s + loss) (L z) ≤ K * p (s + (loss + 2)) z := by
    have hb : p (s + loss) (L z) ≤ B * p (s + (loss + 2)) z := by
      simpa only [Nat.add_assoc] using hBs z
    exact hb.trans (mul_le_mul_of_nonneg_right hBK (apply_nonneg _ _))
  have hDl (z : E) : p base (L z) ≤ K * p (base + 2) z :=
    (hQs z).trans (mul_le_mul_of_nonneg_right hQK (apply_nonneg _ _))
  have hM₂ : p (s + 2) (M x y) ≤ C₂ * N := by
    have hidx : s + 2 + loss = s + (loss + 2) := by omega
    have hm := hC₂s x y
    rw [hidx] at hm
    apply hm.trans
    apply mul_le_mul_of_nonneg_left _ hC₂
    exact add_le_add
      (mul_le_mul_of_nonneg_left (hlo y) (apply_nonneg _ _))
      (mul_le_mul_of_nonneg_right (hlo x) (apply_nonneg _ _))
  have houter : p s (L (M x y)) ≤ (A * C₂) * N :=
    ((hAs (M x y)).trans (mul_le_mul_of_nonneg_left hM₂ hA)).trans_eq (by ring)
  have hleft : p s (M (L x) y) ≤ (C * K) * N := by
    apply (hCs (L x) y).trans
    calc
      _ ≤ C * ((K * p (s + (loss + 2)) x) * p (base + 2) y +
          (K * p (base + 2) x) * p (s + (loss + 2)) y) :=
        mul_le_mul_of_nonneg_left
          (add_le_add
            (mul_le_mul (hDh x) (hlo y) (apply_nonneg _ _)
              (mul_nonneg hK (apply_nonneg _ _)))
            (mul_le_mul (hDl x) (hhi y) (apply_nonneg _ _)
              (mul_nonneg hK (apply_nonneg _ _)))) hC
      _ = _ := by dsimp only [N]; ring
  have hright : p s (M x (L y)) ≤ (C * K) * N := by
    apply (hCs x (L y)).trans
    calc
      _ ≤ C * (p (s + (loss + 2)) x * (K * p (base + 2) y) +
          p (base + 2) x * (K * p (s + (loss + 2)) y)) :=
        mul_le_mul_of_nonneg_left
          (add_le_add
            (mul_le_mul (hhi x) (hDl y) (apply_nonneg _ _) (apply_nonneg _ _))
            (mul_le_mul (hlo x) (hDh y) (apply_nonneg _ _) (apply_nonneg _ _))) hC
      _ = _ := by dsimp only [N]; ring
  exact ((seminorm_half_two_sub_le (p s) _ _ _).trans
    (add_le_add (add_le_add houter hleft) hright)).trans_eq (by
      dsimp only [N]
      ring)

end Seminorm

namespace SobolevModelData

variable {D : ReferenceData} {T : MaterialData} {γ : ℝ} {A : SobolevModelData}

/-- An actual fixed-loss estimate for the genuine even product of two
odd angular derivatives. The base and loss are chosen before the order. -/
theorem angularJetProductMap_oneHigh
    (hT : IsMaterialData D T) (hA : IsSobolevModel D T γ A)
    (hinterp : HasInterpolation A.grading) (hγ : 0 ≤ γ) :
    ∃ base loss : ℕ, 2 ≤ base ∧ ∀ s : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ x y : A.Space,
      A.grading s (angularJetProductMap hT hA hinterp hγ ![x, y]) ≤
        C * (A.grading (s + loss) x * A.grading base y +
          A.grading base x * A.grading (s + loss) y) := by
  classical
  obtain ⟨base, loss, hbase, hproduct⟩ := decodedProductMap_oneHigh hT hA hinterp hγ
  let L := angularSecondCLM hT hA
  let M := decodedProductMap hT hA hinterp hγ 1
  have hL : ∀ s : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ x : A.Space,
      A.grading s (L x) ≤ C * A.grading (s + 2) x := by
    intro s
    obtain ⟨C, hCx⟩ := angularSecondCLM_isTame hT hA s (Nat.zero_le s)
    exact ⟨C, C.coe_nonneg, hCx⟩
  have hM : ∀ s : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ x y : A.Space,
      A.grading s (M ![x, y]) ≤ C *
        (A.grading (s + loss) x * A.grading base y +
          A.grading base x * A.grading (s + loss) y) := by
    intro s
    obtain ⟨C, hC, hCu⟩ := hproduct 1 s
    refine ⟨C, hC, fun x y => ?_⟩
    rw [← oneHigh_fin_two (A.grading base) (A.grading (s + loss)) x y]
    exact hCu ![x, y]
  refine ⟨base + 2, loss + 2, by omega, ?_⟩
  intro s
  obtain ⟨C, hC, hCxy⟩ := oneHigh_secondDerivative_product
    (gradedSeminorm_monotone (fun n => A.level n) A.bond) L
    (fun x y => M ![x, y]) hL hM s
  refine ⟨C, hC, fun x y => ?_⟩
  rw [angularJetProductMap_apply]
  exact hCxy x y

end SobolevModelData

end ContinuousFlexibility.Statements
