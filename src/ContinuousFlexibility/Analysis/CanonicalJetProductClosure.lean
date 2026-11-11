import ContinuousFlexibility.Analysis.CanonicalStateInterpolation

/-!
# Fixed-loss closure of numerical jet products

A fixed shift in the input grading does not grow with the number of
factors. Interpolation reduces every product whose total derivative
order is at most s to one high seminorm on one common low neighborhood.
The factors may include a constant term, as actual coordinate jets do.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open ContinuousFlexibility.Statements
open scoped BigOperators

set_option backward.isDefEq.respectTransparency false

/-- Translating all grading indices preserves interpolation. -/
theorem coordinate_hasInterpolation_shift
    {E : Type*} [AddCommGroup E] [Module ℝ E]
    {p : ℕ → Seminorm ℝ E} (hI : HasInterpolation p) (d : ℕ) :
    HasInterpolation (fun n => p (n + d)) := by
  obtain ⟨base, loss, hI⟩ := hI
  refine ⟨base, loss, ?_⟩
  intro a b c ha hab hbc
  obtain ⟨C, hC, hbound⟩ := hI (a + d) (b + d) (c + d)
    (by omega) (by omega) (by omega)
  refine ⟨C, hC, ?_⟩
  intro x
  have hac : ((c + d : ℕ) : ℝ) - (a + d : ℕ) = (c : ℝ) - a := by
    push_cast
    ring
  have hcb : ((c + d : ℕ) : ℝ) - (b + d : ℕ) = (c : ℝ) - b := by
    push_cast
    ring
  have hba : ((b + d : ℕ) : ℝ) - (a + d : ℕ) = (b : ℝ) - a := by
    push_cast
    ring
  simpa only [hac, hcb, hba] using hbound x

/-- One base and one loss control all numerical jet products, including
constant terms, on the same low-seminorm unit neighborhood. -/
theorem coordinate_jet_product_le_one_high_of_low
    {E : Type} [AddCommGroup E] [Module ℝ E]
    {p : ℕ → Seminorm ℝ E} (hp : Monotone p) (hI : HasInterpolation p)
    (offset : ℕ) :
    ∃ base loss : ℕ, ∀ {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι],
      ∀ (order : ι → ℕ) (s : ℕ), (∑ i, order i) ≤ s →
        ∃ C : ℝ, 0 ≤ C ∧ ∀ x : E, p base x ≤ 1 →
          (∏ i, (1 + p (order i + offset) x)) ≤ C * (1 + p (s + loss) x) := by
  let q : ℕ → Seminorm ℝ (E × ℝ) :=
    fun n => pairGrading p realGrading (n + offset)
  have hRm : Monotone realGrading := fun _ _ _ => le_rfl
  have hq : Monotone q := fun i j hij =>
    tamePairGrading_monotone hp hRm (Nat.add_le_add_right hij offset)
  have hIq : HasInterpolation q :=
    coordinate_hasInterpolation_shift
      (coordinate_hasInterpolation_pair hp hRm hI coordinate_hasInterpolation_realGrading) offset
  obtain ⟨b, l, hprod⟩ := spaces_interpolation_product_bound q
    (fun x _ _ h => hq h x) hIq
  refine ⟨b + offset, l + offset, ?_⟩
  intro ι _ _ _ order s horder
  obtain ⟨C, hC, hbound⟩ := hprod order s horder
  let R : ℝ := ∑ i : ι, ∏ j ∈ Finset.univ.erase i, (2 : ℝ)
  have hR : 0 ≤ R := by positivity
  refine ⟨C * R, mul_nonneg hC hR, ?_⟩
  intro x hx
  let w : E × ℝ := (x, 1)
  have hqval (n : ℕ) : q n w = p (n + offset) x + 1 := by
    simp only [q, w, pairGrading_apply, realGrading, coe_normSeminorm, norm_one]
  have hlow : q b w ≤ 2 := by rw [hqval]; linarith only [hx]
  have hhigh : 0 ≤ q (s + l) w := apply_nonneg _ _
  have hstart :
      (∏ i, (1 + p (order i + offset) x)) ≤ ∏ i, q (order i + 2) w := by
    apply Finset.prod_le_prod
    · intro i _
      exact add_nonneg zero_le_one (apply_nonneg _ _)
    · intro i _
      rw [hqval]
      have hi := hp (show order i + offset ≤ order i + 2 + offset by omega) x
      linarith only [hi]
  have hlower (i : ι) :
      (∏ j ∈ Finset.univ.erase i, q b w) ≤
        ∏ j ∈ Finset.univ.erase i, (2 : ℝ) := by
    exact Finset.prod_le_prod (fun _ _ => apply_nonneg _ _) (fun _ _ => hlow)
  calc
    _ ≤ ∏ i, q (order i + 2) w := hstart
    _ ≤ C * ∑ i, q (s + l) w * ∏ j ∈ Finset.univ.erase i, q b w :=
      hbound (fun _ => w)
    _ ≤ C * ∑ i, q (s + l) w * ∏ j ∈ Finset.univ.erase i, (2 : ℝ) :=
      mul_le_mul_of_nonneg_left
        (Finset.sum_le_sum (fun i _ => mul_le_mul_of_nonneg_left (hlower i) hhigh)) hC
    _ = C * R * (1 + p (s + (l + offset)) x) := by
      rw [← Finset.mul_sum, hqval]
      simp only [Nat.add_assoc]
      dsimp only [R]
      ring

/-- Actual nonlinear coordinate jets use the physical state grading. -/
theorem coordinate_state_product_le_one_high_of_low
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    (hS : IsPhysicalSpaces D T S) (offset : ℕ) :
    ∃ base loss : ℕ, ∀ {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι],
      ∀ (order : ι → ℕ) (s : ℕ), (∑ i, order i) ≤ s →
        ∃ C : ℝ, 0 ≤ C ∧ ∀ x : AnnularState S, stateGrading S base x ≤ 1 →
          (∏ i, (1 + stateGrading S (order i + offset) x)) ≤
            C * (1 + stateGrading S (s + loss) x) :=
  coordinate_jet_product_le_one_high_of_low (stateGrading_monotone S)
    (coordinate_hasInterpolation_stateGrading hS) offset

end ContinuousFlexibility.Analysis
