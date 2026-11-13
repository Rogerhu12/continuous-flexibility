import ContinuousFlexibility.Analysis.N04PulledFieldsFixedBaseComposition
import ContinuousFlexibility.Analysis.CircleProductSmoothTame

/-!
# Fixed-base multiplication of the actual circle fields

The quadratic tower has exactly two nonzero derivative orders above its
value. Its original bilinear one-high bound therefore controls every
parameter order on the same low box. No parameter-dependent low base is
introduced when this operation is used in the correction formulas.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set ContinuousFlexibility.Statements
open scoped BigOperators

set_option backward.isDefEq.respectTransparency false

private theorem n04PulledFields_tameJetSize_two
    {E : Type*} [AddCommGroup E] [Module ℝ E]
    (p : ℕ → Seminorm ℝ E) (s loss base : ℕ) (x : E) (v : Fin 2 → E) :
    tameJetSize p 2 s loss base x v =
      (1 + p (s + loss) x) * (p base (v 0) * p base (v 1)) +
        (p (s + loss) (v 0) * p base (v 1) + p (s + loss) (v 1) * p base (v 0)) := by
  have h0 : (Finset.univ : Finset (Fin 2)).erase 0 = {1} := by decide
  have h1 : (Finset.univ : Finset (Fin 2)).erase 1 = {0} := by decide
  simp only [tameJetSize, Fin.prod_univ_two, Fin.sum_univ_two, h0, h1, Finset.prod_singleton]

/-- All orders of the genuine quadratic family use the given low base. -/
theorem n04PulledFields_fixedBaseFamily_quadratic
    {I E F : Type*}
    [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
    [TopologicalSpace F] [AddCommGroup F] [Module ℝ F]
    [IsTopologicalAddGroup F] [ContinuousSMul ℝ F]
    (p : ℕ → Seminorm ℝ E) (q : ℕ → Seminorm ℝ F)
    (B : E [×2]→L[ℝ] F) (base loss : ℕ)
    (hB : ∀ s, ∃ C : ℝ, 0 ≤ C ∧ ∀ x y,
      q s (bilinearJetValue B x y) ≤
        C * (p (s + loss) x * p base y + p base x * p (s + loss) y)) :
    N04PulledFieldsFixedBaseFamily p q univ (fun _ : I => quadraticJetValue B) := by
  refine ⟨fun _ => smoothDirectionsOfJets isOpen_univ (quadraticJets B)
    (hasProjectiveJetsOn_quadratic B univ), base, fun _ => loss, fun n R hR s => ?_⟩
  obtain ⟨C, hC, hbound⟩ := hB s
  let M : ℝ := max R 1
  have hM : 1 ≤ M := le_max_right _ _
  have hM0 : 0 ≤ M := zero_le_one.trans hM
  refine ⟨2 * C * M, by positivity, fun _ x _ hbx v => ?_⟩
  have hx : p base x ≤ M := hbx.trans (le_max_left _ _)
  have ha : 0 ≤ p (s + loss) x := apply_nonneg _ _
  change q s (quadraticJets B n x v) ≤ 2 * C * M * tameJetSize p n s loss base x v
  cases n with
  | zero =>
      rw [tameJetSize_zero]
      change q s (bilinearJetValue B x x) ≤ _
      calc
        _ ≤ C * (p (s + loss) x * p base x + p base x * p (s + loss) x) := hbound x x
        _ ≤ C * (p (s + loss) x * M + M * p (s + loss) x) :=
          mul_le_mul_of_nonneg_left
            (add_le_add (mul_le_mul_of_nonneg_left hx ha)
              (mul_le_mul_of_nonneg_right hx ha)) hC
        _ = (2 * C * M) * p (s + loss) x := by ring
        _ ≤ (2 * C * M) * (1 + p (s + loss) x) :=
          mul_le_mul_of_nonneg_left (le_add_of_nonneg_left zero_le_one) (by positivity)
  | succ n =>
      cases n with
      | zero =>
          rw [tameJetSize_one]
          change q s (quadraticJetFirst B x (v 0)) ≤ _
          rw [quadraticJetFirst_apply]
          have hv0 : 0 ≤ p (s + loss) (v 0) := apply_nonneg _ _
          have hvl : 0 ≤ p base (v 0) := apply_nonneg _ _
          have hax : p (s + loss) x ≤ M * (1 + p (s + loss) x) :=
            (le_add_of_nonneg_left zero_le_one).trans
              (by simpa only [one_mul] using
                mul_le_mul_of_nonneg_right hM (add_nonneg zero_le_one ha))
          calc
            _ ≤ q s (bilinearJetValue B (v 0) x) + q s (bilinearJetValue B x (v 0)) :=
              map_add_le_add _ _ _
            _ ≤ C * (p (s + loss) (v 0) * p base x + p base (v 0) * p (s + loss) x) +
                C * (p (s + loss) x * p base (v 0) + p base x * p (s + loss) (v 0)) :=
              add_le_add (hbound (v 0) x) (hbound x (v 0))
            _ = 2 * C * (p (s + loss) (v 0) * p base x + p (s + loss) x * p base (v 0)) :=
              by ring
            _ ≤ 2 * C * (p (s + loss) (v 0) * M +
                (M * (1 + p (s + loss) x)) * p base (v 0)) :=
              mul_le_mul_of_nonneg_left
                (add_le_add (mul_le_mul_of_nonneg_left hx hv0)
                  (mul_le_mul_of_nonneg_right hax hvl)) (by positivity)
            _ = _ := by ring
      | succ n =>
          cases n with
          | zero =>
              rw [n04PulledFields_tameJetSize_two]
              change q s (quadraticJetSecond B v) ≤ _
              rw [quadraticJetSecond_apply]
              let A : ℝ := p (s + loss) (v 0) * p base (v 1) +
                p (s + loss) (v 1) * p base (v 0)
              have hA : 0 ≤ A := by dsimp only [A]; positivity
              have hrest : 0 ≤ (1 + p (s + loss) x) * (p base (v 0) * p base (v 1)) :=
                by positivity
              calc
                _ ≤ q s (bilinearJetValue B (v 0) (v 1)) +
                    q s (bilinearJetValue B (v 1) (v 0)) := map_add_le_add _ _ _
                _ ≤ C * (p (s + loss) (v 0) * p base (v 1) +
                    p base (v 0) * p (s + loss) (v 1)) +
                    C * (p (s + loss) (v 1) * p base (v 0) +
                    p base (v 1) * p (s + loss) (v 0)) :=
                  add_le_add (hbound (v 0) (v 1)) (hbound (v 1) (v 0))
                _ = 2 * C * A := by dsimp only [A]; ring
                _ ≤ 2 * C * (M * A) := mul_le_mul_of_nonneg_left
                  (by simpa only [one_mul] using mul_le_mul_of_nonneg_right hM hA) (by positivity)
                _ ≤ 2 * C * M *
                    ((1 + p (s + loss) x) * (p base (v 0) * p base (v 1)) + A) := by
                  rw [← mul_assoc]
                  exact mul_le_mul_of_nonneg_left (le_add_of_nonneg_left hrest) (by positivity)
          | succ n =>
              change q s 0 ≤ 2 * C * M * tameJetSize p (n + 3) s loss base x v
              rw [map_zero]
              exact mul_nonneg (by positivity) (tameJetSize_nonneg _ _ _ _ _ _ _)

end ContinuousFlexibility.Analysis

namespace ContinuousFlexibility.Statements

open Set ContinuousFlexibility.Analysis

set_option backward.isDefEq.respectTransparency false

variable {I : Type*} {D : ReferenceData} {T : MaterialData} {γ : ℝ} {M : CircleModelData}
  (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T)
  (hγ : 0 < γ) (hM : IsCircleModel T γ M) (hI : HasInterpolation M.grading)

include hI

theorem n04PulledFields_fixedBase_circleProduct :
    N04PulledFieldsFixedBaseFamily (pairGrading M.grading M.grading) M.grading univ
      (fun (_ : I) x => circleProductBilinear hM hT hD hγ x.1 x.2) := by
  let data := circleProduct_oneHigh_bound hM hT hD hγ hI
  let B := circleProductPairMultilinear hM hT hD hγ
  have hB : ∀ s, ∃ C : ℝ, 0 ≤ C ∧ ∀ x y : M.Space × M.Space,
      M.grading s (bilinearJetValue B x y) ≤ C *
        (pairGrading M.grading M.grading (s + data.choose_spec.choose) x *
          pairGrading M.grading M.grading data.choose y +
        pairGrading M.grading M.grading data.choose x *
          pairGrading M.grading M.grading (s + data.choose_spec.choose) y) := by
    intro s
    let estimate := data.choose_spec.choose_spec s
    refine ⟨estimate.choose, estimate.choose_spec.1, fun x y => ?_⟩
    rw [show bilinearJetValue B x y = circleProductBilinear hM hT hD hγ x.1 y.2 from
      circleProductPairMultilinear_apply hM hT hD hγ ![x, y]]
    apply (estimate.choose_spec.2 x.1 y.2).trans
    apply mul_le_mul_of_nonneg_left _ estimate.choose_spec.1
    simp only [pairGrading_apply]
    apply add_le_add
    · exact mul_le_mul (le_add_of_nonneg_right (apply_nonneg _ _))
        (le_add_of_nonneg_left (apply_nonneg _ _)) (apply_nonneg _ _)
        (add_nonneg (apply_nonneg _ _) (apply_nonneg _ _))
    · exact mul_le_mul (le_add_of_nonneg_right (apply_nonneg _ _))
        (le_add_of_nonneg_left (apply_nonneg _ _)) (apply_nonneg _ _)
        (add_nonneg (apply_nonneg _ _) (apply_nonneg _ _))
  exact (n04PulledFields_fixedBaseFamily_quadratic (I := I)
    (pairGrading M.grading M.grading) M.grading B data.choose data.choose_spec.choose hB).congr
      (fun _ x _ => circleProductPairMultilinear_apply hM hT hD hγ ![x, x])

theorem n04PulledFields_fixedBase_circleProduct_maps
    {E : Type*} [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
    [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]
    {p : ℕ → Seminorm ℝ E} {U : Set E} {f g : I → E → M.Space}
    (hp : Monotone p) (hPI : HasInterpolation (pairGrading realGrading p)) (hU : IsOpen U)
    (hf : N04PulledFieldsFixedBaseFamily p M.grading U f)
    (hg : N04PulledFieldsFixedBaseFamily p M.grading U g) :
    N04PulledFieldsFixedBaseFamily p M.grading U
      (fun i x => circleProductBilinear hM hT hD hγ (f i x) (g i x)) := by
  letI : ∀ n, CompleteSpace (M.level n) :=
    fun n => (hM.2.1 n).isComplete.completeSpace_coe
  exact (n04PulledFields_fixedBase_circleProduct hD hT hγ hM hI).comp
    hp hPI (hf.prodMk hp hg) hU isOpen_univ (fun _ _ _ => mem_univ _)

end ContinuousFlexibility.Statements
