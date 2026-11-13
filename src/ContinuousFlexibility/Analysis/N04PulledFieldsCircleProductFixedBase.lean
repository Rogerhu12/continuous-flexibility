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

/-- A bilinear operation on a pair inherits one fixed low base.  The scalar
estimate is transferred before any concrete projective space is instantiated. -/
theorem n04PulledFields_fixedBaseFamily_pair_of_multilinear_bound
    {I E F : Type*}
    [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
    [TopologicalSpace F] [AddCommGroup F] [Module ℝ F]
    [IsTopologicalAddGroup F] [ContinuousSMul ℝ F]
    (p : ℕ → Seminorm ℝ E) (q : ℕ → Seminorm ℝ F)
    (A : (E × E) [×2]→L[ℝ] F) (P : E → E → F)
    (heq : ∀ v, A v = P (v 0).1 (v 1).2)
    (hb : ∃ base loss : ℕ, ∀ s, ∃ C : ℝ, 0 ≤ C ∧ ∀ u v : E,
      q s (P u v) ≤ C *
        (p (s + loss) u * p base v + p base u * p (s + loss) v)) :
    N04PulledFieldsFixedBaseFamily (pairGrading p p) q univ
      (fun (_ : I) x => P x.1 x.2) := by
  obtain ⟨base, loss, hb⟩ := hb
  have hA : ∀ s, ∃ C : ℝ, 0 ≤ C ∧ ∀ x y : E × E,
      q s (bilinearJetValue A x y) ≤ C *
        (pairGrading p p (s + loss) x * pairGrading p p base y +
          pairGrading p p base x * pairGrading p p (s + loss) y) := by
    intro s
    obtain ⟨C, hC, hc⟩ := hb s
    refine ⟨C, hC, fun x y => ?_⟩
    rw [show bilinearJetValue A x y = P x.1 y.2 from heq ![x, y]]
    apply (hc x.1 y.2).trans
    apply mul_le_mul_of_nonneg_left _ hC
    change
      p (s + loss) x.1 * p base y.2 + p base x.1 * p (s + loss) y.2 ≤
        (p (s + loss) x.1 + p (s + loss) x.2) * (p base y.1 + p base y.2) +
          (p base x.1 + p base x.2) * (p (s + loss) y.1 + p (s + loss) y.2)
    apply add_le_add
    · exact mul_le_mul (le_add_of_nonneg_right (apply_nonneg _ _))
        (le_add_of_nonneg_left (apply_nonneg _ _)) (apply_nonneg _ _)
        (add_nonneg (apply_nonneg _ _) (apply_nonneg _ _))
    · exact mul_le_mul (le_add_of_nonneg_right (apply_nonneg _ _))
        (le_add_of_nonneg_left (apply_nonneg _ _)) (apply_nonneg _ _)
        (add_nonneg (apply_nonneg _ _) (apply_nonneg _ _))
  exact (n04PulledFields_fixedBaseFamily_quadratic (I := I)
    (pairGrading p p) q A base loss hA).congr
      (fun _ x _ => heq ![x, x])

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
  exact n04PulledFields_fixedBaseFamily_pair_of_multilinear_bound
    M.grading M.grading (circleProductPairMultilinear hM hT hD hγ)
    (circleProductBilinear hM hT hD hγ)
    (circleProductPairMultilinear_apply hM hT hD hγ)
    (circleProduct_oneHigh_bound hM hT hD hγ hI)

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
