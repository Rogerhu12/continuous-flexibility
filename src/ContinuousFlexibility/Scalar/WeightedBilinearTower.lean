import ContinuousFlexibility.Scalar.WeightedTowerCalculus

/-!
# Uniform towers for actual continuous bilinear maps

The tower is the proved quadratic projective tower: orders zero, one, and two
are the value, its bilinear first variation, and its symmetrized second
variation; every higher order is zero.  A single low-seminorm bound on the
domain makes the estimate uniform on that entire domain.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open Set ContinuousFlexibility.Analysis
open scoped BigOperators

set_option backward.isDefEq.respectTransparency false

section Quadratic

variable {E F : Type*} [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
  [TopologicalSpace F] [AddCommGroup F] [Module ℝ F]
  [IsTopologicalAddGroup F] [ContinuousSMul ℝ F]
  {p : ℕ → Seminorm ℝ E} {q : ℕ → Seminorm ℝ F}
  {base loss : ℕ} {U : Set E}

private theorem weighted_tameJetSize_two (p : ℕ → Seminorm ℝ E) (s loss base : ℕ)
    (x : E) (v : Fin 2 → E) :
    tameJetSize p 2 s loss base x v =
      (1 + p (s + loss) x) * (p base (v 0) * p base (v 1)) +
        (p (s + loss) (v 0) * p base (v 1) + p (s + loss) (v 1) * p base (v 0)) := by
  have h0 : (Finset.univ : Finset (Fin 2)).erase 0 = {1} := by decide
  have h1 : (Finset.univ : Finset (Fin 2)).erase 1 = {0} := by decide
  simp only [tameJetSize, Fin.prod_univ_two, Fin.sum_univ_two, h0, h1,
    Finset.prod_singleton]

def smoothDirectionsQuadraticOn (B : E [×2]→L[ℝ] F) (hU : IsOpen U) :
    SmoothDirections U (quadraticJetValue B) :=
  smoothDirectionsOfJets hU (quadraticJets B) (hasProjectiveJetsOn_quadratic B U)

/-- The same fixed two-factor bound controls the whole genuine quadratic
tower on any open domain with a uniform bound on its low seminorm. -/
theorem uniformScalarTowerEstimate_quadratic
    (B : E [×2]→L[ℝ] F)
    (hB : ∀ s, base ≤ s → ∃ C : ℝ, 0 ≤ C ∧ ∀ x y,
      q s (bilinearJetValue B x y) ≤
        C * (p (s + loss) x * p base y + p base x * p (s + loss) y))
    (hU : IsOpen U) {R : ℝ} (hR : 0 ≤ R)
    (hxR : ∀ x ∈ U, p base x ≤ R) :
    UniformScalarTowerEstimate p q U base loss (quadraticJetValue B)
      (smoothDirectionsQuadraticOn B hU) := by
  intro k s hs
  obtain ⟨C, hC, hbound⟩ := hB s hs
  let M : ℝ := 1 + R
  have hM : 1 ≤ M := le_add_of_nonneg_right hR
  have hM0 : 0 ≤ M := zero_le_one.trans hM
  refine ⟨2 * C * M, by positivity, ?_⟩
  intro x hxU v
  have hx : p base x ≤ M := (hxR x hxU).trans (by dsimp [M]; linarith)
  have ha : 0 ≤ p (s + loss) x := apply_nonneg _ _
  change q s (quadraticJets B k x v) ≤ 2 * C * M * tameJetSize p k s loss base x v
  cases k with
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
          mul_le_mul_of_nonneg_left (by linarith) (by positivity)
  | succ k =>
      cases k with
      | zero =>
          rw [tameJetSize_one]
          change q s (quadraticJetFirst B x (v 0)) ≤ _
          rw [quadraticJetFirst_apply]
          have hv0 : 0 ≤ p (s + loss) (v 0) := apply_nonneg _ _
          have hvl : 0 ≤ p base (v 0) := apply_nonneg _ _
          have hax : p (s + loss) x ≤ M * (1 + p (s + loss) x) := by
            have ht := mul_le_mul_of_nonneg_right hM ha
            nlinarith
          calc
            _ ≤ q s (bilinearJetValue B (v 0) x) +
                q s (bilinearJetValue B x (v 0)) := map_add_le_add _ _ _
            _ ≤ C * (p (s + loss) (v 0) * p base x + p base (v 0) * p (s + loss) x) +
                C * (p (s + loss) x * p base (v 0) + p base x * p (s + loss) (v 0)) :=
              add_le_add (hbound (v 0) x) (hbound x (v 0))
            _ = 2 * C * (p (s + loss) (v 0) * p base x +
                p (s + loss) x * p base (v 0)) := by ring
            _ ≤ 2 * C * (p (s + loss) (v 0) * M +
                (M * (1 + p (s + loss) x)) * p base (v 0)) :=
              mul_le_mul_of_nonneg_left
                (add_le_add (mul_le_mul_of_nonneg_left hx hv0)
                  (mul_le_mul_of_nonneg_right hax hvl)) (by positivity)
            _ = _ := by ring
      | succ k =>
          cases k with
          | zero =>
              rw [weighted_tameJetSize_two]
              change q s (quadraticJetSecond B v) ≤ _
              rw [quadraticJetSecond_apply]
              let A : ℝ := p (s + loss) (v 0) * p base (v 1) +
                p (s + loss) (v 1) * p base (v 0)
              have hA : 0 ≤ A := by dsimp [A]; positivity
              have hrest : 0 ≤ (1 + p (s + loss) x) *
                  (p base (v 0) * p base (v 1)) := by positivity
              calc
                _ ≤ q s (bilinearJetValue B (v 0) (v 1)) +
                    q s (bilinearJetValue B (v 1) (v 0)) := map_add_le_add _ _ _
                _ ≤ C * (p (s + loss) (v 0) * p base (v 1) +
                    p base (v 0) * p (s + loss) (v 1)) +
                    C * (p (s + loss) (v 1) * p base (v 0) +
                    p base (v 1) * p (s + loss) (v 0)) :=
                  add_le_add (hbound (v 0) (v 1)) (hbound (v 1) (v 0))
                _ = 2 * C * A := by dsimp [A]; ring
                _ ≤ 2 * C * (M * A) :=
                  mul_le_mul_of_nonneg_left
                    (by simpa only [one_mul] using mul_le_mul_of_nonneg_right hM hA)
                    (by positivity)
                _ ≤ 2 * C * M *
                    ((1 + p (s + loss) x) * (p base (v 0) * p base (v 1)) + A) := by
                  rw [← mul_assoc]
                  exact mul_le_mul_of_nonneg_left (le_add_of_nonneg_left hrest) (by positivity)
          | succ k =>
              change q s 0 ≤ 2 * C * M * tameJetSize p (k + 3) s loss base x v
              rw [map_zero]
              exact mul_nonneg (by positivity) (tameJetSize_nonneg _ _ _ _ _ _ _)

theorem fixedNeighborhoodSmoothTame_quadratic
    (B : E [×2]→L[ℝ] F)
    (hB : ∀ s, base ≤ s → ∃ C : ℝ, 0 ≤ C ∧ ∀ x y,
      q s (bilinearJetValue B x y) ≤
        C * (p (s + loss) x * p base y + p base x * p (s + loss) y))
    (hU : IsOpen U) {R : ℝ} (hR : 0 ≤ R)
    (hxR : ∀ x ∈ U, p base x ≤ R) :
    FixedNeighborhoodSmoothTame p q U base loss (quadraticJetValue B) :=
  fixedNeighborhoodSmoothTame_of_uniform (smoothDirectionsQuadraticOn B hU)
    (uniformScalarTowerEstimate_quadratic B hB hU hR hxR)

end Quadratic

section Bilinear

variable {E F : Type*} [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
  [TopologicalSpace F] [AddCommGroup F] [Module ℝ F]
  [IsTopologicalAddGroup F] [ContinuousSMul ℝ F]
  {p : ℕ → Seminorm ℝ E} {q : ℕ → Seminorm ℝ F} {base loss : ℕ}

/-- Encode a genuine two-input continuous multilinear map as a quadratic
map on the pair of inputs, without introducing a topology on a curried map. -/
def bilinearPairOfMultilinear (B : E [×2]→L[ℝ] F) : (E × E) [×2]→L[ℝ] F :=
  B.compContinuousLinearMap (fun i =>
    if i = 0 then ContinuousLinearMap.fst ℝ E E else ContinuousLinearMap.snd ℝ E E)

theorem bilinearPairOfMultilinear_apply (B : E [×2]→L[ℝ] F) (x y : E × E) :
    bilinearJetValue (bilinearPairOfMultilinear B) x y =
      bilinearJetValue B x.1 y.2 := by
  simp only [bilinearJetValue, bilinearPairOfMultilinear,
    ContinuousMultilinearMap.compContinuousLinearMap_apply]
  apply congrArg B
  funext i
  fin_cases i <;> simp

/-- A genuine continuous bilinear evaluation has a fixed-loss actual tower
on every open set where the pair's fixed low seminorm is bounded. -/
theorem fixedNeighborhoodSmoothTame_bilinearMultilinear
    (B : E [×2]→L[ℝ] F)
    (hB : ∀ s, base ≤ s → ∃ C : ℝ, 0 ≤ C ∧ ∀ x y,
      q s (bilinearJetValue B x y) ≤
        C * (p (s + loss) x * p base y + p base x * p (s + loss) y))
    {U : Set (E × E)} (hU : IsOpen U) {R : ℝ} (hR : 0 ≤ R)
    (hxR : ∀ x ∈ U, pairGrading p p base x ≤ R) :
    FixedNeighborhoodSmoothTame (pairGrading p p) q U base loss
      (fun x : E × E => bilinearJetValue B x.1 x.2) := by
  let A := bilinearPairOfMultilinear B
  have hA : ∀ s, base ≤ s → ∃ C : ℝ, 0 ≤ C ∧ ∀ x y : E × E,
      q s (bilinearJetValue A x y) ≤
        C * (pairGrading p p (s + loss) x * pairGrading p p base y +
          pairGrading p p base x * pairGrading p p (s + loss) y) := by
    intro s hs
    obtain ⟨C, hC, hbound⟩ := hB s hs
    refine ⟨C, hC, ?_⟩
    intro x y
    rw [show bilinearJetValue A x y = bilinearJetValue B x.1 y.2 from
      bilinearPairOfMultilinear_apply B x y]
    apply (hbound x.1 y.2).trans
    apply mul_le_mul_of_nonneg_left _ hC
    simp only [tamePairGrading_apply]
    apply add_le_add
    · exact mul_le_mul (le_add_of_nonneg_right (apply_nonneg _ _))
        (le_add_of_nonneg_left (apply_nonneg _ _)) (apply_nonneg _ _)
        (add_nonneg (apply_nonneg _ _) (apply_nonneg _ _))
    · exact mul_le_mul (le_add_of_nonneg_right (apply_nonneg _ _))
        (le_add_of_nonneg_left (apply_nonneg _ _)) (apply_nonneg _ _)
        (add_nonneg (apply_nonneg _ _) (apply_nonneg _ _))
  have heq : quadraticJetValue A = fun x : E × E => bilinearJetValue B x.1 x.2 :=
    funext (fun x => bilinearPairOfMultilinear_apply B x x)
  rw [← heq]
  exact fixedNeighborhoodSmoothTame_quadratic A hA hU hR hxR

end Bilinear

end ContinuousFlexibility.Statements
