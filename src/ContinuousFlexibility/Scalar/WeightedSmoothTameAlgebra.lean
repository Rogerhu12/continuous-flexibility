import ContinuousFlexibility.Scalar.WeightedTowerCompositionGeneric
import ContinuousFlexibility.Scalar.WeightedTowerOperations
import ContinuousFlexibility.Analysis.TameComposition
import ContinuousFlexibility.Analysis.TamePairTopology

/-!
# Smooth tame algebra on the full operator parameter domains

The common-height and source parameters of S05 range over their whole
spaces. The ordinary local tame composition theorem below retains those
open product domains. Its genuine derivative tower is the actual
ordered-partition chain rule, while each local estimate comes from the
existing seminorm calculus.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open Set Function ContinuousFlexibility.Analysis
open scoped BigOperators

set_option backward.isDefEq.respectTransparency false

section Composition

variable {X Y : Type*}
  [TopologicalSpace X] [AddCommGroup X] [Module ℝ X]
  [IsTopologicalAddGroup X] [ContinuousSMul ℝ X]
  [TopologicalSpace Y] [AddCommGroup Y] [Module ℝ Y]
  [IsTopologicalAddGroup Y] [ContinuousSMul ℝ Y] [LocallyConvexSpace ℝ Y]
  {F : ℕ → Type*} [∀ n, NormedAddCommGroup (F n)] [∀ n, NormedSpace ℝ (F n)]
  [∀ n, CompleteSpace (F n)] {fbond : ∀ n, F (n + 1) →L[ℝ] F n}
  {p : ℕ → Seminorm ℝ X} {q : ℕ → Seminorm ℝ Y}
  {r : ℕ → Seminorm ℝ (ProjectiveLimit F fbond)}
  {U : Set X} {V : Set Y} {f : X → Y} {g : Y → ProjectiveLimit F fbond}

/-- The genuine composition theorem on arbitrary scalar state domains,
with a complete projective target and the original open source domain. -/
theorem smoothTameOn_comp_generic
    (hp : Monotone p) (htp : WithSeminorms p) (htq : WithSeminorms q)
    (hf : SmoothTameOn p q U f) (hg : SmoothTameOn q r V g)
    (hmap : MapsTo f U V) : SmoothTameOn p r U (g ∘ f) := by
  obtain ⟨J, hJ⟩ := hf
  obtain ⟨K, hK⟩ := hg
  let JK := smoothDirectionsUniformCompGeneric J K hmap
  apply smoothTameOn_of_locallyTameOn_jets hp htp JK
  intro k
  exact locallyTameOn_compositionJets hp htp htq J K hJ hK hmap k

end Composition

section Pairing

variable {X E F : Type*}
  [TopologicalSpace X] [AddCommGroup X] [Module ℝ X]
  [IsTopologicalAddGroup X] [ContinuousSMul ℝ X]
  [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
  [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]
  [TopologicalSpace F] [AddCommGroup F] [Module ℝ F]
  [IsTopologicalAddGroup F] [ContinuousSMul ℝ F]
  {p : ℕ → Seminorm ℝ X} {q : ℕ → Seminorm ℝ E} {r : ℕ → Seminorm ℝ F}
  {U : Set X} {f : X → E} {g : X → F}

theorem smoothTameOn_prodMk_generic
    (hp : Monotone p) (ht : WithSeminorms p)
    (hf : SmoothTameOn p q U f) (hg : SmoothTameOn p r U g) :
    SmoothTameOn p (pairGrading q r) U (fun x => (f x, g x)) := by
  obtain ⟨J, hJ⟩ := hf
  obtain ⟨K, hK⟩ := hg
  apply smoothTameOn_of_locallyTameOn_jets hp ht (smoothDirectionsUniformProd J K)
  intro k
  have hleft := locallyTameOn_jetEvaluation ht J hJ k
  have hright := locallyTameOn_jetEvaluation ht K hK k
  simpa only [smoothDirectionsUniformProd, ContinuousMultilinearMap.prod_apply] using
    hleft.prodMk (jetGrading_monotone hp k) hright

end Pairing

section Bilinear

variable {E F : Type*}
  [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
  [TopologicalSpace F] [AddCommGroup F] [Module ℝ F]
  [IsTopologicalAddGroup F] [ContinuousSMul ℝ F]
  {p : ℕ → Seminorm ℝ E} {q : ℕ → Seminorm ℝ F}
  {base loss : ℕ}

/-- A genuine continuous two-input map is smooth tame on the whole pair
space. Its local constants may depend on the pair center. -/
theorem smoothTameOn_bilinearMultilinear
    (B : E [×2]→L[ℝ] F)
    (hB : ∀ s, base ≤ s → ∃ C : ℝ, 0 ≤ C ∧ ∀ x y,
      q s (bilinearJetValue B x y) ≤
        C * (p (s + loss) x * p base y + p base x * p (s + loss) y)) :
    SmoothTameOn (pairGrading p p) q univ
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
    change p (s + loss) x.1 * p base y.2 + p base x.1 * p (s + loss) y.2 ≤
      (p (s + loss) x.1 + p (s + loss) x.2) * (p base y.1 + p base y.2) +
        (p base x.1 + p base x.2) * (p (s + loss) y.1 + p (s + loss) y.2)
    apply add_le_add
    · exact mul_le_mul (le_add_of_nonneg_right (apply_nonneg _ _))
        (le_add_of_nonneg_left (apply_nonneg _ _)) (apply_nonneg _ _)
        (add_nonneg (apply_nonneg _ _) (apply_nonneg _ _))
    · exact mul_le_mul (le_add_of_nonneg_right (apply_nonneg _ _))
        (le_add_of_nonneg_left (apply_nonneg _ _)) (apply_nonneg _ _)
        (add_nonneg (apply_nonneg _ _) (apply_nonneg _ _))
  apply smoothTameOn_congr (smoothTameOn_quadratic A hA)
  intro x _
  exact bilinearPairOfMultilinear_apply B x x

end Bilinear

section BilinearComposition

variable {X Y : Type*}
  [TopologicalSpace X] [AddCommGroup X] [Module ℝ X]
  [TopologicalSpace Y] [AddCommGroup Y] [Module ℝ Y]
  {F : ℕ → Type*} [∀ n, NormedAddCommGroup (F n)] [∀ n, NormedSpace ℝ (F n)]
  [∀ n, CompleteSpace (F n)] {fbond : ∀ n, F (n + 1) →L[ℝ] F n}
  {p : ℕ → Seminorm ℝ X} {q : ℕ → Seminorm ℝ Y}
  {r : ℕ → Seminorm ℝ (ProjectiveLimit F fbond)}
  {U : Set X} {f g : X → Y} {base loss : ℕ}

theorem smoothTameOn_bilinear_comp
    (hp : Monotone p) (htp : WithSeminorms p) (htq : WithSeminorms q)
    (hf : SmoothTameOn p q U f) (hg : SmoothTameOn p q U g)
    (B : Y [×2]→L[ℝ] (ProjectiveLimit F fbond))
    (hB : ∀ s, base ≤ s → ∃ C : ℝ, 0 ≤ C ∧ ∀ y z,
      r s (bilinearJetValue B y z) ≤
        C * (q (s + loss) y * q base z + q base y * q (s + loss) z)) :
    SmoothTameOn p r U (fun x => bilinearJetValue B (f x) (g x)) := by
  letI : IsTopologicalAddGroup X := htp.isTopologicalAddGroup
  letI : ContinuousSMul ℝ X := htp.continuousSMul
  letI : IsTopologicalAddGroup Y := htq.isTopologicalAddGroup
  letI : ContinuousSMul ℝ Y := htq.continuousSMul
  letI : LocallyConvexSpace ℝ Y := htq.toLocallyConvexSpace
  exact smoothTameOn_comp_generic hp htp (withSeminorms_pairGrading htq htq)
    (smoothTameOn_prodMk_generic hp htp hf hg) (smoothTameOn_bilinearMultilinear B hB)
    (fun _ _ => mem_univ _)

end BilinearComposition

end ContinuousFlexibility.Statements
