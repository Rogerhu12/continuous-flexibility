import ContinuousFlexibility.Analysis.TameInverseExpressions
import ContinuousFlexibility.Analysis.TameElementaryCalculus

/-!
# Uniform estimates for an actual smooth linear family

The first source derivative at `(x, 0)` is the original linear map.
Applying the first tame-jet estimate there gives one common parameter
neighborhood and one fixed loss for all output orders and all sources.
There is no bounded-source restriction in the resulting estimate.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set
open scoped Topology BigOperators
open ContinuousFlexibility.Statements

section LinearFamily

variable {X Y Z : Type*}
  [TopologicalSpace X] [AddCommGroup X] [Module ℝ X]
  [IsTopologicalAddGroup X] [ContinuousSMul ℝ X]
  [TopologicalSpace Y] [AddCommGroup Y] [Module ℝ Y]
  [IsTopologicalAddGroup Y] [ContinuousSMul ℝ Y]
  [TopologicalSpace Z] [AddCommGroup Z] [Module ℝ Z]
  [IsTopologicalAddGroup Z] [ContinuousSMul ℝ Z] [T2Space Z]

theorem coupled_uniformLinearFamilyTame_near
    {p : ℕ → Seminorm ℝ X} {q : ℕ → Seminorm ℝ Y} {r : ℕ → Seminorm ℝ Z}
    {U : Set X} {A : X → Y →L[ℝ] Z}
    (hA : SmoothTameOn (pairGrading p q) r (U ×ˢ univ)
      (fun z : X × Y => A z.1 z.2)) {x0 : X} (hx0 : x0 ∈ U) :
    ∃ b : ℕ, ∃ δ : ℝ, 0 < δ ∧
      LinearFamilyTame p r q {x | x ∈ U ∧ p b (x - x0) < δ}
        (fun x => (A x).toLinearMap) := by
  obtain ⟨J, hJ⟩ := hA
  obtain ⟨loss, b, δ, hδ, hbound⟩ := hJ 1 (x0, 0) ⟨hx0, mem_univ _⟩
  refine ⟨b, δ, hδ, loss, b, fun s hs => ?_⟩
  obtain ⟨c, hc, hbound⟩ := hbound s hs
  refine ⟨c, hc, fun x hx y => ?_⟩
  have hnear : pairGrading p q b ((x, (0 : Y)) - (x0, 0)) < δ := by
    simpa only [Prod.mk_sub_mk, sub_self, pairGrading_apply, map_zero, add_zero]
      using hx.2
  have h := hbound (x, 0) ⟨hx.1, mem_univ _⟩ hnear
    (fun _ : Fin 1 => ((0 : X), y))
  have heq : J.D 1 (x, 0) (fun _ : Fin 1 => ((0 : X), y)) = A x y := by
    have hi := inverseForwardJet_zero J hx.1 y
    convert hi using 1
    unfold inverseForwardJet
    congr 1
    funext i
    fin_cases i
    rfl
  change r s (J.D 1 (x, 0) (fun _ : Fin 1 => ((0 : X), y))) ≤
    c * tameJetSize (pairGrading p q) 1 s loss b (x, 0)
      (fun _ : Fin 1 => ((0 : X), y)) at h
  rw [heq, tameJetSize_one] at h
  simp only [pairGrading_apply, map_zero, add_zero, zero_add] at h
  simpa only [add_comm ((1 + p (s + loss) x) * q b y) (q (s + loss) y)] using h

end LinearFamily

end ContinuousFlexibility.Analysis
