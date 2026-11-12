import ContinuousFlexibility.Analysis.TameJetLocalBounds
import ContinuousFlexibility.Analysis.ProjectiveCurveIteratedChain

/-!
# Products of genuine smooth tame maps

The jets and their directional limits are paired in the actual product
topology. The common local jet bound then gives the exact homogeneous
estimate for the sum grading on the product.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter ContinuousFlexibility.Statements
open scoped Topology

variable {E F G : Type*}
  [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
  [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]
  [TopologicalSpace F] [AddCommGroup F] [Module ℝ F]
  [IsTopologicalAddGroup F] [ContinuousSMul ℝ F]
  [TopologicalSpace G] [AddCommGroup G] [Module ℝ G]
  [IsTopologicalAddGroup G] [ContinuousSMul ℝ G]
  {U : Set E} {f : E → F} {g : E → G}

def smoothDirectionsProd (J : SmoothDirections U f) (K : SmoothDirections U g) :
    SmoothDirections U (fun x => (f x, g x)) where
  open_domain := J.open_domain
  D n x := (J.D n x).prod (K.D n x)
  zero x hx := Prod.ext (J.zero x hx) (K.zero x hx)
  continuous n := (J.continuous n).prodMk (K.continuous n)
  derivative n x hx v w := (J.derivative n x hx v w).prodMk (K.derivative n x hx v w)

theorem smoothTameOn_prodMk
    {p : ℕ → Seminorm ℝ E} {q : ℕ → Seminorm ℝ F} {r : ℕ → Seminorm ℝ G}
    (hp : Monotone p) (ht : WithSeminorms p)
    (hf : SmoothTameOn p q U f) (hg : SmoothTameOn p r U g) :
    SmoothTameOn p (pairGrading q r) U (fun x => (f x, g x)) := by
  obtain ⟨J, hJ⟩ := hf
  obtain ⟨K, hK⟩ := hg
  apply smoothTameOn_of_locallyTameOn_jets hp ht (smoothDirectionsProd J K)
  intro n
  exact (locallyTameOn_jetEvaluation ht J hJ n).prodMk (jetGrading_monotone hp n)
    (locallyTameOn_jetEvaluation ht K hK n)

end ContinuousFlexibility.Analysis
