import ContinuousFlexibility.Analysis.LocalJointJetSeminormBounds

/-!
# Joining both spatial variables to a genuine scalar parameter tower

The hypotheses concern the original mixed spatial fields, their actual
first partial derivatives and uniform seminorm bounds for the supplied
parameter towers. Local FTC first joins the radial variable and then
the angular variable. No regularity of formal higher jets is assumed.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace ContinuousFlexibility.Analysis

open Set ContinuousFlexibility.Statements
open scoped Topology ContDiff

variable {E : Type*}
  [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
  [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]
  {U : Set E} {I : Set ℝ} {F : ℕ → ℕ → PolarPoint → E → ℝ}
  (J : ∀ a b p, p ∈ I ×ˢ (univ : Set ℝ) → SmoothDirections U (F a b p))
  (hU : IsOpen U) (hcU : Convex ℝ U) (hI : IsOpen I)
  (hf : ∀ a b, ∀ x ∈ U, ContinuousOn (fun p => F a b p x) (I ×ˢ univ))
  (hbound : ∀ a b, UniformScalarJetSeminormBounds
    (fun p : I ×ˢ (univ : Set ℝ) => J a b p p.property))
  (hrad : ∀ a b p, p ∈ I ×ˢ (univ : Set ℝ) → ∀ x ∈ U,
    HasDerivAt (fun r => F a b (r, p.2) x) (F (a + 1) b p x) p.1)
  (hang : ∀ a b p, p ∈ I ×ˢ (univ : Set ℝ) → ∀ x ∈ U,
    HasDerivAt (fun θ => F a b (p.1, θ) x) (F a (b + 1) p x) p.2)

def mixedScalarRadialJointDirections (b : ℕ) (θ : ℝ) :
    SmoothDirections (U ×ˢ I) (fun x : E × ℝ => F 0 b (x.2, θ) x.1) := by
  let K : ∀ a r, r ∈ I → SmoothDirections U (fun x => F a b (r, θ) x) :=
    fun a r hr => J a b (r, θ) ⟨hr, mem_univ θ⟩
  apply localAngularTowerJointDirectionsOfUniform K hU hcU hI
  · intro a x hx
    exact (hf a b x hx).comp (continuous_id.prodMk continuous_const).continuousOn
      (fun r hr => ⟨hr, mem_univ θ⟩)
  · intro a
    exact (hbound a b).reindex
      (fun r : I => (⟨((r : ℝ), θ), ⟨r.property, mem_univ θ⟩⟩ : I ×ˢ univ))
  · intro a r hr x hx
    exact hrad a b (r, θ) ⟨hr, mem_univ θ⟩ x hx

theorem mixedScalarRadialJointDirections_uniform (b : ℕ) :
    UniformScalarJetSeminormBounds
      (mixedScalarRadialJointDirections J hU hcU hI hf hbound hrad b) := by
  let K : ∀ a θ r, r ∈ I → SmoothDirections U (fun x => F a b (r, θ) x) :=
    fun a θ r hr => J a b (r, θ) ⟨hr, mem_univ θ⟩
  apply uniformScalarJetSeminormBounds_local_joint K hU hcU hI _ _ _
    (mixedScalarRadialJointDirections J hU hcU hI hf hbound hrad b)
  · intro a θ x hx
    exact (hf a b x hx).comp (continuous_id.prodMk continuous_const).continuousOn
      (fun r hr => ⟨hr, mem_univ θ⟩)
  · intro a
    exact (hbound a b).reindex
      (fun p : ℝ × I =>
        (⟨((p.2 : ℝ), p.1), ⟨p.2.property, mem_univ p.1⟩⟩ : I ×ˢ univ))
  · intro a θ r hr x hx
    exact hrad a b (r, θ) ⟨hr, mem_univ θ⟩ x hx

def mixedScalarSpatialJointDirections (hcI : Convex ℝ I) :
    SmoothDirections ((U ×ˢ I) ×ˢ univ)
      (fun x : (E × ℝ) × ℝ => F 0 0 (x.1.2, x.2) x.1.1) := by
  let K : ∀ b θ, θ ∈ (univ : Set ℝ) →
      SmoothDirections (U ×ˢ I) (fun x : E × ℝ => F 0 b (x.2, θ) x.1) :=
    fun b θ _ => mixedScalarRadialJointDirections J hU hcU hI hf hbound hrad b θ
  apply localAngularTowerJointDirectionsOfUniform K (hU.prod hI) (hcU.prod hcI) isOpen_univ
  · intro b x hx
    exact (hf 0 b x.1 hx.1).comp (continuous_const.prodMk continuous_id).continuousOn
      (fun θ _ => ⟨hx.2, mem_univ θ⟩)
  · intro b
    exact (mixedScalarRadialJointDirections_uniform J hU hcU hI hf hbound hrad b).reindex
      (fun θ : (univ : Set ℝ) => (θ : ℝ))
  · intro b θ hθ x hx
    exact hang 0 b (x.2, θ) ⟨hx.2, mem_univ θ⟩ x.1 hx.1

end ContinuousFlexibility.Analysis
