import ContinuousFlexibility.Analysis.N04RealizationPositiveAngularCircle
import ContinuousFlexibility.Analysis.ParameterizedCircleInverse

/-!
# Genuine towers for the actual finite positive angular map and its inverse

The inputs are the finitely many endpoint traces, with their genuine
angular hierarchies and qualitative seminorm bounds. Their finite Taylor
formula is assembled in the existing circle model before its proved
inversion is applied. Both outputs use the literal original maps and
the same state domain, endpoints, and fixed collar width.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set ContinuousFlexibility.Statements
open scoped ContDiff

variable {E : Type*} [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
  [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]
  {D : ReferenceData} {T : MaterialData} {γ : ℝ} {S : CircleModelData}
  {U : Set E}

/-- No joint inverse hypothesis is supplied. In particular the raw
pointwise angular towers are promoted using their uniform seminorm
bounds before any circle inverse or joint evaluation is taken. -/
def n04Realization_positiveAngularTaylor_jointDirections
    (hS : IsCircleModel T γ S) (hT : IsMaterialData D T)
    (hD : IsAccumulatingProfile D) (hγ : 0 < γ) (hi : HasInterpolation S.grading)
    (hU : IsOpen U) (hc : Convex ℝ U) (n m : ℕ) (l r δ : ℝ)
    (A : E → Bool → ℕ → ℝ → ℝ)
    (hA : ∀ x ∈ U, ∀ side (j : Fin (n + 1)),
      ContDiff ℝ ∞ (fun θ => A x side j θ - if (j : ℕ) = 0 then θ else 0))
    (hperiod : ∀ x ∈ U, ∀ side (j : Fin (n + 1)),
      Function.Periodic
        (fun θ => A x side j θ - if (j : ℕ) = 0 then θ else 0) Real.pi)
    (J : ∀ side (j : Fin (n + 1)) b θ, SmoothDirections U
      (fun x => iteratedDeriv b
        (fun η => A x side j η - if (j : ℕ) = 0 then η else 0) θ))
    (hbound : ∀ side j b, UniformScalarJetSeminormBounds (J side j b))
    (hpositive : ∀ x ∈ U, ∀ t θ,
      0 < deriv (fun η => positiveAngularTaylorInterpolation n l r δ
        (A x) (t, η)) θ) :
    SmoothDirections (U ×ˢ univ)
        (fun p : E × PolarPoint =>
          positiveAngularTaylorInterpolation n l r δ (A p.1) p.2) ×
      SmoothDirections (U ×ˢ univ)
        (fun p : E × PolarPoint => parameterizedCircleInverse
          (positiveAngularTaylorInterpolation n l r δ (A p.1)) p.2) := by
  classical
  have hM (i : ℕ) : 0 ≤ T.M (T.sample i) :=
    ((material_circle_sample_weights_pos hT hD).1 i).le
  have hH (i : ℕ) : 0 < T.H (T.sample i) :=
    (material_circle_sample_weights_pos hT hD).2 i
  have htrace (side : Bool) (j : Fin (n + 1)) :
      ∃ F : E → S.Space, ∃ K : SmoothDirections U F,
        ∀ x ∈ U, S.decode (F x) = circleSingleComponentField m
          (fun θ => A x side j θ - if (j : ℕ) = 0 then θ else 0) :=
    n04Realization_singleComponentDirections hS hU hc hM (fun i => (hH i).le)
      (fun x θ => A x side j θ - if (j : ℕ) = 0 then θ else 0)
      (fun x hx => hA x hx side j) (fun x hx => hperiod x hx side j)
      (J side j) (hbound side j) m
  let F : Bool → Fin (n + 1) → E → S.Space := fun side j => (htrace side j).choose
  let KF : ∀ side j, SmoothDirections U (F side j) :=
    fun side j => (htrace side j).choose_spec.choose
  have hF (side : Bool) (j : Fin (n + 1)) (x : E) (hx : x ∈ U) :
      S.decode (F side j x) = circleSingleComponentField m
        (fun θ => A x side j θ - if (j : ℕ) = 0 then θ else 0) :=
    (htrace side j).choose_spec.choose_spec x hx
  have hcircle := n04Realization_positiveAngularTaylor_circleDirections
    hS hT hD hγ hi hU n m l r δ A F KF hF
  let G : E × ℝ → S.Space := hcircle.choose
  let KG : SmoothDirections (U ×ˢ univ) G := hcircle.choose_spec.choose
  have hG := hcircle.choose_spec.choose_spec
  let φ : E × ℝ → ℝ → ℝ := fun x θ =>
    positiveAngularTaylorInterpolation n l r δ (A x.1) (x.2, θ)
  let Kinv : SmoothDirections ((U ×ˢ univ) ×ˢ univ)
      (fun p : (E × ℝ) × ℝ => Function.invFun (φ p.1) p.2) :=
    n04Realization_circleInverseJointDirections hS hT hD hγ hi φ G KG m hG
      (fun x hx θ => hpositive x.1 hx.1 x.2 θ)
  let Kforward : SmoothDirections ((U ×ˢ univ) ×ˢ univ)
      (fun p : (E × ℝ) × ℝ => φ p.1 p.2) := by
    apply (circleAffineLiftJointDirections hS hH KG (fun _ => 0) m).congr
    intro p hp
    rw [hG p.1 hp.1]
    simp only [circleSingleComponentField, if_pos rfl]
    dsimp only [φ]
    ring
  let P : (E × PolarPoint) →L[ℝ] E := ContinuousLinearMap.fst ℝ E PolarPoint
  let R : (E × PolarPoint) →L[ℝ] ℝ :=
    (ContinuousLinearMap.fst ℝ ℝ ℝ).comp (ContinuousLinearMap.snd ℝ E PolarPoint)
  let Θ : (E × PolarPoint) →L[ℝ] ℝ :=
    (ContinuousLinearMap.snd ℝ ℝ ℝ).comp (ContinuousLinearMap.snd ℝ E PolarPoint)
  let L : (E × PolarPoint) →L[ℝ] ((E × ℝ) × ℝ) := (P.prod R).prod Θ
  have hL (p : E × PolarPoint) : L p = ((p.1, p.2.1), p.2.2) := by
    simp only [L, P, R, Θ, ContinuousLinearMap.prod_apply,
      ContinuousLinearMap.comp_apply, ContinuousLinearMap.coe_fst',
      ContinuousLinearMap.coe_snd']
  have hdomain : IsOpen (U ×ˢ (univ : Set PolarPoint)) := hU.prod isOpen_univ
  have hmap : MapsTo L (U ×ˢ univ) ((U ×ˢ univ) ×ˢ univ) := by
    intro p hp
    rw [hL]
    exact ⟨⟨hp.1, mem_univ _⟩, mem_univ _⟩
  refine ⟨(Kforward.compLinear L hdomain hmap).congrOn ?_,
    (Kinv.compLinear L hdomain hmap).congrOn ?_⟩
  · intro p _
    rw [hL]
    rfl
  · intro p _
    rw [hL]
    rfl

end ContinuousFlexibility.Analysis
