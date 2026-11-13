import ContinuousFlexibility.Analysis.N04RealizationPhysicalJointBounds

/-!
# Joining a uniformly controlled mixed tower in two physical coordinates

The existing radial and angular constructors apply to the actual mixed
fields on an unchanged product domain. The uniform seminorm premise is
qualitative and is supplied independently by the physical coefficient
construction. The formula below retains the original mixed parameter
towers for the sharper weighted estimate.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set ContinuousFlexibility.Statements
open scoped ContDiff

variable {E : Type*}
  [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
  [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]
  {U : Set E} {I : Set ℝ} {f : E → PolarPoint → ℝ}

def n04Realization_mixedJointDirections
    (RF : MixedJetRegularity U (I ×ˢ (univ : Set ℝ)) f)
    (hU : IsOpen U) (hcU : Convex ℝ U) (hI : IsOpen I) (hcI : Convex ℝ I)
    (hb : ∀ a b, UniformScalarJetSeminormBounds
      (fun q : I ×ˢ (univ : Set ℝ) => RF.parameter a b q q.property)) :
    SmoothDirections (U ×ˢ (I ×ˢ (univ : Set ℝ)))
      (fun x : E × PolarPoint => f x.1 x.2) := by
  have hΩ : IsOpen (I ×ˢ (univ : Set ℝ)) := hI.prod isOpen_univ
  let K := mixedScalarSpatialJointDirections RF.parameter hU hcU hI
    (fun a b x hx => (contDiffOn_mixedDerivative hΩ (RF.spatial x hx) a b).continuousOn)
    hb
    (fun a b q hq x hx => mixedDerivative_hasDerivAt_radial hΩ (RF.spatial x hx) a b hq)
    (fun a b q hq x hx => mixedDerivative_hasDerivAt_angular hΩ (RF.spatial x hx) a b hq)
    hcI
  let L := K.compLinear (parameterSpatialAssociation E) (hU.prod hΩ)
    (fun x hx => ⟨⟨hx.1, hx.2.1⟩, hx.2.2⟩)
  exact L.congrOn (fun x _ => by
    simp only [mixedDerivative, iteratedDeriv_zero, parameterSpatialAssociation,
      ContinuousLinearMap.prod_apply, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.coe_fst', ContinuousLinearMap.coe_snd', Prod.eta])

theorem n04Realization_mixedJointDirections_expansion
    (RF : MixedJetRegularity U (I ×ˢ (univ : Set ℝ)) f)
    (hU : IsOpen U) (hcU : Convex ℝ U) (hI : IsOpen I) (hcI : Convex ℝ I)
    (hb : ∀ a b, UniformScalarJetSeminormBounds
      (fun q : I ×ˢ (univ : Set ℝ) => RF.parameter a b q q.property))
    (n : ℕ) (x : E) (q : PolarPoint) (hq : q ∈ I ×ˢ (univ : Set ℝ))
    (v : Fin n → E × PolarPoint) :
    (n04Realization_mixedJointDirections RF hU hcU hI hcI hb).D n (x, q) v =
      scalarAngularExpansion n (fun b k => scalarAngularExpansion k
        (fun a j => ((RF.parameter a b q hq).D j x).toMultilinearMap))
        (fun i => (((v i).1, (v i).2.1), (v i).2.2)) := by
  have hΩ : IsOpen (I ×ˢ (univ : Set ℝ)) := hI.prod isOpen_univ
  let hf : ∀ a b, ∀ z ∈ U,
      ContinuousOn (fun p => mixedDerivative a b (f z) p) (I ×ˢ (univ : Set ℝ)) :=
    fun a b z hz => (contDiffOn_mixedDerivative hΩ (RF.spatial z hz) a b).continuousOn
  let hr : ∀ a b p, p ∈ I ×ˢ (univ : Set ℝ) → ∀ z ∈ U,
      HasDerivAt (fun r => mixedDerivative a b (f z) (r, p.2))
        (mixedDerivative (a + 1) b (f z) p) p.1 :=
    fun a b p hp z hz => mixedDerivative_hasDerivAt_radial hΩ (RF.spatial z hz) a b hp
  let ha : ∀ a b p, p ∈ I ×ˢ (univ : Set ℝ) → ∀ z ∈ U,
      HasDerivAt (fun θ => mixedDerivative a b (f z) (p.1, θ))
        (mixedDerivative a (b + 1) (f z) p) p.2 :=
    fun a b p hp z hz => mixedDerivative_hasDerivAt_angular hΩ (RF.spatial z hz) a b hp
  let K := mixedScalarSpatialJointDirections RF.parameter hU hcU hI hf hb hr ha hcI
  have hsame :
      (n04Realization_mixedJointDirections RF hU hcU hI hcI hb).D n (x, q) v =
        K.D n ((x, q.1), q.2)
          (fun i => (((v i).1, (v i).2.1), (v i).2.2)) := by
    change ((K.D n (0 + parameterSpatialAssociation E (x, q))).compContinuousLinearMap
      (fun _ => parameterSpatialAssociation E)) v = _
    rw [ContinuousMultilinearMap.compContinuousLinearMap_apply, zero_add]
    simp only [parameterSpatialAssociation, ContinuousLinearMap.prod_apply,
      ContinuousLinearMap.comp_apply, ContinuousLinearMap.coe_fst', ContinuousLinearMap.coe_snd']
  exact hsame.trans (n04Realization_spatialJoint_expansion RF.parameter hU hcU hI
    hf hb hr ha hcI n x q hq (fun i => (((v i).1, (v i).2.1), (v i).2.2)))

end ContinuousFlexibility.Analysis
