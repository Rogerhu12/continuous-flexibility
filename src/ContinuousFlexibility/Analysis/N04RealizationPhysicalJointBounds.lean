import ContinuousFlexibility.Analysis.N04RealizationJointExpansionBounds
import ContinuousFlexibility.Analysis.N04RealizationHeightJointDirections

/-!
# Physical height bounds for the genuine joint tower

The existing radial and angular joins have exactly the two scalar
expansions of the original mixed parameter jets. Their numerical bound
retains the physical height once, including parameter order zero. No
bound for a final canonical field is used.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set ContinuousFlexibility.Statements
open scoped ContDiff BigOperators

variable {E : Type*}
  [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
  [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]

section ExistingExpansion

variable {U : Set E} {I : Set ℝ} {F : ℕ → ℕ → PolarPoint → E → ℝ}
  (J : ∀ a b q, q ∈ I ×ˢ (univ : Set ℝ) → SmoothDirections U (F a b q))
  (hU : IsOpen U) (hcU : Convex ℝ U) (hI : IsOpen I)
  (hf : ∀ a b, ∀ x ∈ U, ContinuousOn (fun q => F a b q x) (I ×ˢ univ))
  (hb : ∀ a b, UniformScalarJetSeminormBounds
    (fun q : I ×ˢ (univ : Set ℝ) => J a b q q.property))
  (hr : ∀ a b q, q ∈ I ×ˢ (univ : Set ℝ) → ∀ x ∈ U,
    HasDerivAt (fun r => F a b (r, q.2) x) (F (a + 1) b q x) q.1)
  (ha : ∀ a b q, q ∈ I ×ˢ (univ : Set ℝ) → ∀ x ∈ U,
    HasDerivAt (fun θ => F a b (q.1, θ) x) (F a (b + 1) q x) q.2)

/-- The radial join is the existing scalar angular expansion evaluated
at the actual physical radius. -/
theorem n04Realization_radialJoint_expansion
    (b n : ℕ) (x : E) (q : PolarPoint) (hq : q ∈ I ×ˢ (univ : Set ℝ))
    (v : Fin n → E × ℝ) :
    (mixedScalarRadialJointDirections J hU hcU hI hf hb hr b q.2).D n (x, q.1) v =
      scalarAngularExpansion n
        (fun a k => ((J a b q hq).D k x).toMultilinearMap) v := by
  change scalarAngularExpansion n
    (fun a k => (localScalarJetMap
      (fun r hr => J a b (r, q.2) ⟨hr, mem_univ _⟩) k x q.1).toMultilinearMap) v = _
  have heq :
      (fun a k => (localScalarJetMap
        (fun r hr => J a b (r, q.2) ⟨hr, mem_univ _⟩) k x q.1).toMultilinearMap) =
      (fun a k => ((J a b q hq).D k x).toMultilinearMap) := by
    funext a k
    apply MultilinearMap.ext
    intro u
    exact (localScalarJetMap_apply _ k x q.1 u).trans
      (localScalarJet_of_mem _ k x u hq.1)
  rw [heq]

/-- Both spatial joins reuse the original scalar expansion, in the
same radial-then-angular order as the genuine constructor. -/
theorem n04Realization_spatialJoint_expansion
    (hcI : Convex ℝ I) (n : ℕ) (x : E)
    (q : PolarPoint) (hq : q ∈ I ×ˢ (univ : Set ℝ))
    (v : Fin n → (E × ℝ) × ℝ) :
    (mixedScalarSpatialJointDirections J hU hcU hI hf hb hr ha hcI).D
        n ((x, q.1), q.2) v =
      scalarAngularExpansion n (fun b k => scalarAngularExpansion k
        (fun a j => ((J a b q hq).D j x).toMultilinearMap)) v := by
  change scalarAngularExpansion n
    (fun b k => (localScalarJetMap (fun (θ : ℝ) (_ : θ ∈ (univ : Set ℝ)) =>
      mixedScalarRadialJointDirections J hU hcU hI hf hb hr b θ)
        k (x, q.1) q.2).toMultilinearMap) v = _
  have heq :
      (fun b k => (localScalarJetMap (fun (θ : ℝ) (_ : θ ∈ (univ : Set ℝ)) =>
        mixedScalarRadialJointDirections J hU hcU hI hf hb hr b θ)
          k (x, q.1) q.2).toMultilinearMap) =
      (fun b k => scalarAngularExpansion k
        (fun a j => ((J a b q hq).D j x).toMultilinearMap)) := by
    funext b k
    apply MultilinearMap.ext
    intro u
    rw [localScalarJetMap_apply, localScalarJet_of_mem _ k (x, q.1) u (mem_univ q.2)]
    exact n04Realization_radialJoint_expansion J hU hcU hI hf hb hr b k x q hq u
  rw [heq]

end ExistingExpansion

/-- A finite physical mixed bound controls the same joint height tower
with one spatial scale in each physical direction. -/
theorem n04Realization_heightFieldJointDirections_bound
    {D : ReferenceData} {T : MaterialData} {γ : ℝ} {M : SobolevModelData}
    (hT : IsMaterialData D T) (hM : IsSobolevModel D T γ M) (hγ : 0 < γ)
    {p : ℕ → Seminorm ℝ E} (hp : Monotone p) (hcp : ∀ j, Continuous (p j))
    {U : Set E} {f : E → M.Space} {g : E → PolarPoint → ℝ}
    {base loss : ℕ} (J : SmoothDirections U f)
    (hJ : UniformScalarTowerEstimate p M.grading U base loss f J)
    (heq : ∀ x ∈ U, M.decode (f x) = g x) (hc : Convex ℝ U)
    (low high : Seminorm ℝ E) {C R t : ℝ}
    (hC : 0 ≤ C) (hR : 0 < R) (ht : 0 ≤ t)
    (n : ℕ) (x : E) (q : PolarPoint) (hq : q ∈ annularOpen D)
    (hb : ∀ a b k : ℕ, a + b + k ≤ n → ∀ v : Fin k → E,
      (∀ i, low (v i) ≤ 1) → (∀ i, high (v i) ≤ R) →
      |((n04Realization_heightFieldMixedJets hT hM J heq).parameter a b q hq).D k x v| ≤
        C * t ^ (a + b))
    (v : Fin n → E × PolarPoint) :
    |(n04Realization_heightFieldJointDirections hT hM hγ hp hcp J hJ heq hc).D
        n (x, q) v| ≤
      C * ∏ i, (low (v i).1 + high (v i).1 / R +
        t * |(v i).2.1| + t * |(v i).2.2|) := by
  let RF : MixedJetRegularity U (annularOpen D) g :=
    n04Realization_heightFieldMixedJets hT hM J heq
  have hΩ : IsOpen (annularOpen D) := isOpen_Ioo.prod isOpen_univ
  let hf : ∀ a b : ℕ, ∀ x ∈ U,
      ContinuousOn (fun q => mixedDerivative a b (g x) q) (annularOpen D) :=
    fun a b x hx => (contDiffOn_mixedDerivative hΩ (RF.spatial x hx) a b).continuousOn
  let hbounds := n04Realization_heightField_uniformSeminormBounds hT hM hγ hp hcp J hJ heq
  let hrad : ∀ a b : ℕ, ∀ q : PolarPoint, q ∈ annularOpen D → ∀ x ∈ U,
      HasDerivAt (fun r => mixedDerivative a b (g x) (r, q.2))
        (mixedDerivative (a + 1) b (g x) q) q.1 :=
    fun a b q hq x hx => mixedDerivative_hasDerivAt_radial hΩ (RF.spatial x hx) a b hq
  let hang : ∀ a b : ℕ, ∀ q : PolarPoint, q ∈ annularOpen D → ∀ x ∈ U,
      HasDerivAt (fun θ => mixedDerivative a b (g x) (q.1, θ))
        (mixedDerivative a (b + 1) (g x) q) q.2 :=
    fun a b q hq x hx => mixedDerivative_hasDerivAt_angular hΩ (RF.spatial x hx) a b hq
  let K := mixedScalarSpatialJointDirections RF.parameter J.open_domain hc isOpen_Ioo
    hf hbounds hrad hang (convex_Ioo D.a D.b)
  have hsame :
      (n04Realization_heightFieldJointDirections hT hM hγ hp hcp J hJ heq hc).D n (x, q) v =
        K.D n ((x, q.1), q.2) (fun i => (((v i).1, (v i).2.1), (v i).2.2)) := by
    change ((K.D n (0 + parameterSpatialAssociation E (x, q))).compContinuousLinearMap
      (fun _ => parameterSpatialAssociation E)) v = _
    rw [ContinuousMultilinearMap.compContinuousLinearMap_apply, zero_add]
    simp only [parameterSpatialAssociation, ContinuousLinearMap.prod_apply,
      ContinuousLinearMap.comp_apply, ContinuousLinearMap.coe_fst', ContinuousLinearMap.coe_snd']
  rw [hsame, n04Realization_spatialJoint_expansion RF.parameter J.open_domain hc
    isOpen_Ioo hf hbounds hrad hang (convex_Ioo D.a D.b) n x q hq]
  apply n04Realization_doubleAngularExpansion_weighted_bound n
    (fun w => low w + high w / R)
    (fun w => add_nonneg (apply_nonneg low _) (div_nonneg (apply_nonneg high _) hR.le))
    _ hC ht
  intro a b k hab u
  exact n04Realization_multilinear_twoSeminorm_bound ((RF.parameter a b q hq).D k x)
    low high (mul_nonneg hC (pow_nonneg ht _)) hR (hb a b k hab) u

end ContinuousFlexibility.Analysis
