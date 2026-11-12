import ContinuousFlexibility.Analysis.N04RealizationMovingGraphBounds

/-!
# The actual height field composed with its moving-point graph

The state coordinate is the supplied continuous linear map and the
physical coordinate is the supplied genuine point tower. The physical
mixed-jet estimate and positive point jets are inserted into the actual
ordered-partition formula on the original domain.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set ContinuousFlexibility.Statements
open scoped BigOperators

variable {X E : Type*}
  [TopologicalSpace X] [AddCommGroup X] [Module ℝ X]
  [IsTopologicalAddGroup X] [ContinuousSMul ℝ X]
  [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
  [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]

/-- Positive jets of the actual linear state coordinate do not increase
either of its supplied parameter seminorm bounds. -/
theorem n04Realization_linearJet_seminorm_le
    (L : X →L[ℝ] E) (p : Seminorm ℝ E)
    {n : ℕ} (hn : 0 < n) (x : X) (v : Fin n → X)
    {B : ℝ} (hB : 0 ≤ B) (hv : ∀ i, p (L (v i)) ≤ B) :
    p (continuousLinearJets L n x v) ≤ B := by
  cases n with
  | zero => omega
  | succ n =>
      cases n with
      | zero =>
          simpa only [continuousLinearJets,
            ContinuousMultilinearMap.ofSubsingleton_apply_apply] using hv 0
      | succ n =>
          simpa only [continuousLinearJets, zero_apply, p.map_zero'] using hB

/-- The actual graph uses exactly the linear state jets and the supplied
point jets; no additional map representation is introduced. -/
theorem n04Realization_linearPointGraph_D_apply
    {W : Set X} {φ : X → PolarPoint} (Jφ : SmoothDirections W φ)
    (L : X →L[ℝ] E) (n : ℕ) (x : X) (v : Fin n → X) :
    (smoothDirectionsUniformProd
      ((smoothDirectionsLinear L).restrict Jφ.open_domain (subset_univ W)) Jφ).D n x v =
      (continuousLinearJets L n x v, Jφ.D n x v) := by
  simp only [smoothDirectionsUniformProd, SmoothDirections.restrict,
    smoothDirectionsLinear, smoothDirectionsOfJets, ContinuousMultilinearMap.prod_apply]

variable [LocallyConvexSpace ℝ E]

/-- Pointwise composition from the actual physical height tower and
raw inverse-point block jets. `C` retains the complete physical height
factor at the moving point; `M` contains only the inverse-geometry cost. -/
theorem n04Realization_heightGraph_composition_bound
    {D : ReferenceData} {T : MaterialData} {γ : ℝ} {M : SobolevModelData}
    (hT : IsMaterialData D T) (hM : IsSobolevModel D T γ M) (hγ : 0 < γ)
    {p : ℕ → Seminorm ℝ E} (hp : Monotone p) (hcp : ∀ j, Continuous (p j))
    {U : Set E} {f : E → M.Space} {g : E → PolarPoint → ℝ}
    {base loss : ℕ} (J : SmoothDirections U f)
    (hJ : UniformScalarTowerEstimate p M.grading U base loss f J)
    (heq : ∀ x ∈ U, M.decode (f x) = g x) (hc : Convex ℝ U)
    {W : Set X} {φ : X → PolarPoint} (Jφ : SmoothDirections W φ)
    (L : X →L[ℝ] E)
    (hmap : MapsTo (fun x => (L x, φ x)) W (U ×ˢ annularOpen D))
    (low high : Seminorm ℝ E) {C A R t : ℝ}
    (hC : 0 ≤ C) (hA : 1 ≤ A) (hR : 0 < R) (ht : 1 ≤ t)
    (n budget offset : ℕ) (x : X) (hx : x ∈ W) (v : Fin n → X)
    (κ β : ∀ c : OrderedFinpartition n, Fin c.length → ℕ)
    (hpart : ∀ c i, 0 < κ c i + β c i)
    (hcost : ∀ c, ∑ i, (β c i + (offset + 1) * κ c i) ≤ budget)
    (hlow : ∀ i, low (L (v i)) ≤ 1)
    (hhigh : ∀ i, high (L (v i)) ≤ R)
    (hphysical : ∀ a b k : ℕ, a + b + k ≤ n → ∀ u : Fin k → E,
      (∀ i, low (u i) ≤ 1) → (∀ i, high (u i) ≤ R) →
      |((n04Realization_heightFieldMixedJets hT hM J heq).parameter
        a b (φ x) (hmap hx).2).D k (L x) u| ≤ C * t ^ (a + b))
    (hinverse : ∀ c : OrderedFinpartition n, ∀ i : Fin c.length,
      ‖Jφ.D (c.partSize i) x (v ∘ c.emb i)‖ ≤
        A * t ^ (if κ c i = 0 then β c i - 1 else β c i + offset)) :
    let G := smoothDirectionsUniformProd
      ((smoothDirectionsLinear L).restrict Jφ.open_domain (subset_univ W)) Jφ
    let F := n04Realization_heightFieldJointDirections hT hM hγ hp hcp J hJ heq hc
    |(smoothDirections_realCompTVS G F hmap).D n x v| ≤
      (Fintype.card (OrderedFinpartition n) : ℝ) * C * (4 * A) ^ n * t ^ budget := by
  let G := smoothDirectionsUniformProd
    ((smoothDirectionsLinear L).restrict Jφ.open_domain (subset_univ W)) Jφ
  let F := n04Realization_heightFieldJointDirections hT hM hγ hp hcp J hJ heq hc
  let q : E × PolarPoint → ℝ := fun w => low w.1 + high w.1 / R +
    t * |w.2.1| + t * |w.2.2|
  have ht0 : 0 ≤ t := zero_le_one.trans ht
  have hq (w : E × PolarPoint) : 0 ≤ q w := by
    dsimp only [q]
    positivity
  apply n04Realization_realComp_weighted_power_bound G F hmap q hq hC
    (by nlinarith : 1 ≤ 4 * A) ht n budget x v
    (fun c i => β c i + (offset + 1) * κ c i) hcost
  · intro j hj w
    exact n04Realization_heightFieldJointDirections_bound hT hM hγ hp hcp J hJ heq hc
      low high hC hR ht0 j (L x) (φ x) (hmap hx).2
      (fun a b k hab u hu hv => hphysical a b k (hab.trans hj) u hu hv) w
  · intro c i
    have hl : low (continuousLinearJets L (c.partSize i) x (v ∘ c.emb i)) ≤ 1 :=
      n04Realization_linearJet_seminorm_le L low (c.partSize_pos i) x _
        zero_le_one (fun j => hlow _)
    have hh : high (continuousLinearJets L (c.partSize i) x (v ∘ c.emb i)) ≤ R :=
      n04Realization_linearJet_seminorm_le L high (c.partSize_pos i) x _
        hR.le (fun j => hhigh _)
    have hstate : low (continuousLinearJets L (c.partSize i) x (v ∘ c.emb i)) +
        high (continuousLinearJets L (c.partSize i) x (v ∘ c.emb i)) / R ≤ 2 := by
      have hd := (div_le_one hR).mpr hh
      linarith
    have hb := n04Realization_movingGraph_slot_bound
      (fun w : E => low w + high w / R)
      (continuousLinearJets L (c.partSize i) x (v ∘ c.emb i),
        Jφ.D (c.partSize i) x (v ∘ c.emb i))
      (κ c i) (β c i) offset (hpart c i) hA ht hstate (hinverse c i)
    simpa only [G, q, n04Realization_linearPointGraph_D_apply] using hb

end ContinuousFlexibility.Analysis
