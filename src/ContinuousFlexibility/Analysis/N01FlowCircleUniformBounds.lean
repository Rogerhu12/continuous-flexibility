import ContinuousFlexibility.Analysis.N01EndpointSmoothTame
import ContinuousFlexibility.Analysis.TameUniformFamilyJets

/-!
# Selector-uniform bounds for the actual closed-radius flow towers

The underlying estimates are the physical endpoint norm bounds with
their constants already chosen before the radius selector. Passing to
the supplied finite-maximum grading and to joint jet growth preserves
that uniformity. The result applies to any genuine tower of the actual
flow displacement, by uniqueness.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open Set ContinuousFlexibility.Analysis
open scoped BigOperators

local instance n01FlowCircleUniformBoundsStateSMul (S : PhysicalSpacesData) :
    SMul ℝ (AnnularState S) := Prod.instSMul

private theorem uniform_flow_decoded_jet_eq
    {E F G : Type*} [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
    [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]
    [TopologicalSpace F] [AddCommGroup F] [Module ℝ F] [T2Space F]
    {U : Set E} {f : E → F} (J K : SmoothDirections U f) (decode : F → G)
    (n : ℕ) (x : E) (hx : x ∈ U) (v : Fin n → E) :
    decode (J.D n x v) = decode (K.D n x v) :=
  congrArg (fun A : E [×n]→L[ℝ] F => decode (A v)) (J.unique K n x hx)

private theorem uniform_flow_jetBounds_of_measured_bounds
    {I E F : Type*}
    [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
    [TopologicalSpace F] [AddCommGroup F] [Module ℝ F]
    (p : ℕ → Seminorm ℝ E) (q : ℕ → Seminorm ℝ F)
    (measure : ℕ → F → ℝ)
    (hcompare : ∀ s y A, 0 ≤ A → (∀ j, j ≤ s → measure j y ≤ A) → q s y ≤ A)
    (hmono : ∀ j k, j ≤ k → ∀ y, measure j y ≤ measure k y)
    {U : Set E} {f : I → E → F} (J : ∀ i, SmoothDirections U (f i))
    (hraw : ∀ n, ∃ B L : ℕ, ∀ R : ℝ, 0 ≤ R →
      ∀ s : ℕ, B ≤ s → ∃ K : ℝ, 0 ≤ K ∧
      ∀ i x, x ∈ U → p B x ≤ R → ∀ v : Fin n → E,
        measure s ((J i).D n x v) ≤ K * oneHighVariationWeight p B (s + L) x v) :
    UniformFamilyJetBounds p q J := by
  intro n
  refine uniformFamilyLowGrowthOn_of_oneHigh
    (I := I) (p := p) (q := q) (n := n) (U := U)
    (fun (i : I) (x : E) (v : Fin n → E) => (J i).D n x v) ?_
  obtain ⟨B, L, hb⟩ := hraw n
  refine ⟨B, B + L, fun R hR s => ?_⟩
  obtain ⟨K, hK, hk⟩ := hb R hR (s + B) (by omega)
  refine ⟨K, hK, fun i x hx hlow v => ?_⟩
  have hnorm : measure (s + B) ((J i).D n x v) ≤
      K * tameJetSize p n s (B + L) B x v := by
    simpa only [oneHighVariationWeight, tameJetSize, Nat.add_assoc] using hk i x hx hlow v
  exact hcompare s ((J i).D n x v) (K * tameJetSize p n s (B + L) B x v)
    (mul_nonneg hK (tameJetSize_nonneg p n s (B + L) B x v))
    (fun j hj => (hmono j (s + B) (hj.trans (Nat.le_add_right s B))
      ((J i).D n x v)).trans hnorm)

private theorem uniform_flow_measured_bounds_of_zero_positive
    {I P E F G : Type*}
    [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
    [TopologicalSpace F] [AddCommGroup F] [Module ℝ F]
    (p : ℕ → Seminorm ℝ E) (measure : ℕ → G → ℝ) (decode : F → G)
    (base : ℕ) (valid : P → Prop)
    (f : ∀ r : P, valid r → E → F)
    (A : ∀ n : ℕ, ∀ r : P, valid r → E → (Fin n → E) → G)
    {U : Set E} (rsel : I → P) (hrsel : ∀ i, valid (rsel i))
    (J : ∀ i, SmoothDirections U (f (rsel i) (hrsel i)))
    (hdecode : ∀ i n x, x ∈ U → ∀ v : Fin n → E,
      decode ((J i).D n x v) = A n (rsel i) (hrsel i) x v)
    (hzero : ∃ B L : ℕ, base ≤ B ∧ ∀ R : ℝ, 0 ≤ R →
      ∀ s : ℕ, B ≤ s → ∃ K : ℝ, 0 ≤ K ∧
      ∀ (r : P) (hr : valid r) x, x ∈ U → p B x ≤ R →
        measure s (decode (f r hr x)) ≤ K * (1 + p (s + L) x))
    (hpositive : ∃ B L : ℕ, base ≤ B ∧ ∀ n : ℕ, ∀ R : ℝ, 0 ≤ R →
      ∀ s : ℕ, B ≤ s → ∃ K : ℝ, 0 ≤ K ∧
      ∀ (r : P) (hr : valid r) x, x ∈ U → p B x ≤ R →
      ∀ v : Fin (n + 1) → E,
        measure s (A (n + 1) r hr x v) ≤
          K * oneHighVariationWeight p B (s + L) x v) :
    ∀ n, ∃ B L : ℕ, ∀ R : ℝ, 0 ≤ R →
      ∀ s : ℕ, B ≤ s → ∃ K : ℝ, 0 ≤ K ∧
      ∀ i x, x ∈ U → p B x ≤ R → ∀ v : Fin n → E,
        measure s (decode ((J i).D n x v)) ≤
          K * oneHighVariationWeight p B (s + L) x v := by
  intro n
  cases n with
  | zero =>
      let B : ℕ := hzero.choose
      let L : ℕ := hzero.choose_spec.choose
      refine ⟨B, L, fun R hR s hs => ?_⟩
      let orderData := hzero.choose_spec.choose_spec.2 R hR s hs
      let K : ℝ := orderData.choose
      refine ⟨K, orderData.choose_spec.1, ?_⟩
      intro i x hx hlow v
      have hv : v = Fin.elim0 := by
        funext j
        exact Fin.elim0 j
      have hvalue : (J i).D 0 x v = f (rsel i) (hrsel i) x :=
        (congrArg (fun w : Fin 0 → E => (J i).D 0 x w) hv).trans
          ((J i).zero x hx)
      have hbound : measure s (decode (f (rsel i) (hrsel i) x)) ≤
          K * (1 + p (s + L) x) :=
        orderData.choose_spec.2 (rsel i) (hrsel i) x hx hlow
      have hweight : oneHighVariationWeight p B (s + L) x v =
          1 + p (s + L) x := by
        simp only [oneHighVariationWeight, Fin.prod_univ_zero, Fin.sum_univ_zero,
          mul_one, add_zero]
      exact (congrArg (fun y : F => measure s (decode y)) hvalue).trans_le
        (hbound.trans_eq (congrArg (fun a : ℝ => K * a) hweight.symm))
  | succ n =>
      let B : ℕ := hpositive.choose
      let L : ℕ := hpositive.choose_spec.choose
      refine ⟨B, L, fun R hR s hs => ?_⟩
      let orderData := hpositive.choose_spec.choose_spec.2 n R hR s hs
      let K : ℝ := orderData.choose
      refine ⟨K, orderData.choose_spec.1, ?_⟩
      intro i x hx hlow v
      exact (congrArg (measure s) (hdecode i (n + 1) x hx v)).trans_le
        (orderData.choose_spec.2 (rsel i) (hrsel i) x hx hlow v)

variable {I : Type*} {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {base loss : ℕ} {ε : ℝ}

private theorem endpointFlowCircle_uniform_measured_bounds
    (hN : N01Properties D T S C base loss ε)
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    (rsel : I → ℕ → ℝ)
    (hrsel : ∀ i m, rsel i m ∈ Icc (C.left m) (C.right m))
    (J : ∀ i, SmoothDirections (sectorNeighborhood S base ε ε)
      (hN.endpointFlowCircle hS hT (rsel i) (hrsel i))) :
    ∀ n, ∃ B L : ℕ, ∀ R : ℝ, 0 ≤ R →
      ∀ s : ℕ, B ≤ s → ∃ K : ℝ, 0 ≤ K ∧
      ∀ i x, x ∈ sectorNeighborhood S base ε ε →
        pairGrading (sectorGrading S) realGrading B x ≤ R →
      ∀ v : Fin n → StateDirections S × ℝ,
        circleNorm T (3 / 4 : ℝ) s
          ((S.circle (3 / 4 : ℝ)).decode ((J i).D n x v)) ≤
          K * oneHighVariationWeight (pairGrading (sectorGrading S) realGrading)
            B (s + L) x v := by
  let H := S.circle (3 / 4 : ℝ)
  have hdecode (i : I) (n : ℕ) (x : StateDirections S × ℝ)
      (hx : x ∈ sectorNeighborhood S base ε ε) (v : Fin n → StateDirections S × ℝ) :
      H.decode ((J i).D n x v) =
        hN.endpointFlowScalarJets hS hT (rsel i) (hrsel i) n x v := by
    let towerData := hN.exists_endpointFlowCircle_smoothDirections hS hT (rsel i) (hrsel i)
    let J₀ : SmoothDirections (sectorNeighborhood S base ε ε)
        (hN.endpointFlowCircle hS hT (rsel i) (hrsel i)) := towerData.choose
    exact (uniform_flow_decoded_jet_eq
      (E := StateDirections S × ℝ) (F := CircleSpace S) (G := ℕ → ℝ → ℝ)
      (J i) J₀ H.decode n x hx v).trans (towerData.choose_spec n x hx v)
  exact uniform_flow_measured_bounds_of_zero_positive
    (I := I) (P := ℕ → ℝ) (E := StateDirections S × ℝ)
    (F := CircleSpace S) (G := ℕ → ℝ → ℝ)
    (U := sectorNeighborhood S base ε ε)
    (pairGrading (sectorGrading S) realGrading) (circleNorm T (3 / 4 : ℝ)) H.decode
    base (fun r : ℕ → ℝ => ∀ m, r m ∈ Icc (C.left m) (C.right m))
    (fun r hr => hN.endpointFlowCircle hS hT r hr)
    (fun n r hr x v => hN.endpointFlowScalarJets hS hT r hr n x v)
    rsel hrsel J hdecode
    (hN.endpointFlowCircle_circleNorm_local_growth_uniform_radius hS hT)
    (hN.endpointFlowScalarJets_positive_circleNorm_oneHigh_uniform_radius hS hT)

theorem N01Properties.endpointFlowCircle_uniformFamilyJetBounds
    (hN : N01Properties D T S C base loss ε)
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    (rsel : I → ℕ → ℝ)
    (hrsel : ∀ i m, rsel i m ∈ Icc (C.left m) (C.right m))
    (J : ∀ i, SmoothDirections (sectorNeighborhood S base ε ε)
      (hN.endpointFlowCircle hS hT (rsel i) (hrsel i))) :
    UniformFamilyJetBounds (pairGrading (sectorGrading S) realGrading)
      (S.circle (3 / 4 : ℝ)).grading J := by
  exact uniform_flow_jetBounds_of_measured_bounds
    (pairGrading (sectorGrading S) realGrading) (S.circle (3 / 4 : ℝ)).grading
    (fun s y => circleNorm T (3 / 4 : ℝ) s ((S.circle (3 / 4 : ℝ)).decode y))
    (fun s y A hA hbound =>
      (circleGrading_le_iff_circleNorm (hS.2.1 (3 / 4 : ℝ)) s y hA).mpr hbound)
    (fun j k hj y =>
      circleNorm_monotone_of_member ((hS.2.1 (3 / 4 : ℝ)).2.2.2.1 y) hj)
    J (endpointFlowCircle_uniform_measured_bounds hN hS hT rsel hrsel J)

end ContinuousFlexibility.Statements
