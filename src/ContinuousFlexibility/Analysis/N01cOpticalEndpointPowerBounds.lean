module

public import ContinuousFlexibility.Analysis.N01cOpticalMaterialBounds
public import ContinuousFlexibility.Analysis.N01cEndpointMixedPowerAlgebra
public import ContinuousFlexibility.Analysis.N01cStateHeightJets

/-!
# The actual optical root in the endpoint-weighted coefficient algebra

All radial and parameter orders use the same state neighbourhood. The
finite derivative range is enveloped only after its actual low-seminorm
products have been bounded. Angular derivatives vanish because this
factor is the original radial optical square root.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter
open ContinuousFlexibility.Statements
open scoped ContDiff Topology BigOperators

set_option backward.isDefEq.respectTransparency false

variable {X ι : Type*} [TopologicalSpace X] [AddCommGroup X] [Module ℝ X]
  [IsTopologicalAddGroup X] [ContinuousSMul ℝ X]

/-- The low-order radial product estimates imply the endpoint power
bound for every actual tower, without any parameter loss. -/
theorem endpointRadialLowJets_powerBounds
    (p : ℕ → Seminorm ℝ X) (q : Seminorm ℝ X)
    (center : X) (base loss : ℕ) (hqp : ∀ v, q v ≤ p base v)
    {U : Set X} (I : ι → Set ℝ) (δ : ι → ℝ → ℝ) (H E : ι → ℝ)
    (hH : ∀ m, 0 ≤ H m) (hE : ∀ m, 1 ≤ E m)
    (f : ι → X → ℝ → ℝ)
    (hraw : ∀ n k : ℕ, ∃ C A : ℝ, 0 < C ∧ 0 ≤ A ∧
      ∀ m r, r ∈ I m →
      ∀ J : SmoothDirections U (fun x => iteratedDeriv n (f m x) r),
      ∀ x ∈ U, ∀ v : Fin k → X,
        δ m r ^ n * ‖J.D k x v‖ ≤
          C * E m ^ A * parameterHeightWeight (H m) k * ∏ i, q (v i)) :
    EndpointMixedPowerBounds p center base loss U (fun m => I m ×ˢ univ)
      (fun m t => δ m t.1) (fun m _ => H m) (fun m _ => E m)
      (fun m x t => f m x t.1) := by
  classical
  intro K s
  choose c A hc hA hb using
    (fun i : Fin (s + 1) × Fin (K + 1) => hraw i.1.val i.2.val)
  let C : ℝ := 1 + ∑ i : Fin (s + 1) × Fin (K + 1), c i
  let B : ℝ := ∑ i : Fin (s + 1) × Fin (K + 1), A i
  have hC : 1 ≤ C := le_add_of_nonneg_right (Finset.sum_nonneg (fun i _ => (hc i).le))
  have hB : 0 ≤ B := Finset.sum_nonneg (fun i _ => hA i)
  have hcC (i) : c i ≤ C :=
    (Finset.single_le_sum (fun j _ => (hc j).le) (Finset.mem_univ i)).trans
      (le_add_of_nonneg_left zero_le_one)
  have hAB (i) : A i ≤ B := Finset.single_le_sum (fun j _ => hA j) (Finset.mem_univ i)
  refine ⟨C, B, hC, hB, ?_⟩
  intro m k hk a b hab t ht J x hx hlow v hv R hR hhigh hvhigh
  have hW : 0 ≤ parameterHeightWeight (H m) k := parameterHeightWeight_nonneg (hH m) k
  have hRpow : 1 ≤ R ^ (((a + b : ℕ) : ℝ) / ((s : ℝ) + 1)) :=
    Real.one_le_rpow hR (spatialOrder_fraction_nonneg (a + b) s)
  by_cases hb0 : b = 0
  · subst b
    let i : Fin (s + 1) × Fin (K + 1) := (⟨a, by omega⟩, ⟨k, by omega⟩)
    let Jrad : SmoothDirections U (fun y => iteratedDeriv a (f m y) t.1) :=
      J.congr (fun y _ => by
        simp only [mixedDerivative_radialFunction, ite_true])
    have hprod : (∏ j, q (v j)) ≤ 1 := Finset.prod_le_one₀
      (fun j _ => apply_nonneg _ _) (fun j _ => (hqp _).trans (hv j))
    have hcoef : 0 ≤ c i * E m ^ A i * parameterHeightWeight (H m) k :=
      mul_nonneg (mul_nonneg (hc i).le (Real.rpow_nonneg (zero_le_one.trans (hE m)) _)) hW
    have hbound := (hb i m t.1 ht.1 Jrad x hx v).trans
      ((mul_le_mul_of_nonneg_left hprod hcoef).trans_eq (mul_one _))
    have henv : c i * E m ^ A i ≤ C * E m ^ B := mul_le_mul (hcC i)
      (Real.rpow_le_rpow_of_exponent_le (hE m) (hAB i))
      (Real.rpow_nonneg (zero_le_one.trans (hE m)) _) (zero_le_one.trans hC)
    exact (hbound.trans (mul_le_mul_of_nonneg_right henv hW)).trans
      (le_mul_of_one_le_right
        (mul_nonneg (mul_nonneg (zero_le_one.trans hC)
          (Real.rpow_nonneg (zero_le_one.trans (hE m)) _)) hW) hRpow)
  · let Jzero : SmoothDirections U (fun _ : X => (0 : ℝ)) :=
      J.congr (fun y _ => by
        simp only [mixedDerivative_radialFunction, if_neg hb0])
    have hz : J.D k x v = 0 := by
      by_cases hk0 : k = 0
      · subst k
        exact smoothDirections_D_zero_apply Jzero hx v
      · exact smoothDirections_D_constant Jzero (Nat.pos_of_ne_zero hk0) hx v
    rw [hz, norm_zero, mul_zero]
    exact mul_nonneg (mul_nonneg (mul_nonneg (zero_le_one.trans hC)
      (Real.rpow_nonneg (zero_le_one.trans (hE m)) _)) hW)
      (Real.rpow_nonneg (zero_le_one.trans hR) _)

/-- Convert the complete absolute-value material envelope to the norm
envelope before specializing the endpoint algebra to a concrete state. -/
private theorem endpointRadialLowJets_powerBounds_of_abs
    (p : ℕ → Seminorm ℝ X) (q : Seminorm ℝ X)
    (center : X) (base loss : ℕ) (hqp : ∀ v, q v ≤ p base v)
    {U : Set X} (I : ι → Set ℝ) (δ : ι → ℝ → ℝ) (H E : ι → ℝ)
    (hH : ∀ m, 0 ≤ H m) (hE : ∀ m, 1 ≤ E m)
    (f : ι → X → ℝ → ℝ)
    (hraw : ∀ n k : ℕ, ∃ C A : ℝ, 0 < C ∧ 0 < A ∧
      ∀ m r, r ∈ I m →
      ∀ J : SmoothDirections U (fun x => iteratedDeriv n (f m x) r),
      ∀ x ∈ U, ∀ v : Fin k → X,
        δ m r ^ n * |J.D k x v| ≤
          C * E m ^ A * parameterHeightWeight (H m) k * ∏ i, q (v i)) :
    EndpointMixedPowerBounds p center base loss U (fun m => I m ×ˢ univ)
      (fun m t => δ m t.1) (fun m _ => H m) (fun m _ => E m)
      (fun m x t => f m x t.1) := by
  apply endpointRadialLowJets_powerBounds p q center base loss hqp I δ H E hH hE f
  intro n k
  obtain ⟨C, A, hC, hA, hb⟩ := hraw n k
  exact ⟨C, A, hC, hA.le, fun m r hr J x hx v => by
    simpa only [Real.norm_eq_abs] using hb m r hr J x hx v⟩

/-- Radial towers need exist only on the same original parameter domain. -/
def radialMixedRegularityOn
    {U : Set X} {I : Set ℝ} (hU : IsOpen U) (f : X → ℝ → ℝ)
    (hf : ∀ x ∈ U, ContDiffOn ℝ ∞ (f x) I)
    (Jr : ∀ n r, r ∈ I → SmoothDirections U (fun x => iteratedDeriv n (f x) r)) :
    MixedJetRegularity U (I ×ˢ univ) (fun x t => f x t.1) where
  spatial x hx := (hf x hx).comp contDiffOn_fst (fun _ ht => ht.1)
  parameter a b t ht := by
    by_cases hb : b = 0
    · subst b
      exact (Jr a t.1 ht.1).congr (fun x _ => by
        simp only [mixedDerivative_radialFunction, ite_true])
    · exact (smoothDirections_constant hU (0 : ℝ)).congr (fun _ _ => by
        simp only [mixedDerivative_radialFunction, if_neg hb])

end ContinuousFlexibility.Analysis

namespace ContinuousFlexibility.Statements

open Set Filter ContinuousFlexibility.Analysis ContinuousFlexibility.Blueprint
open scoped ContDiff Topology BigOperators

set_option backward.isDefEq.respectTransparency true

private abbrev opticalEndpointStateTopology (S : PhysicalSpacesData) :
    TopologicalSpace (AnnularState S) := inferInstance
attribute [local instance] opticalEndpointStateTopology
private abbrev opticalEndpointStateGroup (S : PhysicalSpacesData) :
    AddCommGroup (AnnularState S) := inferInstance
attribute [local instance] opticalEndpointStateGroup
private abbrev opticalEndpointStateModule (S : PhysicalSpacesData) :
    Module ℝ (AnnularState S) := inferInstance
attribute [local instance] opticalEndpointStateModule
private abbrev opticalEndpointStateSMul (S : PhysicalSpacesData) : SMul ℝ (AnnularState S) :=
  (opticalEndpointStateModule S).toDistribMulAction.toDistribSMul.toSMul
attribute [local instance] opticalEndpointStateSMul

def stateOpticalRootField (D : ReferenceData) (S : PhysicalSpacesData)
    (C : NonlinearGeometryData S) (z : AnnularState S × ℝ) (t : PolarPoint) : ℝ :=
  Real.sqrt (-deriv (stateProfile D S C z.1) t.1 / (t.1 * stateProfile D S C z.1 t.1))

/-- Spatial smoothness and all actual parameter towers on the positive
optical domain, with the unchanged state and control witnesses. -/
def stateOpticalRoot_regular
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S}
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    (hA : N01PartA D T S C)
    {U : Set (AnnularState S × ℝ)} (hU : IsOpen U)
    (hpos : ∀ z ∈ U, ∀ m r, r ∈ Ioo (C.left m) (C.right m) →
      0 < -deriv (stateProfile D S C z.1) r / (r * stateProfile D S C z.1 r)) (m : ℕ) :
    MixedJetRegularity U (Ioo (C.left m) (C.right m) ×ˢ univ)
      (stateOpticalRootField D S C) := by
  let f : (AnnularState S × ℝ) → ℝ → ℝ := fun z r =>
    Real.sqrt (-deriv (stateProfile D S C z.1) r / (r * stateProfile D S C z.1 r))
  have hD := hA.1.1.choose_spec.1
  have hC := hA.2.2.1
  have hf (z) (hz : z ∈ U) : ContDiffOn ℝ ∞ (f z) (Ioo (C.left m) (C.right m)) := by
    intro r hr
    have hcore : r ∈ Ioo D.a D.b :=
      ⟨(hC.1 m).1.trans hr.1, hr.2.trans (hC.1 m).2.2⟩
    let q : ℝ → ℝ := fun s => referenceOpticalSquare D s -
      stateKappa S z.1 m * controlOpticalFactor C m s
    have hq : ContDiffAt ℝ ∞ q r :=
      (referenceOpticalSquare_contDiffAt hD hcore).sub
        (contDiffAt_const.mul (controlOpticalFactor_contDiffAt hD hC m hr))
    have he (s) (hs : s ∈ Ioo (C.left m) (C.right m)) :
        -deriv (stateProfile D S C z.1) s / (s * stateProfile D S C z.1 s) = q s := by
      simpa only [q, referenceOpticalSquare, controlOpticalFactor, mul_div_assoc] using
        n01_stateProfile_opticalSquare_eq hA z.1 m hs
    have hqr : 0 < q r := (he r hr) ▸ hpos z hz m r hr
    apply ((hq.sqrt hqr.ne').congr_of_eventuallyEq ?_).contDiffWithinAt
    filter_upwards [isOpen_Ioo.mem_nhds hr] with s hs
    exact congrArg Real.sqrt (he s hs)
  exact radialMixedRegularityOn hU f hf (fun n r hr =>
    stateOpticalRadialJetSmoothDirections hS hT hA m n r hr hU
      (fun z hz => hpos z hz m r hr))

theorem n01_stateOpticalRoot_endpoint_powerBounds
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S}
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    (hA : N01PartA D T S C)
    (hE : ∀ r ∈ Ioo D.a D.b, 1 ≤ T.E0 r)
    (hloc : ∀ m, Ioo (C.left m) (C.right m) ⊆ D.cells (C.cell m))
    {base loss : ℕ} {ε c₀ K : ℝ} (hε : 0 < ε) (hc₀ : 0 < c₀) (hK : 0 < K)
    (hlower : ∀ z ∈ stateNeighborhood S C base ε, ∀ m r,
      r ∈ Ioo (C.left m) (C.right m) →
        c₀ * T.E0 (T.sample (C.cell m)) ^ (-K) *
            min (r - C.left m) (C.right m - r) ≤
          -deriv (stateProfile D S C z.1) r / (r * stateProfile D S C z.1 r)) :
    EndpointMixedPowerBounds (pairGrading (stateGrading S) realGrading)
      (C.referenceState, 0) base loss (stateNeighborhood S C base ε)
      (fun m => Ioo (C.left m) (C.right m) ×ˢ univ)
      (fun m q => min (q.1 - C.left m) (C.right m - q.1))
      (fun m _ => T.H (T.sample (C.cell m)) ^ (3 / 4 : ℝ))
      (fun m _ => T.E0 (T.sample (C.cell m)))
      (fun _ => stateOpticalRootField D S C) := by
  exact endpointRadialLowJets_powerBounds_of_abs
    (pairGrading (stateGrading S) realGrading) (pairGrading (stateGrading S) realGrading 0)
    (C.referenceState, 0) base loss
    (fun v => jointStateGrading_monotone S (Nat.zero_le base) v)
    (fun m => Ioo (C.left m) (C.right m))
    (fun m r => min (r - C.left m) (C.right m - r))
    (fun m => T.H (T.sample (C.cell m)) ^ (3 / 4 : ℝ))
    (fun m => T.E0 (T.sample (C.cell m)))
    (fun m => Real.rpow_nonneg
      (hT.2.1 _ (materialSample_mem_radialCore hT hA.1.1.choose_spec.2.1 (C.cell m))).2.1.le _)
    (fun m => hE _
      (materialSample_mem_radialCore hT hA.1.1.choose_spec.2.1 (C.cell m)))
    (fun _ z r => Real.sqrt (-deriv (stateProfile D S C z.1) r /
      (r * stateProfile D S C z.1 r)))
    (n01_stateOpticalRadialJet_material_bounds hS hT hA hE hloc hε hc₀ hK hlower)

/-- The original reference lower bound produces both the true mixed
towers and their endpoint power bounds on one common neighbourhood. -/
theorem n01_exists_stateOpticalRoot_endpoint_powerBounds
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S}
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    (hA : N01PartA D T S C)
    (hE : ∀ r ∈ Ioo D.a D.b, 1 ≤ T.E0 r)
    (hloc : ∀ m, Ioo (C.left m) (C.right m) ⊆ D.cells (C.cell m))
    (hlower : ∃ K : ℝ, 0 < K ∧ ∀ m r,
      r ∈ Ioo (C.left m) (C.right m) →
        K⁻¹ * T.E0 (T.sample (C.cell m)) ^ (-K) *
            min (r - C.left m) (C.right m - r) ≤ -deriv D.w r / (r * D.w r)) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε : ℝ, 0 < ε → ε ≤ ε₀ → ∀ base loss : ℕ,
      Nonempty (∀ m, MixedJetRegularity (stateNeighborhood S C base ε)
        (Ioo (C.left m) (C.right m) ×ˢ univ) (stateOpticalRootField D S C)) ∧
      EndpointMixedPowerBounds (pairGrading (stateGrading S) realGrading)
        (C.referenceState, 0) base loss (stateNeighborhood S C base ε)
        (fun m => Ioo (C.left m) (C.right m) ×ˢ univ)
        (fun m q => min (q.1 - C.left m) (C.right m - q.1))
        (fun m _ => T.H (T.sample (C.cell m)) ^ (3 / 4 : ℝ))
        (fun m _ => T.E0 (T.sample (C.cell m)))
        (fun _ => stateOpticalRootField D S C) := by
  obtain ⟨ε₀, hε₀, hb⟩ := n01_exists_common_opticalBounds_of_referenceLower hS hT hA hlower
  obtain ⟨K, hK, hQ⟩ := hlower
  have hc : 0 < K⁻¹ / 2 := div_pos (inv_pos.mpr hK) (by norm_num)
  refine ⟨ε₀, hε₀, fun ε hε hε₀' base loss => ?_⟩
  have hlow (z) (hz : z ∈ stateNeighborhood S C base ε) (m r)
      (hr : r ∈ Ioo (C.left m) (C.right m)) :
      (K⁻¹ / 2) * T.E0 (T.sample (C.cell m)) ^ (-K) *
          min (r - C.left m) (C.right m - r) ≤
        -deriv (stateProfile D S C z.1) r / (r * stateProfile D S C z.1 r) := by
    calc
      _ = (K⁻¹ * T.E0 (T.sample (C.cell m)) ^ (-K) *
          min (r - C.left m) (C.right m - r)) / 2 := by ring
      _ ≤ (-deriv D.w r / (r * D.w r)) / 2 :=
        div_le_div_of_nonneg_right (hQ m r hr) (by norm_num)
      _ ≤ _ := (hb base z (stateNeighborhood_subset le_rfl hε₀' hz) m r hr).2.1
  have hpos (z) (hz : z ∈ stateNeighborhood S C base ε) (m r)
      (hr : r ∈ Ioo (C.left m) (C.right m)) :
      0 < -deriv (stateProfile D S C z.1) r / (r * stateProfile D S C z.1 r) := by
    have hs := materialSample_mem_radialCore hT hA.1.1.choose_spec.2.1 (C.cell m)
    exact (mul_pos (mul_pos hc (Real.rpow_pos_of_pos
      (zero_lt_one.trans_le (hE _ hs)) _))
        (lt_min (sub_pos.mpr hr.1) (sub_pos.mpr hr.2))).trans_le (hlow z hz m r hr)
  exact ⟨⟨fun m => stateOpticalRoot_regular hS hT hA (isOpen_stateNeighborhood S C base ε) hpos m⟩,
    n01_stateOpticalRoot_endpoint_powerBounds hS hT hA hE hloc hε hc hK hlow⟩

end ContinuousFlexibility.Statements
