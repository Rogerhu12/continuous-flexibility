import ContinuousFlexibility.Analysis.N01SectorFlowTower
import ContinuousFlexibility.Analysis.SmoothDirectionsOneHighLimit
import ContinuousFlexibility.Analysis.MaterialSampleCofinite
import Mathlib.Topology.Sequences

/-!
# Actual parameter jets at every closed N01 flow radius

The endpoint is approached through interior radii. N01 supplies genuine
parameter towers there, and uniqueness identifies the witnesses for all
orders. The uniform next-two-jet bounds produce an actual smooth limit
tower. The original sharp one-high-factor bound passes to that tower
without changing its height power, material loss, or uniform constant.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

local instance n01EndpointParameterTowerStateSMul (S : PhysicalSpacesData) : SMul ℝ (AnnularState S) := Prod.instSMul
local instance n01EndpointParameterTowerRealNormedSpace : NormedSpace ℝ ℝ :=
    NormedField.toNormedSpace

open Set Filter ContinuousFlexibility.Analysis
open scoped Topology ContDiff

private theorem exists_interior_sequence_of_mem_Icc
    {l r x : ℝ} (hlr : l < r) (hx : x ∈ Icc l r) :
    ∃ u : ℕ → ℝ, (∀ i, u i ∈ Ioo l r) ∧ Tendsto u atTop (𝓝 x) := by
  have hclosure : x ∈ closure (Ioo l r) := by
    rw [closure_Ioo hlr.ne]
    exact hx
  exact mem_closure_iff_seq_limit.mp hclosure

/-- The limiting argument is scalar and independent of the realization
of the parameter space. Its sharp bound is retained separately from the
larger bounds used to construct the limit tower. -/
private theorem closed_parameter_tower_of_interior_towers
    {E : Type*} [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
    [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]
    (p : ℕ → Seminorm ℝ E) (hp : ∀ n, Continuous (p n)) (hmono : Monotone p)
    {U : Set E} (base : ℕ) (high : ℕ → ℕ)
    (hU : IsOpen U) (hc : Convex ℝ U)
    {l r x : ℝ} (hlr : l < r) (hx : x ∈ Icc l r)
    (f : ℝ → E → ℝ)
    (hcontinuous : ∀ z ∈ U, ContinuousOn (fun t => f t z) (Icc l r))
    (htowers : ∀ n, ∃ A : ℝ, 0 ≤ A ∧ ∀ t ∈ Ioo l r,
      ∃ J : SmoothDirections U (f t), ∀ z ∈ U, ∀ v : Fin n → E,
        |J.D n z v| ≤ A * oneHighVariationWeight p base (high n) z v)
    (k sharpHigh : ℕ) (B : ℝ)
    (hsharp : ∀ t ∈ Ioo l r,
      ∃ J : SmoothDirections U (f t), ∀ z ∈ U, ∀ v : Fin k → E,
        |J.D k z v| ≤ B * oneHighVariationWeight p base sharpHigh z v) :
    ∃ K : SmoothDirections U (f x), ∀ z ∈ U, ∀ v : Fin k → E,
      |K.D k z v| ≤ B * oneHighVariationWeight p base sharpHigh z v := by
  classical
  obtain ⟨rseq, hrseq, htendsto⟩ := exists_interior_sequence_of_mem_Icc hlr hx
  let hstart := htowers 0
  let J : ∀ i : ℕ, SmoothDirections U (f (rseq i)) :=
    fun i => (hstart.choose_spec.2 (rseq i) (hrseq i)).choose
  have hwithin : Tendsto rseq atTop (𝓝[Icc l r] x) :=
    tendsto_nhdsWithin_iff.mpr ⟨htendsto,
      Eventually.of_forall (fun i => ⟨(hrseq i).1.le, (hrseq i).2.le⟩)⟩
  have hzero : ∀ z ∈ U, Tendsto (fun i => f (rseq i) z) atTop (𝓝 (f x z)) := by
    intro z hz
    exact ((hcontinuous z hz) x hx).tendsto.comp hwithin
  have hbounds : ∀ n, ∃ A : ℝ, 0 ≤ A ∧ ∀ i z, z ∈ U → ∀ v : Fin n → E,
      |(J i).D n z v| ≤ A * oneHighVariationWeight p base (high n) z v := by
    intro n
    obtain ⟨A, hA, hn⟩ := htowers n
    refine ⟨A, hA, ?_⟩
    intro i z hz v
    obtain ⟨Jn, hJn⟩ := hn (rseq i) (hrseq i)
    have heq : (J i).D n z v = Jn.D n z v :=
      congrArg (fun L => L v) ((J i).unique Jn n z hz)
    exact (congrArg abs heq).trans_le (hJn z hz v)
  obtain ⟨K, hK⟩ := exists_smoothDirections_limit_of_oneHigh_bounds
    p hp hmono base high J hU hc hzero hbounds
  refine ⟨K, ?_⟩
  intro z hz v
  apply abs_directionalJet_limit_le J K (hK k z hz v)
  intro i
  obtain ⟨Ji, hJi⟩ := hsharp (rseq i) (hrseq i)
  have heq : (J i).D k z v = Ji.D k z v :=
    congrArg (fun L => L v) ((J i).unique Ji k z hz)
  exact (congrArg abs heq).trans_le (hJi z hz v)

private theorem N01Properties.sectorFlow_closed_tower_point
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {base loss : ℕ} {ε : ℝ}
    (hN : N01Properties D T S C base loss ε)
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T) (k s : ℕ)
    (B : ℝ)
    (hdata : ∀ m b θ r, b ≤ s → r ∈ Ioo (C.left m) (C.right m) →
      ∃ J : SmoothDirections (sectorNeighborhood S base ε ε)
        (fun z => ordinaryFlowFamily S C m 0 b (r, θ) (liftSectorParameter S C z)),
      ∀ z ∈ sectorNeighborhood S base ε ε, ∀ v : Fin k → (StateDirections S × ℝ),
        |J.D k z v| ≤ B * T.H (T.sample (C.cell m)) ^ (3 / 4 : ℝ) *
          T.E0 (T.sample (C.cell m)) ^ B *
          oneHighVariationWeight (pairGrading (sectorGrading S) realGrading)
            base (s + loss) z v)
    (m b : ℕ) (θ r : ℝ) (hb : b ≤ s) (hr : r ∈ Icc (C.left m) (C.right m)) :
      ∃ J : SmoothDirections (sectorNeighborhood S base ε ε)
        (fun z => ordinaryFlowFamily S C m 0 b (r, θ) (liftSectorParameter S C z)),
      ∀ z ∈ sectorNeighborhood S base ε ε, ∀ v : Fin k → (StateDirections S × ℝ),
        |J.D k z v| ≤ B * T.H (T.sample (C.cell m)) ^ (3 / 4 : ℝ) *
          T.E0 (T.sample (C.cell m)) ^ B *
          oneHighVariationWeight (pairGrading (sectorGrading S) realGrading)
            base (s + loss) z v := by
  classical
  have hsamples := materialSample_mem_radialCore hT hN.1.1.choose_spec.2.1
  have hH (m : ℕ) : 0 < T.H (T.sample m) := (hT.2.1 _ (hsamples m)).2.1
  have hE (m : ℕ) : 0 < T.E0 (T.sample m) := (hT.2.1 _ (hsamples m)).2.2.1
  have hcontrol : controlGeometryConditions D S C := hN.2.2.2.1
  have hcontinuous : ∀ z ∈ sectorNeighborhood S base ε ε,
      ContinuousOn (fun t => ordinaryFlowFamily S C m 0 b (t, θ)
        (liftSectorParameter S C z)) (Icc (C.left m) (C.right m)) := by
    intro z hz
    exact hN.ordinaryFlowFamily_radial_continuousOn hS hT
      (liftSectorParameter_mem_stateNeighborhood hz (le_refl ε))
      (hN.2.2.1.liftSectorParameter_sector z) m b θ
  have hbounds : ∀ n, ∃ A : ℝ, 0 ≤ A ∧ ∀ t ∈ Ioo (C.left m) (C.right m),
      ∃ J : SmoothDirections (sectorNeighborhood S base ε ε)
        (fun z => ordinaryFlowFamily S C m 0 b (t, θ) (liftSectorParameter S C z)),
      ∀ z ∈ sectorNeighborhood S base ε ε, ∀ v : Fin n → (StateDirections S × ℝ),
      |J.D n z v| ≤ A *
        oneHighVariationWeight (pairGrading (sectorGrading S) realGrading)
          base (b + loss) z v := by
    intro n
    let hraw := hN.sectorFlow_tower n b
    let A : ℝ := hraw.choose
    refine ⟨A * T.H (T.sample (C.cell m)) ^ (3 / 4 : ℝ) *
      T.E0 (T.sample (C.cell m)) ^ A,
      mul_nonneg (mul_nonneg hraw.choose_spec.1.le (Real.rpow_nonneg (hH _).le _))
        (Real.rpow_nonneg (hE _).le _), ?_⟩
    intro t ht
    exact hraw.choose_spec.2 m b θ t le_rfl ht
  exact closed_parameter_tower_of_interior_towers
    (pairGrading (sectorGrading S) realGrading)
    (sectorPairGrading_continuous S) (sectorPairGrading_monotone S)
    base (fun _ => b + loss) (sectorNeighborhood_isOpen S base ε ε)
    (sectorNeighborhood_convex S base ε ε) (hcontrol.1 m).2.1 hr
    (fun t z => ordinaryFlowFamily S C m 0 b (t, θ) (liftSectorParameter S C z))
    hcontinuous hbounds k (s + loss)
    (B * T.H (T.sample (C.cell m)) ^ (3 / 4 : ℝ) * T.E0 (T.sample (C.cell m)) ^ B)
    (fun t ht => hdata m b θ t hb ht)

theorem N01Properties.sectorFlow_closed_tower
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {base loss : ℕ} {ε : ℝ}
    (hN : N01Properties D T S C base loss ε)
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T) (k s : ℕ) :
    ∃ B : ℝ, 0 < B ∧ ∀ m b θ r, b ≤ s → r ∈ Icc (C.left m) (C.right m) →
      ∃ J : SmoothDirections (sectorNeighborhood S base ε ε)
        (fun z => ordinaryFlowFamily S C m 0 b (r, θ) (liftSectorParameter S C z)),
      ∀ z ∈ sectorNeighborhood S base ε ε, ∀ v : Fin k → (StateDirections S × ℝ),
        |J.D k z v| ≤ B * T.H (T.sample (C.cell m)) ^ (3 / 4 : ℝ) *
          T.E0 (T.sample (C.cell m)) ^ B *
          oneHighVariationWeight (pairGrading (sectorGrading S) realGrading)
            base (s + loss) z v := by
  let hdata := hN.sectorFlow_tower k s
  exact ⟨hdata.choose, hdata.choose_spec.1,
    hN.sectorFlow_closed_tower_point hS hT k s hdata.choose hdata.choose_spec.2⟩

end ContinuousFlexibility.Statements
