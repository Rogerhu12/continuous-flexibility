module

public import ContinuousFlexibility.Analysis.N01EndpointAngularJets
public import ContinuousFlexibility.Analysis.N01FlowSmallness
public import ContinuousFlexibility.Analysis.N04RealizationDifferenceValue
public import ContinuousFlexibility.Analysis.MaterialEnvelopeNormalization
public import ContinuousFlexibility.Analysis.StateNeighborhood

/-!
# The actual closed-radius flow bounds in the current-jet normalization

The N01 angular towers already describe the actual ordinary-flow difference
at every radius of the closed component. Restriction retains those same
towers and all their sharp variation bounds. Integrating the first tower
from the reference parameter removes the additive constant in the value
estimate. One radius is chosen before every angular and parameter order.

These estimates retain the sampled height factor. They do not replace it
by a uniform upper bound, and make no assertion about unregularized radial
derivatives at a root.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set ContinuousFlexibility.Statements CanonicalGeometry

local instance n04NegativeFlowBoundsStateSMul (S : PhysicalSpacesData) :
    SMul ℝ (AnnularState S) := Prod.instSMul

/-- The sum grading is at most one on the same half-radius sector for
every physical-space realization. -/
theorem n04NegativeGeometry_parameterGrading_le_one
    (S : PhysicalSpacesData) (base : ℕ) {δ : ℝ} (hδ : δ ≤ 1 / 2)
    {z : Parameter S} (hz : z ∈ sectorNeighborhood S base δ δ) :
    parameterGrading S base z ≤ 1 := by
  change sectorGrading S base z.1 + |z.2| ≤ 1
  linarith [hz.1, hz.2]

/-- A genuine first parameter tower gives a value bound linear in the
displacement grading, with its external material factor unchanged. -/
theorem n04NegativeGeometry_sector_difference_bound
    {S : PhysicalSpacesData} {base high : ℕ} {ε δ : ℝ}
    {f : Parameter S → ℝ}
    (J : SmoothDirections (sectorNeighborhood S base ε ε) f)
    (hε : 0 < ε) (hδ : δ ≤ ε) (hhalf : δ ≤ 1 / 2)
    (horder : base ≤ high) (hzero : f 0 = 0)
    {M : ℝ} (hM : 0 ≤ M)
    (hfirst : ∀ y ∈ sectorNeighborhood S base ε ε, ∀ v : Fin 1 → Parameter S,
      |J.D 1 y v| ≤ M *
        oneHighVariationWeight (parameterGrading S) base high y v)
    {z : Parameter S} (hz : z ∈ sectorNeighborhood S base δ δ) :
    |f z| ≤ (3 * M) * parameterGrading S high z := by
  have hzold : z ∈ sectorNeighborhood S base ε ε :=
    sectorNeighborhood_mono S le_rfl hδ hδ hz
  have hzeroU : (0 : Parameter S) ∈ sectorNeighborhood S base ε ε :=
    ⟨(sectorGrading S base).map_zero'.trans_lt hε,
      (abs_zero : |(0 : ℝ)| = 0).trans_lt hε⟩
  have hsegment : ∀ t ∈ Icc (0 : ℝ) 1,
      (0 : Parameter S) + t • z ∈ sectorNeighborhood S base ε ε := by
    intro t ht
    have hm := sectorNeighborhood_convex S base ε ε hzeroU hzold
      (sub_nonneg.mpr ht.2) ht.1 (sub_add_cancel 1 t)
    simpa only [smul_zero, zero_add] using hm
  have hb := n04Realization_smoothDirections_difference_value_bound J
    (parameterGrading S) base high 0 z
    (sectorPairGrading_monotone S horder) hsegment
    (n04NegativeGeometry_parameterGrading_le_one S base hhalf hz) hM
    (fun y hy v => by simpa only [sub_zero] using hfirst y hy v)
  simpa only [zero_add, hzero, sub_zero] using hb

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {base loss : ℕ} {ε : ℝ}

/-- The same selected N01 tower restricted to one fixed neighborhood. -/
def n04NegativeGeometry_ordinaryFlow_angularTower
    (hN : N01Properties D T S C base loss ε)
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    (m : ℕ) (r : ℝ) (hr : r ∈ Icc (C.left m) (C.right m))
    (j : ℕ) (θ : ℝ) :
    SmoothDirections
      (sectorNeighborhood S base (min ε (1 / 2)) (min ε (1 / 2)))
      (fun z => ordinaryFlowFamily S C m 0 j (r, θ) (liftSectorParameter S C z)) :=
  (hN.sectorFlow_closed_angularTower hS hT m r hr j θ).restrict
    (sectorNeighborhood_isOpen S base (min ε (1 / 2)) (min ε (1 / 2)))
    (sectorNeighborhood_mono S le_rfl (min_le_left _ _) (min_le_left _ _))

/-- The neighborhood and tower family are fixed before every parameter
order. Only the loss depends on that order. -/
theorem n04NegativeGeometry_ordinaryFlow_angularTower_bound
    (hN : N01Properties D T S C base loss ε)
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T) (k : ℕ) :
    ∃ d : ℕ, ∀ s : ℕ, ∃ B : ℝ, 0 < B ∧
      ∀ m r (hr : r ∈ Icc (C.left m) (C.right m)) j θ, j ≤ s →
      ∀ z ∈ sectorNeighborhood S base (min ε (1 / 2)) (min ε (1 / 2)),
      ∀ v : Fin k → Parameter S,
        |(n04NegativeGeometry_ordinaryFlow_angularTower hN hS hT m r hr j θ).D k z v| ≤
          B * T.E0 (T.sample (C.cell m)) ^ B *
            T.H (T.sample (C.cell m)) ^ (3 / 4 : ℝ) *
              oneHighVariationWeight (parameterGrading S) base (s + d) z v := by
  let data := hN.sectorFlow_closed_angularTower_bound hS hT k
  refine ⟨loss + data.choose, fun s => ?_⟩
  let orderData := data.choose_spec s
  refine ⟨orderData.choose, orderData.choose_spec.1, ?_⟩
  intro m r hr j θ hjs z hz v
  have hzold : z ∈ sectorNeighborhood S base ε ε :=
    sectorNeighborhood_mono S le_rfl (min_le_left _ _) (min_le_left _ _) hz
  have hb := orderData.choose_spec.2 m r hr j θ hjs z hzold v
  exact hb.trans_eq (by
    simp only [parameterGrading, Nat.add_assoc]
    ring)

/-- At every angular order the true flow-reference difference has no
constant term. Its one loss is selected before the angular order, radius,
component, angle and state. -/
theorem n04NegativeGeometry_ordinaryFlow_angular_value_bound
    (hN : N01Properties D T S C base loss ε)
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    (hfloor : ∀ m, 1 ≤ T.E0 (T.sample (C.cell m))) :
    ∃ d : ℕ, ∀ s : ℕ, ∃ B : ℝ, 0 < B ∧
      ∀ m r (hr : r ∈ Icc (C.left m) (C.right m)) j θ, j ≤ s →
      ∀ z ∈ sectorNeighborhood S base (min ε (1 / 2)) (min ε (1 / 2)),
        |ordinaryFlowFamily S C m 0 j (r, θ) (liftSectorParameter S C z)| ≤
          B * T.E0 (T.sample (C.cell m)) ^ B *
            T.H (T.sample (C.cell m)) ^ (3 / 4 : ℝ) *
              parameterGrading S (s + d) z := by
  let data := hN.sectorFlow_closed_angularTower_bound hS hT 1
  let d : ℕ := max base (loss + data.choose)
  refine ⟨d, fun s => ?_⟩
  let orderData := data.choose_spec s
  let A : ℝ := orderData.choose
  have hA : 0 < A := orderData.choose_spec.1
  let packed := coefficientEnvelope_pack (3 * A) A
  let B : ℝ := packed.choose
  have hB : 0 < B := packed.choose_spec.1
  refine ⟨B, hB, ?_⟩
  intro m r hr j θ hjs z hz
  let J := hN.sectorFlow_closed_angularTower hS hT m r hr j θ
  let H : ℝ := T.H (T.sample (C.cell m)) ^ (3 / 4 : ℝ)
  let E : ℝ := T.E0 (T.sample (C.cell m))
  have hH : 0 ≤ H := Real.rpow_nonneg
    (hT.2.1 _ (materialSample_mem_interval hN.1.1 hT (C.cell m))).2.1.le _
  let M : ℝ := A * H * E ^ A
  have hM : 0 ≤ M := mul_nonneg (mul_nonneg hA.le hH)
    (Real.rpow_nonneg (zero_le_one.trans (hfloor m)) _)
  have hhigh : s + loss + data.choose ≤ s + d := by
    exact (Nat.add_assoc s loss data.choose).le.trans
      (Nat.add_le_add_left (le_max_right base (loss + data.choose)) s)
  have hfirst : ∀ y ∈ sectorNeighborhood S base ε ε,
      ∀ v : Fin 1 → Parameter S, |J.D 1 y v| ≤
        M * oneHighVariationWeight (parameterGrading S) base (s + d) y v := by
    intro y hy v
    exact (orderData.choose_spec.2 m r hr j θ hjs y hy v).trans
      (mul_le_mul_of_nonneg_left
        (oneHighVariationWeight_mono (sectorPairGrading_monotone S)
          le_rfl hhigh y v) hM)
  have hlift : liftSectorParameter S C (0 : Parameter S) = (C.referenceState, 0) := by
    simp only [liftSectorParameter, Prod.fst_zero, Prod.snd_zero,
      ZeroMemClass.coe_zero, add_zero]
  have hzero : ordinaryFlowFamily S C m 0 j (r, θ)
      (liftSectorParameter S C (0 : Parameter S)) = 0 :=
    (congrArg (ordinaryFlowFamily S C m 0 j (r, θ)) hlift).trans
      (ordinaryFlowFamily_reference_zero S C m 0 j (r, θ))
  have hb := n04NegativeGeometry_sector_difference_bound J hN.2.1
    (min_le_left _ _) (min_le_right _ _)
    ((le_max_left base (loss + data.choose)).trans (Nat.le_add_left d s))
    hzero hM hfirst hz
  have hpack : (3 * A) * E ^ A ≤ B * E ^ B :=
    packed.choose_spec.2 E (hfloor m)
  calc
    _ ≤ (3 * M) * parameterGrading S (s + d) z := hb
    _ = ((3 * A) * E ^ A) * H * parameterGrading S (s + d) z := by
      dsimp only [M]
      ring
    _ ≤ (B * E ^ B) * H * parameterGrading S (s + d) z :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hpack hH)
        (apply_nonneg _ _)

end ContinuousFlexibility.Analysis

/-- info: 'ContinuousFlexibility.Analysis.n04NegativeGeometry_ordinaryFlow_angular_value_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ContinuousFlexibility.Analysis.n04NegativeGeometry_ordinaryFlow_angular_value_bound
