import ContinuousFlexibility.Analysis.N01SectorFlowTower
import ContinuousFlexibility.Analysis.SmoothDirectionsLocalLabels
import ContinuousFlexibility.Analysis.N01OpticalCollarJetBounds

/-!
# Actual mixed flow towers in sector coordinates

The radial endpoint factor of the original N01 estimate is retained.
On a fixed closed radial interval in one negative component it gives a
uniform seminorm bound for every angular label. These local bounds are
used for genuine joint radial and state differentiability; the sharper
original spatial budget remains available in the weighted theorem.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace ContinuousFlexibility.Statements

local instance n01FlowMixedParameterTowerStateSMul (S : PhysicalSpacesData) :
    SMul ℝ (AnnularState S) := Prod.instSMul

open Set ContinuousFlexibility.Analysis
open scoped Topology BigOperators

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {base loss : ℕ} {ε : ℝ}

theorem N01Properties.sectorFlow_mixed_tower
    (hN : N01Properties D T S C base loss ε) (k s : ℕ) :
    ∃ B : ℝ, 0 < B ∧ ∀ m a b p, a + b ≤ s →
      p.1 ∈ Ioo (C.left m) (C.right m) →
      ∃ J : SmoothDirections (sectorNeighborhood S base ε ε)
        (fun z => ordinaryFlowFamily S C m a b p (liftSectorParameter S C z)),
      ∀ z ∈ sectorNeighborhood S base ε ε, ∀ v : Fin k → (StateDirections S × ℝ),
        min (p.1 - C.left m) (C.right m - p.1) ^ a * |J.D k z v| ≤
          B * T.H (T.sample (C.cell m)) ^ (3 / 4 : ℝ) *
            T.E0 (T.sample (C.cell m)) ^ B *
            oneHighVariationWeight (pairGrading (sectorGrading S) realGrading)
              base (s + loss) z v := by
  let data := hN.2.2.2.2.2.2.2.2.2.2.2.2 k s
  let B : ℝ := data.choose
  have hB : 0 < B := data.choose_spec.1
  refine ⟨B, hB, ?_⟩
  intro m a b p hab hp
  let pointData := data.choose_spec.2 m a b p hab hp
  let J := pointData.choose
  have hmap : MapsTo (fun z : StateDirections S × ℝ =>
      (C.referenceState, 0) + sectorParameterInclusion S z)
      (sectorNeighborhood S base ε ε) (stateNeighborhood S C base ε) := by
    intro z hz
    exact Eq.mp
      (congrArg (fun u : AnnularState S × ℝ => u ∈ stateNeighborhood S C base ε)
        (liftSectorParameter_eq_affine S C z))
      (liftSectorParameter_mem_stateNeighborhood hz le_rfl)
  let K : SmoothDirections (sectorNeighborhood S base ε ε)
      (fun z => ordinaryFlowFamily S C m a b p (liftSectorParameter S C z)) :=
    (J.compAffine (sectorParameterInclusion S) (C.referenceState, 0)
      (sectorNeighborhood_isOpen S base ε ε) hmap).congrOn
      (fun z _ => congrArg (ordinaryFlowFamily S C m a b p)
        (liftSectorParameter_eq_affine S C z).symm)
  refine ⟨K, ?_⟩
  intro z hz v
  have heq : K.D k z v = J.D k (liftSectorParameter S C z)
      (fun i => sectorParameterInclusion S (v i)) :=
    congrArg (fun y => J.D k y (fun i => sectorParameterInclusion S (v i)))
      (liftSectorParameter_eq_affine S C z).symm
  have hraw := pointData.choose_spec (liftSectorParameter S C z)
    (liftSectorParameter_mem_stateNeighborhood hz le_rfl)
    (fun i => sectorParameterInclusion S (v i))
  rw [heq]
  exact hraw.trans_eq (congrArg (fun W : ℝ =>
    B * T.H (T.sample (C.cell m)) ^ (3 / 4 : ℝ) *
      T.E0 (T.sample (C.cell m)) ^ B * W)
    (oneHighVariationWeight_sector_lift S C base (s + loss) z v))

def N01Properties.sectorFlowMixedTower
    (hN : N01Properties D T S C base loss ε)
    (m a b : ℕ) (p : PolarPoint) (hp : p.1 ∈ Ioo (C.left m) (C.right m)) :
    SmoothDirections (sectorNeighborhood S base ε ε)
      (fun z => ordinaryFlowFamily S C m a b p (liftSectorParameter S C z)) :=
  ((hN.sectorFlow_mixed_tower 0 (a + b)).choose_spec.2 m a b p le_rfl hp).choose

theorem N01Properties.sectorFlowMixedTower_bound
    (hN : N01Properties D T S C base loss ε) (k s : ℕ) :
    ∃ B : ℝ, 0 < B ∧ ∀ m a b p (hab : a + b ≤ s)
      (hp : p.1 ∈ Ioo (C.left m) (C.right m)),
      ∀ z ∈ sectorNeighborhood S base ε ε, ∀ v : Fin k → (StateDirections S × ℝ),
        min (p.1 - C.left m) (C.right m - p.1) ^ a *
            |(hN.sectorFlowMixedTower m a b p hp).D k z v| ≤
          B * T.H (T.sample (C.cell m)) ^ (3 / 4 : ℝ) *
            T.E0 (T.sample (C.cell m)) ^ B *
            oneHighVariationWeight (pairGrading (sectorGrading S) realGrading)
              base (s + loss) z v := by
  let data := hN.sectorFlow_mixed_tower k s
  refine ⟨data.choose, data.choose_spec.1, ?_⟩
  intro m a b p hab hp z hz v
  let pointData := data.choose_spec.2 m a b p hab hp
  let K := pointData.choose
  have heq := (hN.sectorFlowMixedTower m a b p hp).unique K k z hz
  have hvalue : (hN.sectorFlowMixedTower m a b p hp).D k z v = K.D k z v :=
    congrArg (fun A : (StateDirections S × ℝ) [×k]→L[ℝ] ℝ => A v) heq
  rw [hvalue]
  exact pointData.choose_spec z hz v

theorem N01Properties.sectorFlowMixedTower_uniform_on_radial_interval
    (hN : N01Properties D T S C base loss ε) (hT : IsMaterialData D T)
    (m a b : ℕ) (l h : ℝ) (hl : C.left m < l) (hh : h < C.right m) :
    UniformScalarJetSeminormBounds
      (fun p : Icc l h × ℝ => hN.sectorFlowMixedTower m a b (p.1, p.2)
        ⟨hl.trans_le p.1.property.1, p.1.property.2.trans_lt hh⟩) := by
  intro n
  let data := hN.sectorFlowMixedTower_bound n (a + b)
  let B : ℝ := data.choose
  have hB : 0 < B := data.choose_spec.1
  let d : ℝ := min (l - C.left m) (C.right m - h)
  have hd : 0 < d := lt_min (sub_pos.mpr hl) (sub_pos.mpr hh)
  let q : Seminorm ℝ (StateDirections S × ℝ) :=
    pairGrading (sectorGrading S) realGrading (max base (a + b + loss))
  let W : ℝ := B * T.H (T.sample (C.cell m)) ^ (3 / 4 : ℝ) *
    T.E0 (T.sample (C.cell m)) ^ B
  have hsample := materialSample_mem_radialCore hT hN.1.1.choose_spec.2.1 (C.cell m)
  have hweights := hT.2.1 _ hsample
  have hW : 0 ≤ W := mul_nonneg
    (mul_nonneg hB.le (Real.rpow_nonneg hweights.2.1.le _))
    (Real.rpow_nonneg hweights.2.2.1.le _)
  let A : ℝ := d⁻¹ ^ a * W * ((n : ℝ) + 1)
  have hA : 0 ≤ A := mul_nonneg
    (mul_nonneg (pow_nonneg (inv_nonneg.mpr hd.le) a) hW)
    (add_nonneg (Nat.cast_nonneg _) zero_le_one)
  refine ⟨q, A, sectorPairGrading_continuous S _, hA, ?_⟩
  intro p z hz v
  have hp : (p.1 : ℝ) ∈ Ioo (C.left m) (C.right m) :=
    ⟨hl.trans_le p.1.property.1, p.1.property.2.trans_lt hh⟩
  have hdist : d ≤ min ((p.1 : ℝ) - C.left m) (C.right m - p.1) :=
    min_le_min (sub_le_sub_right p.1.property.1 _) (sub_le_sub_left p.1.property.2 _)
  have hdp : 0 < min ((p.1 : ℝ) - C.left m) (C.right m - p.1) := hd.trans_le hdist
  have hraw := data.choose_spec.2 m a b (p.1, p.2) le_rfl hp z hz v
  have hbound := abs_le_of_power_weight_bound (K := d⁻¹)
    (E := (1 : ℝ)) (A := (0 : ℝ)) a
    hdp zero_lt_one (by
      simpa only [Real.one_rpow, mul_one, one_div] using
        (one_div_le_one_div_of_le hd hdist)) hraw
  have hw := oneHighVariationWeight_le_seminorm_product
    (pairGrading (sectorGrading S) realGrading) q base (a + b + loss)
    (sectorPairGrading_monotone S (le_max_left _ _))
    (sectorPairGrading_monotone S (le_max_right _ _)) z v
  have hbound' : |(hN.sectorFlowMixedTower m a b (p.1, p.2) hp).D n z v| ≤
      d⁻¹ ^ a * (W * oneHighVariationWeight
        (pairGrading (sectorGrading S) realGrading) base (a + b + loss) z v) := by
    simpa only [Real.one_rpow, mul_one, W, B] using hbound
  apply hbound'.trans
  have hmul := mul_le_mul_of_nonneg_left hw
    (mul_nonneg (pow_nonneg (inv_nonneg.mpr hd.le) a) hW)
  convert hmul using 1 <;> dsimp only [A] <;> ring

end ContinuousFlexibility.Statements
