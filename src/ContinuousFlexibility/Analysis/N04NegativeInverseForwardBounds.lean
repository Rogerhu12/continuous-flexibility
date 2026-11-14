module

public import ContinuousFlexibility.Analysis.N04NegativeInverseReferenceBounds
public import ContinuousFlexibility.Analysis.N04NegativeInverseOverlap
public import ContinuousFlexibility.Analysis.N04NegativeInverseCurrentData
public import ContinuousFlexibility.Analysis.N04NegativeInversePureJointBounds
public import ContinuousFlexibility.Analysis.N04NegativeGeometryPhysicalAtomTowers
public import ContinuousFlexibility.Analysis.ActualNegativeOppositeRootFields
public import ContinuousFlexibility.Analysis.MaterialEndpointWeightTransport
public import ContinuousFlexibility.Analysis.N07aPhysicalAtomBounds

/-!
# Actual forward inputs on the two fixed negative reference halves

The two halves may store different material samples.  Their bounded
endpoint-coordinate separation transfers every prescribed height power
without changing that power.  The current/reference atom estimates then
give pure joint derivative bounds with their exact parameter and physical
arities, before the moving inverse point is selected.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set ContinuousFlexibility.Statements CanonicalGeometry
open scoped ContDiff BigOperators

attribute [local instance]
  n07aNonlinearAnnularGroup n07aNonlinearAnnularModule
  n07aNonlinearAnnularAddGroup n07aNonlinearAnnularSMul n07aNonlinearAnnularSub
  n07aNonlinearAnnularParameterGroup n07aNonlinearAnnularParameterModule
  n07aNonlinearAnnularParameterAddGroup n07aNonlinearAnnularParameterSMul
  n07aNonlinearAnnularParameterSub
  n07aNonlinearDirectionsGroup n07aNonlinearDirectionsModule
  n07aNonlinearDirectionsAddGroup n07aNonlinearDirectionsSMul n07aNonlinearDirectionsSub
  n07aNonlinearSectorParameterGroup n07aNonlinearSectorParameterModule
  n07aNonlinearSectorParameterAddGroup n07aNonlinearSectorParameterSMul
  n07aNonlinearSectorParameterSub

/-- A uniform estimate on an open reference half passes to its old cut
by continuity of the actual full-component field. -/
theorem n04NegativeInverse_le_on_closedHalf
    {f : PolarPoint → ℝ} {a b M : ℝ} (hab : a < b)
    {p : PolarPoint} (hp : p ∈ Icc a b ×ˢ (univ : Set ℝ))
    (hf : ContinuousAt f p)
    (hbound : ∀ q ∈ Ioo a b ×ˢ (univ : Set ℝ), f q ≤ M) : f p ≤ M := by
  have hpcl : p ∈ closure (Ioo a b ×ˢ (univ : Set ℝ)) := by
    rw [closure_prod_eq, closure_Ioo hab.ne, closure_univ]
    exact hp
  have hcl : f p ∈ closure (Iic M) :=
    hf.continuousWithinAt.mem_closure hpcl hbound
  simpa only [isClosed_Iic.closure_eq, mem_Iic] using hcl

private theorem n04NegativeInverse_remove_zero_height_weight
    {H H' a b M : ℝ}
    (h : H ^ (0 : ℝ) * a ≤ M * (H' ^ (0 : ℝ) * b)) : a ≤ M * b := by
  simpa only [Real.rpow_zero, one_mul] using h

namespace N04RealizationStart

variable (W : N04RealizationStart)

/-- The original parameter topology carries the interpolation supplied
by the physical spaces, including the scalar sector parameter. -/
theorem negativeInverse_parameterInterpolation :
    HasInterpolation (parameterGrading W.S) :=
  hasInterpolation_of_hasSmoothing (sectorPairGrading_monotone W.S)
    (hasSmoothing_pairGrading (solve_sector_hasSmoothing W.hS) hasSmoothing_realGrading)

/-- Both retained samples stay a bounded endpoint distance from the
same component endpoint, hence from one another. -/
theorem negativeInverse_pair_sample_endpointX (e : ℕ ≃ N04PieceIndex W.D) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ k k' m side side',
      e k = .inl (m, side) → e k' = .inl (m, side') →
        |endpointX 1 (Statements.endpointDistance W.D (W.U.sample ((W.A e).cell k'))) -
          endpointX 1 (Statements.endpointDistance W.D (W.U.sample ((W.A e).cell k)))| ≤ A := by
  have data := n04bActualTypedAtlas_negative_sample_endpointX
    W.hT W.hS W.through03 W.field e
  let A : ℝ := data.choose
  have hA : 0 ≤ A := data.choose_spec.1
  have hb := data.choose_spec.2
  refine ⟨A + A, add_nonneg hA hA, ?_⟩
  intro k k' m side side' hk hk'
  have hr : W.C.left m ∈ Icc (W.C.left m) (W.C.right m) :=
    ⟨le_rfl, (W.through03.1.1.2.2.2.1.1 m).2.1.le⟩
  have hleft := hb k m side hk (W.C.left m) hr
  have hright := hb k' m side' hk' (W.C.left m) hr
  exact (abs_sub_le _ (endpointX 1 (Statements.endpointDistance W.D (W.C.left m))) _).trans
    (add_le_add hright ((abs_sub_comm _ _).trans_le hleft))

/-- The prescribed height power survives transfer between either two
halves of one component.  Only the coefficient exponent changes. -/
theorem negativeInverse_pair_sample_weights
    (e : ℕ ≃ N04PieceIndex W.D) (γ P : ℝ) (hP : 0 ≤ P) :
    ∃ B A : ℝ, 0 < B ∧ 0 ≤ A ∧ ∀ k k' m side side',
      e k = .inl (m, side) → e k' = .inl (m, side') →
        W.U.H (W.U.sample ((W.A e).cell k')) ^ γ *
            W.U.E0 (W.U.sample ((W.A e).cell k')) ^ P ≤
          B * (W.U.H (W.U.sample ((W.A e).cell k)) ^ γ *
            W.U.E0 (W.U.sample ((W.A e).cell k)) ^ A) := by
  have hU := isMaterialData_enlargedMaterialData W.radial.1 W.hT
  obtain ⟨L, hL, hdist⟩ := W.negativeInverse_pair_sample_endpointX e
  obtain ⟨B, A, hB, hA, hb⟩ :=
    material_global_H_M_E0_rpow_bounded_X_shift hU W.radial.1 γ 0 hP hL
  refine ⟨B, A, hB, hA, ?_⟩
  intro k k' m side side' hk hk'
  simpa only [Real.rpow_zero, mul_one] using hb
    (W.U.sample ((W.A e).cell k')) (W.U.sample ((W.A e).cell k))
    (materialSample_mem_interval W.radial.1 hU _)
    (materialSample_mem_interval W.radial.1 hU _)
    (hdist k k' m side side' hk hk')

/-- The determinant transition is an identity of the stored chosen
charts, on their entire common physical component. -/
theorem negativeChart_opposite_absJacobian (m : ℕ) (side : Bool)
    {z : Parameter W.S} (hz : z ∈ sectorNeighborhood W.S W.base W.ε W.ε)
    {p : PolarPoint} (hp : p ∈ Ioo (W.C.left m) (W.C.right m) ×ˢ (univ : Set ℝ)) :
    |planeJacobian (n04bActualNegativeChart W.hT W.hS W.through03 W.field
        (liftSectorParameter W.S W.C z) m side) p| =
      |planeJacobian (n04bActualNegativeChart W.hT W.hS W.through03 W.field
        (liftSectorParameter W.S W.C z) m (!side)) p| *
        Real.sqrt
          ((n04bActualNegativeChart W.hT W.hS W.through03 W.field
            (liftSectorParameter W.S W.C z) m (!side) p).1 /
          (n04bActualNegativeChart W.hT W.hS W.through03 W.field
            (liftSectorParameter W.S W.C z) m side p).1) := by
  have hw := liftSectorParameter_mem_stateNeighborhood (C := W.C) hz le_rfl
  have hs := W.through03.1.1.2.2.1.liftSectorParameter_sector z
  have hg (b : Bool) := (n04bActualNegativeFunctions_spec
    W.hT W.hS W.through03 W.field hw hs m b).component_chart_germ hp
  have hj (b : Bool) :
      planeJacobian (n04bActualNegativeChart W.hT W.hS W.through03 W.field
          (liftSectorParameter W.S W.C z) m b) p =
        planeJacobian (n04bRootPhysicalChart
          (n04bActualTravelChart W.S W.C W.L (liftSectorParameter W.S W.C z) m)
          (W.C.travel m) b) p := by
    unfold planeJacobian
    rw [(hg b).fderiv_eq (𝕜 := ℝ)]
  rw [hj side, hj (!side), (hg side).self_of_nhds, (hg (!side)).self_of_nhds]
  apply n04b_abs_planeJacobian_rootPhysicalChart_opposite side
  · have hSmooth := n04b_actualTravelChart_smooth W.through03 W.hS W.hT W.field hw hs m
    exact (hSmooth.contDiffAt ((isOpen_Ioo.prod isOpen_univ).mem_nhds hp)).differentiableAt
      (by simp)
  · exact ((n04b_actualTravelChart_bijOn W.through03 W.hS W.hT W.field hw hs m).mapsTo hp).1

/-- On the current target half, changing to the opposite reference half
can only decrease the needed reciprocal determinant. -/
theorem negativeChart_inverseJacobian_le_opposite (m : ℕ) (side : Bool)
    {z : Parameter W.S} (hz : z ∈ sectorNeighborhood W.S W.base W.ε W.ε)
    {p : PolarPoint} (hp : p ∈ Ioo (W.C.left m) (W.C.right m) ×ˢ (univ : Set ℝ))
    (hcut : (n04bActualNegativeChart W.hT W.hS W.through03 W.field
      (liftSectorParameter W.S W.C z) m side p).1 ≤ n04bRootCutRadius (W.C.travel m)) :
    |planeJacobian (n04bActualNegativeChart W.hT W.hS W.through03 W.field
        (liftSectorParameter W.S W.C z) m side) p|⁻¹ ≤
      |planeJacobian (n04bActualNegativeChart W.hT W.hS W.through03 W.field
        (liftSectorParameter W.S W.C z) m (!side)) p|⁻¹ := by
  have hw := liftSectorParameter_mem_stateNeighborhood (C := W.C) hz le_rfl
  have hs := W.through03.1.1.2.2.1.liftSectorParameter_sector z
  have hT := n04b_actualTravel_positive W.through03 W.hS W.hT W.field hw hs m
  have hR := n04bRootCutRadius_pos hT
  have hpositive (b : Bool) : 0 <
      (n04bActualNegativeChart W.hT W.hS W.through03 W.field
        (liftSectorParameter W.S W.C z) m b p).1 := by
    rw [((n04bActualNegativeFunctions_spec W.hT W.hS W.through03 W.field
      hw hs m b).component_chart_germ hp).self_of_nhds]
    exact W.negativeRootChart_radial_pos m b hz hp
  let x := (n04bActualNegativeChart W.hT W.hS W.through03 W.field
    (liftSectorParameter W.S W.C z) m side p).1 / n04bRootCutRadius (W.C.travel m)
  let y := (n04bActualNegativeChart W.hT W.hS W.through03 W.field
    (liftSectorParameter W.S W.C z) m (!side) p).1 / n04bRootCutRadius (W.C.travel m)
  have hx : 0 < x := div_pos (hpositive side) hR
  have hy : 0 < y := div_pos (hpositive (!side)) hR
  have hx1 : x ≤ 1 := (div_le_one hR).mpr hcut
  have hsum : x ^ (3 / 2 : ℝ) + y ^ (3 / 2 : ℝ) = 2 :=
    W.negativeChart_normalizedRoot_power_sum m side hz hp
  have hyp : (1 : ℝ) ^ (3 / 2 : ℝ) ≤ y ^ (3 / 2 : ℝ) := by
    have hxp := Real.rpow_le_one hx.le hx1 (by norm_num : (0 : ℝ) ≤ 3 / 2)
    rw [Real.one_rpow]
    linarith
  have hy1 : 1 ≤ y :=
    (Real.rpow_le_rpow_iff (by norm_num) hy.le (by norm_num)).mp hyp
  have hradial :
      (n04bActualNegativeChart W.hT W.hS W.through03 W.field
        (liftSectorParameter W.S W.C z) m side p).1 ≤
      (n04bActualNegativeChart W.hT W.hS W.through03 W.field
        (liftSectorParameter W.S W.C z) m (!side) p).1 :=
    (div_le_div_iff_of_pos_right hR).mp (hx1.trans hy1)
  have hfactor : 1 ≤ Real.sqrt
      ((n04bActualNegativeChart W.hT W.hS W.through03 W.field
        (liftSectorParameter W.S W.C z) m (!side) p).1 /
      (n04bActualNegativeChart W.hT W.hS W.through03 W.field
        (liftSectorParameter W.S W.C z) m side p).1) :=
    Real.one_le_sqrt.mpr ((one_le_div (hpositive side)).mpr hradial)
  apply inv_anti₀ (abs_pos.mpr (W.negativeChart_jacobian_ne_zero m (!side) hz hp))
  rw [W.negativeChart_opposite_absJacobian m side hz hp]
  exact le_mul_of_one_le_right (abs_nonneg _) hfactor

theorem negativeInverse_inverseJacobian_le_opposite (m : ℕ) (side : Bool)
    {z : Parameter W.S} (hz : z ∈ sectorNeighborhood W.S W.base W.ε W.ε)
    {q : PolarPoint}
    (hq : q ∈ Ioo (0 : ℝ) (n04bRootCutRadius (W.C.travel m)) ×ˢ (univ : Set ℝ)) :
    let p := n04bActualNegativeInverse W.hT W.hS W.through03 W.field
      (liftSectorParameter W.S W.C z) m side q
    |planeJacobian (n04bActualNegativeChart W.hT W.hS W.through03 W.field
        (liftSectorParameter W.S W.C z) m side) p|⁻¹ ≤
      |planeJacobian (n04bActualNegativeChart W.hT W.hS W.through03 W.field
        (liftSectorParameter W.S W.C z) m (!side)) p|⁻¹ := by
  apply W.negativeChart_inverseJacobian_le_opposite m side hz
    (W.negativeInverse_maps_component m side hz hq)
  rw [W.negativeInverse_right m side hz hq]
  exact hq.1.2.le

end N04RealizationStart

namespace N04RealizationGauge

variable (G : N04RealizationGauge)

/-- The retained half has its actual root radius, old optical endpoints,
and the actual chosen chart and inverse at every state. -/
theorem negativeInverse_actual_fields
    (η : (G.W.S.height (3 / 4 : ℝ)).Space) (z : Parameter G.W.S)
    (k m : ℕ) (side : Bool) (hi : G.e k = .inl (m, side)) :
    (G.V η).left k = 0 ∧
      (G.V η).right k = n04bRootCutRadius (G.W.C.travel m) ∧
      (G.V η).physicalLeft k =
        n04bNegativeLeft G.W.C (n04bActualReferenceCut G.W.through03) (m, side) ∧
      (G.V η).physicalRight k =
        n04bNegativeRight G.W.C (n04bActualReferenceCut G.W.through03) (m, side) ∧
      (G.V η).chart (G.lift η z) k =
        n04bActualNegativeChart G.W.hT G.W.hS G.W.through03 G.W.field
          (liftSectorParameter G.W.S G.W.C z) m side ∧
      (G.V η).inverseChart (G.lift η z) k =
        n04bActualNegativeInverse G.W.hT G.W.hS G.W.through03 G.W.field
          (liftSectorParameter G.W.S G.W.C z) m side ∧
      (G.V η).height (G.lift η z) k =
        n04bActualNegativeHeight G.W.hT G.W.hS G.W.through03 G.W.field
          (liftSectorParameter G.W.S G.W.C z) m side := by
  have hf := G.negative_fields η (liftSectorParameter G.W.S G.W.C z) k (m, side) hi
  have hk : G.X.e₀ (G.negativeIndex (m, side)) = .inl (m, side) :=
    G.X.e₀.apply_symm_apply _
  have ht := n04bTypedAtlasData_negative_fields
    (C := G.W.C) (L := G.W.L) (z := liftSectorParameter G.W.S G.W.C z) G.X.e₀
    (n04bActualNegativeChart G.W.hT G.W.hS G.W.through03 G.W.field)
    (n04bActualNegativeHeight G.W.hT G.W.hS G.W.through03 G.W.field)
    (n04bActualNegativeInverse G.W.hT G.W.hS G.W.through03 G.W.field)
    (n04bActualReferenceCut G.W.through03) (G.negativeIndex (m, side)) m side hk
  refine ⟨?_, ?_, ?_, ?_, hf.2.2.2.2.2.2.2.1.trans ht.2.2.2.1,
    hf.2.2.2.2.2.2.2.2.1.trans ht.2.2.2.2.1,
    hf.2.2.2.2.2.2.2.2.2.1.trans ht.2.2.2.2.2⟩
  · rw [hf.1]
    exact n04bTypedAtlasData_left ..
  · rw [hf.2.1]
    simp only [N04RealizationStart.A, n04bActualTypedAtlas, n04bTypedAtlasData_right, hk]
  · rw [hf.2.2.1]
    change n04bReferenceTypedLeft G.W.C (n04bActualReferenceCut G.W.through03)
      (G.X.e₀ (G.negativeIndex (m, side))) = _
    rw [hk]
    rfl
  · rw [hf.2.2.2.1]
    change n04bReferenceTypedRight G.W.C (n04bActualReferenceCut G.W.through03)
      (G.X.e₀ (G.negativeIndex (m, side))) = _
    rw [hk]
    rfl

/-- Every point of the original component belongs to a closed old half.
The cut itself is covered by the same assertion. -/
theorem negativeInverse_referenceHalf_cover
    (η : (G.W.S.height (3 / 4 : ℝ)).Space) (m : ℕ) {p : PolarPoint}
    (hp : p ∈ Ioo (G.W.C.left m) (G.W.C.right m) ×ˢ (univ : Set ℝ)) :
    ∃ side : Bool, let k := G.e.symm (.inl (m, side))
      p ∈ Icc ((G.V η).physicalLeft k) ((G.V η).physicalRight k) ×ˢ (univ : Set ℝ) := by
  have hf (side : Bool) := G.negativeInverse_actual_fields η 0
    (G.e.symm (.inl (m, side))) m side (G.e.apply_symm_apply _)
  by_cases hcut : p.1 ≤ n04bActualReferenceCut G.W.through03 m
  · refine ⟨false, ?_⟩
    dsimp only
    rw [(hf false).2.2.1, (hf false).2.2.2.1]
    exact ⟨⟨hp.1.1.le, hcut⟩, mem_univ _⟩
  · refine ⟨true, ?_⟩
    dsimp only
    rw [(hf true).2.2.1, (hf true).2.2.2.1]
    exact ⟨⟨(lt_of_not_ge hcut).le, hp.1.2.le⟩, mem_univ _⟩

theorem negativeInverse_pair_sample_weights (γ P : ℝ) (hP : 0 ≤ P) :
    ∃ B A : ℝ, 0 < B ∧ 0 ≤ A ∧
      ∀ (η : (G.W.S.height (3 / 4 : ℝ)).Space) k k' m side side',
        G.e k = .inl (m, side) → G.e k' = .inl (m, side') →
          G.W.U.H (G.W.U.sample ((G.V η).cell k')) ^ γ *
              G.W.U.E0 (G.W.U.sample ((G.V η).cell k')) ^ P ≤
            B * (G.W.U.H (G.W.U.sample ((G.V η).cell k)) ^ γ *
              G.W.U.E0 (G.W.U.sample ((G.V η).cell k)) ^ A) := by
  obtain ⟨B, A, hB, hA, hb⟩ := G.W.negativeInverse_pair_sample_weights G.X.e₀ γ P hP
  refine ⟨B, A, hB, hA, ?_⟩
  intro η k k' m side side' hk hk'
  have hf := G.negative_fields η (G.W.C.referenceState, 0) k (m, side) hk
  have hf' := G.negative_fields η (G.W.C.referenceState, 0) k' (m, side') hk'
  rw [hf.2.2.2.2.2.1, hf'.2.2.2.2.2.1]
  exact hb (G.negativeIndex (m, side)) (G.negativeIndex (m, side')) m side side'
    (G.X.e₀.apply_symm_apply _) (G.X.e₀.apply_symm_apply _)

/-- The actual reciprocal determinant bound on an open old half extends
to its closed half at all points that remain in the original component. -/
theorem negativeInverse_inverseJacobian_closedHalf
    (η : (G.W.S.height (3 / 4 : ℝ)).Space)
    {z : Parameter G.W.S} (hz : z ∈ sectorNeighborhood G.W.S G.W.base G.W.ε G.W.ε)
    (k m : ℕ) (side : Bool) (hi : G.e k = .inl (m, side))
    {p : PolarPoint}
    (hp : p ∈ Ioo (G.W.C.left m) (G.W.C.right m) ×ˢ (univ : Set ℝ))
    (hhalf : p ∈ Icc ((G.V η).physicalLeft k) ((G.V η).physicalRight k) ×ˢ
      (univ : Set ℝ))
    {M : ℝ} (hvalues : ∀ q ∈ unitStrip,
      |G.atomFamily η .jacobianInverse z k q| ≤ M) :
    |planeJacobian (n04bActualNegativeChart G.W.hT G.W.hS G.W.through03 G.W.field
      (liftSectorParameter G.W.S G.W.C z) m side) p|⁻¹ ≤ M := by
  have hf := G.negativeInverse_actual_fields η z k m side hi
  have lengths := G.negativeInverse_length_values
  have hlength := lengths.choose_spec.2
  have hlen : (G.V η).physicalLeft k < (G.V η).physicalRight k :=
    sub_pos.mp (hlength η k).1
  apply n04NegativeInverse_le_on_closedHalf hlen hhalf
  · let J := G.W.negativeJacobianInverseJointTower m side
    have hc : ContinuousAt (fun x : Parameter G.W.S × PolarPoint =>
        |planeJacobian (n04bActualNegativeChart G.W.hT G.W.hS G.W.through03 G.W.field
          (liftSectorParameter G.W.S G.W.C x.1) m side) x.2|⁻¹) (z, p) :=
      J.continuousOn.continuousAt (J.open_domain.mem_nhds ⟨hz, hp⟩)
    exact hc.comp (continuousAt_const.prodMk continuousAt_id)
  · intro r hr
    let q := n07aCanonicalUnitInversePoint (n07aPhysicalIntervalData (G.V η)) k r
    have hq : q ∈ unitStrip :=
      n07aCanonicalUnitInversePoint_maps (K := n07aPhysicalIntervalData (G.V η)) hlen hr
    have hpoint : physicalUnitPoint (G.V η) k q = r :=
      n07aCanonicalUnitPoint_inverse (K := n07aPhysicalIntervalData (G.V η)) hlen r
    have hv := hvalues q hq
    change abs (|planeJacobian ((G.V η).chart (G.lift η z) k)
      (physicalUnitPoint (G.V η) k q)|⁻¹) ≤ M at hv
    have he : |planeJacobian ((G.V η).chart (G.lift η z) k)
        (physicalUnitPoint (G.V η) k q)|⁻¹ =
        |planeJacobian (n04bActualNegativeChart G.W.hT G.W.hS G.W.through03 G.W.field
          (liftSectorParameter G.W.S G.W.C z) m side) r|⁻¹ :=
      congrArg₂ (fun (F : PolarPoint → PolarPoint) (p : PolarPoint) =>
        |planeJacobian F p|⁻¹) hf.2.2.2.2.1 hpoint
    exact he.symm.trans_le ((le_abs_self _).trans hv)

/-- The determinant needed by the actual negative inverse has one
uniform coefficient envelope.  Crossing the old reference cut is
handled by the actual opposite-root determinant identity and by transfer
between the two stored material samples. -/
theorem negativeInverse_inverseJacobian_bound
    {b : ℕ} {ε : ℝ} (hadm : G.Admissible b ε)
    (h : G.Data 0 (G.Neg 0) b ε
      (G.atomFamily 0 .jacobianInverse) (G.atomRef 0 .jacobianInverse)) :
    ∃ b' : ℕ, ∃ ε' B : ℝ, b ≤ b' ∧ 0 < ε' ∧ ε' ≤ ε ∧ 0 < B ∧
      ∀ (η : (G.W.S.height (3 / 4 : ℝ)).Space),
        ∀ z ∈ sectorNeighborhood G.W.S b' ε' ε', ∀ k, G.Neg η k →
          ∀ q ∈ unitStrip,
            |planeJacobian ((G.V η).chart (G.lift η z) k)
              (G.pulledPoint η (G.lift η z) k q)|⁻¹ ≤
              B * G.W.U.E0 (G.W.U.sample ((G.V η).cell k)) ^ B := by
  have hcurrent :=
    G.negativeInverse_atom_value_bound hadm.2.1 .jacobianInverse
      (by simp [atomIsGeometry]) h
  let b' : ℕ := hcurrent.choose
  let ε' : ℝ := hcurrent.choose_spec.choose
  let C : ℝ := hcurrent.choose_spec.choose_spec.choose
  have hc := hcurrent.choose_spec.choose_spec.choose_spec
  have hb : b ≤ b' := hc.1
  have hε' : 0 < ε' := hc.2.1
  have hε'ε : ε' ≤ ε := hc.2.2.1
  have hC : 0 < C := hc.2.2.2.1
  have hvalues := hc.2.2.2.2
  have transfers := G.negativeInverse_pair_sample_weights 0 C hC.le
  let M : ℝ := transfers.choose
  let P : ℝ := transfers.choose_spec.choose
  have htransfer := transfers.choose_spec.choose_spec.2.2
  have packed := coefficientEnvelope_pack (C * M) P
  let B : ℝ := packed.choose
  have hB : 0 < B := packed.choose_spec.1
  have hpack := packed.choose_spec.2
  refine ⟨b', ε', B, hb, hε', hε'ε, hB, ?_⟩
  intro η z hz k hk q hq
  let data : ∃ j : ℕ × Bool, G.e k = .inl j := (G.neg_iff_inl η k).mp hk
  let m : ℕ := data.choose.1
  let side : Bool := data.choose.2
  have hi : G.e k = .inl (m, side) := data.choose_spec
  have hzfull : z ∈ sectorNeighborhood G.W.S G.W.base G.W.ε G.W.ε :=
    sectorNeighborhood_mono G.W.S (hadm.1.trans hb)
      (hε'ε.trans hadm.2.2.1) (hε'ε.trans hadm.2.2.1) hz
  have hf := G.negativeInverse_actual_fields η z k m side hi
  let y := canonicalUnitPoint (G.V η) k q
  have hy : y ∈ Ioo (0 : ℝ) (n04bRootCutRadius (G.W.C.travel m)) ×ˢ (univ : Set ℝ) := by
    change canonicalUnitPoint (G.V η) k q ∈ _
    rw [G.negative_canonicalUnitPoint η k (m, side) hi]
    exact G.W.negativeCanonicalUnit_mapsTo G.X.e₀ (G.negativeIndex (m, side)) m side
      (G.X.e₀.apply_symm_apply _) hq
  let p := n04bActualNegativeInverse G.W.hT G.W.hS G.W.through03 G.W.field
    (liftSectorParameter G.W.S G.W.C z) m side y
  have hp := G.W.negativeInverse_maps_component m side hzfull hy
  have covered := G.negativeInverse_referenceHalf_cover η m hp
  let source : Bool := covered.choose
  have hhalf := covered.choose_spec
  let k' := G.e.symm (.inl (m, source))
  have hi' : G.e k' = .inl (m, source) := G.e.apply_symm_apply _
  have hk' : G.Neg η k' := (G.neg_iff_inl η k').mpr ⟨(m, source), hi'⟩
  have hsource := G.negativeInverse_inverseJacobian_closedHalf η hzfull k' m source hi'
    hp hhalf (hvalues η z hz k' hk')
  have hcompare :
      |planeJacobian (n04bActualNegativeChart G.W.hT G.W.hS G.W.through03 G.W.field
        (liftSectorParameter G.W.S G.W.C z) m side) p|⁻¹ ≤
      |planeJacobian (n04bActualNegativeChart G.W.hT G.W.hS G.W.through03 G.W.field
        (liftSectorParameter G.W.S G.W.C z) m source) p|⁻¹ := by
    have hs : source = side ∨ source = !side := by cases source <;> cases side <;> simp
    let inverseJac : Bool → ℝ := fun b =>
      |planeJacobian (n04bActualNegativeChart G.W.hT G.W.hS G.W.through03 G.W.field
        (liftSectorParameter G.W.S G.W.C z) m b) p|⁻¹
    rcases hs with hsame | hopposite
    · exact (congrArg inverseJac hsame).symm.le
    · exact (G.W.negativeInverse_inverseJacobian_le_opposite m side hzfull hy).trans_eq
        (congrArg inverseJac hopposite).symm
  have ht : G.W.U.E0 (G.W.U.sample ((G.V η).cell k')) ^ C ≤
      M * G.W.U.E0 (G.W.U.sample ((G.V η).cell k)) ^ P := by
    exact n04NegativeInverse_remove_zero_height_weight (M := M)
      (a := G.W.U.E0 (G.W.U.sample ((G.V η).cell k')) ^ C)
      (b := G.W.U.E0 (G.W.U.sample ((G.V η).cell k)) ^ P)
      (htransfer η k k' m side source hi hi')
  change |planeJacobian ((G.V η).chart (G.lift η z) k)
    ((G.V η).inverseChart (G.lift η z) k y)|⁻¹ ≤ _
  have he : |planeJacobian ((G.V η).chart (G.lift η z) k)
      ((G.V η).inverseChart (G.lift η z) k y)|⁻¹ =
      |planeJacobian (n04bActualNegativeChart G.W.hT G.W.hS G.W.through03 G.W.field
        (liftSectorParameter G.W.S G.W.C z) m side) p|⁻¹ :=
    congrArg₂ (fun (F : PolarPoint → PolarPoint) (p : PolarPoint) =>
      |planeJacobian F p|⁻¹) hf.2.2.2.2.1 (congrFun hf.2.2.2.2.2.1 y)
  apply he.trans_le
  calc
    _ ≤ C * G.W.U.E0 (G.W.U.sample ((G.V η).cell k')) ^ C :=
      hcompare.trans hsource
    _ ≤ C * (M * G.W.U.E0 (G.W.U.sample ((G.V η).cell k)) ^ P) :=
      mul_le_mul_of_nonneg_left ht hC.le
    _ = (C * M) * G.W.U.E0 (G.W.U.sample ((G.V η).cell k)) ^ P :=
      (mul_assoc C M _).symm
    _ ≤ B * G.W.U.E0 (G.W.U.sample ((G.V η).cell k)) ^ B :=
      hpack _ ((G.cost_nonneg η).2.2 k)

/-- Genuine joint towers of one of the actual physical atoms restrict
to every admissible parameter neighborhood without changing their jets. -/
def negativeInverse_physicalAtomJointTower
    {b : ℕ} {ε : ℝ} (hadm : G.Admissible b ε)
    (m : ℕ) (hm : G.Neg 0 m) (a : Atom) (ha : negativePhysicalGeometryAtom a) :
    SmoothDirections (sectorNeighborhood G.W.S b ε ε ×ˢ unitStrip)
      (fun x : Parameter G.W.S × PolarPoint => G.atomFamily 0 a x.1 m x.2) :=
  (G.negativePhysicalAtomJointTower 0 m hm a ha).restrict
    ((sectorNeighborhood_isOpen G.W.S b ε ε).prod (isOpen_Ioo.prod isOpen_univ))
    (fun x hx => ⟨sectorNeighborhood_mono G.W.S hadm.1 hadm.2.2.1 hadm.2.2.1 hx.1, hx.2⟩)

/-- On each actual reference unit half, mixed current estimates give
pure joint estimates with exactly the same parameter arity and height
gain.  The spatial factor is packaged into the coefficient envelope. -/
theorem negativeInverse_atom_purePrefix
    {b : ℕ} {ε : ℝ} (a : Atom) (ha : atomIsGeometry a)
    (h : G.Data 0 (G.Neg 0) b ε (G.atomFamily 0 a) (G.atomRef 0 a)) :
    ∃ low : ℕ, b ≤ low ∧ ∀ K : ℕ, ∃ shift : ℕ, 1 ≤ shift ∧ ∀ s : ℕ,
      ∃ B : ℝ, 0 < B ∧ ∀ m (hm : G.Neg 0 m),
        ∀ J : SmoothDirections (sectorNeighborhood G.W.S b ε ε ×ˢ unitStrip)
          (fun x : Parameter G.W.S × PolarPoint => G.atomFamily 0 a x.1 m x.2),
        ∀ z ∈ sectorNeighborhood G.W.S b ε ε, parameterGrading G.W.S low z ≤ 1 →
        ∀ q ∈ unitStrip, ∀ n : ℕ, ∀ w : StateAngleWord n,
          w.stateArity ≤ K → w.angleArity ≤ s →
        ∀ v : Fin n → Parameter G.W.S × PolarPoint,
          (∀ i, parameterGrading G.W.S low (v i).1 ≤ 1) →
        ∀ R : ℝ, 1 ≤ R → parameterGrading G.W.S (low + s + shift * K + 1) z ≤ R →
          (∀ i, parameterGrading G.W.S (low + s + shift * K + 1) (v i).1 ≤ R) →
          (∀ i, ‖(v i).2‖ ≤ 1) →
          (∀ i, w.isState i = false → (v i).1 = 0) →
          (∀ i, w.isState i = true → (v i).2 = 0) →
        |J.D n (z, q) v| ≤
          B * G.W.U.E0 (G.W.U.sample ((G.V 0).cell m)) ^ B *
            parameterHeightWeight
              (G.W.U.H (G.W.U.sample ((G.V 0).cell m)) ^ (3 / 4 : ℝ)) w.stateArity *
            R ^ (((w.angleArity + shift * w.stateArity - 1 : ℕ) : ℝ) /
              (((s + shift * K : ℕ) : ℝ) + 1)) := by
  have hU := isMaterialData_enlargedMaterialData G.W.radial.1 G.W.hT
  have href : ∀ s : ℕ, ∃ B : ℝ, 0 < B ∧ ∀ m, G.Neg 0 m →
      ∀ q ∈ unitStrip, ∀ i j : ℕ, i + j ≤ s →
        |mixedDerivative i j (G.atomRef 0 a m) q| ≤
          B * G.W.U.E0 (G.W.U.sample ((G.V 0).cell m)) ^ B := by
    intro s
    have reference := G.negativeInverse_reference_geometry_bounds s
    let B : ℝ := reference.choose
    have hB : 0 < B := reference.choose_spec.1
    have hb := reference.choose_spec.2
    exact ⟨B, hB, fun m hm q hq i j hij => hb 0 m hm a ha q hq i j hij⟩
  have hfamily := CurrentJetDataOn.negativeInverse_sharpPrefix_power
    (D := G.W.D) (S := G.S 0) (T := G.W.U) (cell := (G.V 0).cell)
    (P := G.Neg 0) (base := b) (ε := ε)
    (f := G.atomFamily 0 a) (f₀ := G.atomRef 0 a)
    G.W.radial.1 hU G.W.negativeInverse_parameterInterpolation h
    (fun m hm => (G.negativeInverse_reference_geometry_regular 0 m hm a ha).1)
    href (G.cost_nonneg 0).2.2 (G.cost_nonneg 0).2.1
  let low : ℕ := hfamily.choose
  have hlow : b ≤ low := hfamily.choose_spec.1
  have hprefix := hfamily.choose_spec.2
  refine ⟨low, hlow, fun K => ?_⟩
  let shift : ℕ := (hprefix K).choose
  have hshift : 1 ≤ shift := (hprefix K).choose_spec.1
  have hp := (hprefix K).choose_spec.2
  refine ⟨shift, hshift, fun s => ?_⟩
  let C : ℝ := (hp s).choose
  have hC : 0 < C := (hp s).choose_spec.1
  have hb := (hp s).choose_spec.2
  have packed := coefficientEnvelope_pack ((2 : ℝ) ^ s * C) C
  let B : ℝ := packed.choose
  have hB : 0 < B := packed.choose_spec.1
  have hpack := packed.choose_spec.2
  refine ⟨B, hB, ?_⟩
  intro m hm J z hz hzlow q hq n w hwK hws v hvlow R hR hzR hvR hvphys hvstate hvspatial
  let E := G.W.U.E0 (G.W.U.sample ((G.V 0).cell m))
  let H := G.W.U.H (G.W.U.sample ((G.V 0).cell m)) ^ (3 / 4 : ℝ)
  let major : ℕ → ℕ → ℝ := fun k t =>
    C * E ^ C * parameterHeightWeight H k *
      R ^ (((t + shift * k - 1 : ℕ) : ℝ) / (((s + shift * K : ℕ) : ℝ) + 1))
  have hE : 1 ≤ E := (G.cost_nonneg 0).2.2 m
  have hH : 0 ≤ H := Real.rpow_nonneg ((G.cost_nonneg 0).2.1 m) _
  have hmajor (k t : ℕ) : 0 ≤ major k t :=
    mul_nonneg (mul_nonneg (mul_nonneg hC.le
      (Real.rpow_nonneg (zero_le_one.trans hE) _))
      (parameterHeightWeight_nonneg hH k))
      (Real.rpow_nonneg (zero_le_one.trans hR) _)
  have hraw := n04NegativeInverse_pureJoint_of_parameterTowers
    (E := Parameter G.W.S) (U := sectorNeighborhood G.W.S b ε ε) (V := unitStrip)
    (f := fun x : Parameter G.W.S × PolarPoint => G.atomFamily 0 a x.1 m x.2)
    (sectorNeighborhood_isOpen G.W.S b ε ε) (isOpen_Ioo.prod isOpen_univ)
    ((sectorNeighborhood_convex G.W.S b ε ε).prod
      ((convex_Ioo (0 : ℝ) 1).prod convex_univ))
    (parameterGrading G.W.S low)
    (parameterGrading G.W.S (low + s + shift * K + 1)) R z hz q hq w J major hmajor
    (fun k i j hk hij Q u hu huR =>
      hb k (hk.trans hwK) m hm q hq i j (hij.trans hws) Q z hz hzlow u hu R hR hzR huR)
    v hvlow hvR hvphys hvstate hvspatial
  have htwo : (2 : ℝ) ^ w.angleArity ≤ (2 : ℝ) ^ s :=
    pow_le_pow_right₀ (by norm_num) hws
  have hcost : (2 : ℝ) ^ w.angleArity * (C * E ^ C) ≤ B * E ^ B := by
    calc
      _ ≤ (2 : ℝ) ^ s * (C * E ^ C) :=
        mul_le_mul_of_nonneg_right htwo
          (mul_nonneg hC.le (Real.rpow_nonneg (zero_le_one.trans hE) _))
      _ = ((2 : ℝ) ^ s * C) * E ^ C := (mul_assoc _ _ _).symm
      _ ≤ B * E ^ B := hpack E hE
  have htail : 0 ≤ parameterHeightWeight H w.stateArity *
      R ^ (((w.angleArity + shift * w.stateArity - 1 : ℕ) : ℝ) /
        (((s + shift * K : ℕ) : ℝ) + 1)) :=
    mul_nonneg (parameterHeightWeight_nonneg hH _)
      (Real.rpow_nonneg (zero_le_one.trans hR) _)
  calc
    |J.D n (z, q) v| ≤ (2 : ℝ) ^ w.angleArity * major w.stateArity w.angleArity := hraw
    _ = ((2 : ℝ) ^ w.angleArity * (C * E ^ C)) *
        (parameterHeightWeight H w.stateArity *
          R ^ (((w.angleArity + shift * w.stateArity - 1 : ℕ) : ℝ) /
            (((s + shift * K : ℕ) : ℝ) + 1))) := by simp only [major, mul_assoc]
    _ ≤ (B * E ^ B) * (parameterHeightWeight H w.stateArity *
        R ^ (((w.angleArity + shift * w.stateArity - 1 : ℕ) : ℝ) /
          (((s + shift * K : ℕ) : ℝ) + 1))) := mul_le_mul_of_nonneg_right hcost htail
    _ = _ := (mul_assoc _ _ _).symm

end N04RealizationGauge
end ContinuousFlexibility.Analysis
