import ContinuousFlexibility.Analysis.N01FlowConstantDirections
import ContinuousFlexibility.Analysis.N01EndpointParameterTower
import ContinuousFlexibility.Analysis.SmoothDirectionsEuler
import ContinuousFlexibility.Analysis.HeightScalarVariationWeights

/-!
# Every pure scalar flow jet has a local physical height factor

The true scaling identity supplies the Euler relation throughout the
scalar segment. A mixed N01 jet and the scalar mean value theorem then
bound every positive pure scalar order, including at scalar parameter
zero. The precise one-high-factor height expression is retained.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

local instance n01FlowScalarHeightBoundsStateSMul (S : PhysicalSpacesData) : SMul ℝ (AnnularState S) := Prod.instSMul

open Set Filter ContinuousFlexibility.Analysis
open scoped Topology ContDiff BigOperators

private theorem scalar_segment_mul_mem {t q : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    t * q ∈ uIcc (0 : ℝ) q := by
  rcases le_total (0 : ℝ) q with hq | hq
  · rw [uIcc_of_le hq]
    exact ⟨mul_nonneg ht.1 hq,
      (mul_le_mul_of_nonneg_right ht.2 hq).trans_eq (one_mul q)⟩
  · rw [uIcc_of_ge hq]
    refine ⟨?_, mul_nonpos_of_nonneg_of_nonpos ht.1 hq⟩
    simpa only [one_mul] using mul_le_mul_of_nonpos_right ht.2 hq

private theorem scalar_height_bound_of_tower
    {S : PhysicalSpacesData} {base : ℕ} {ε : ℝ}
    {f : StateDirections S × ℝ → ℝ}
    (J : SmoothDirections (sectorNeighborhood S base ε ε) f)
    (high n : ℕ) (z : StateDirections S × ℝ)
    (hz : z ∈ sectorNeighborhood S base ε ε) (η : HeightPair S)
    {P : ℝ} (hP : 0 ≤ P)
    (hJ : ∀ y ∈ sectorNeighborhood S base ε ε,
      ∀ v : Fin (n + 2) → StateDirections S × ℝ,
      |J.D (n + 2) y v| ≤ P *
        oneHighVariationWeight (pairGrading (sectorGrading S) realGrading) base high y v)
    (heuler : ∀ q : ℝ, (z.1, q) ∈ sectorNeighborhood S base ε ε →
      J.D 1 (z.1, q) (fun _ => heightParameterDirection S η) =
        q * J.D 1 (z.1, q) (fun _ => scalarParameterDirection S)) :
    |J.D (n + 1) z (fun _ => scalarParameterDirection S)| ≤
      P * (((n : ℝ) + 2 + pairGrading (sectorGrading S) realGrading high z) *
        heightPairGrading S base η + heightPairGrading S high η) := by
  let x₀ : StateDirections S × ℝ := (z.1, 0)
  have hpoint (q : ℝ) : x₀ + q • scalarParameterDirection S = (z.1, q) :=
    scalarParameter_zero_line S z.1 q
  have hEuler (q : ℝ) (hq : x₀ + q • scalarParameterDirection S ∈
      sectorNeighborhood S base ε ε) :
      J.D 1 (x₀ + q • scalarParameterDirection S) (fun _ => heightParameterDirection S η) =
        q * J.D 1 (x₀ + q • scalarParameterDirection S) (fun _ => scalarParameterDirection S) := by
    have hq' : (z.1, q) ∈ sectorNeighborhood S base ε ε := (hpoint q) ▸ hq
    exact (congrArg (fun y => J.D 1 y (fun _ => heightParameterDirection S η)) (hpoint q)).trans
      ((heuler q hq').trans (congrArg (fun y =>
        q * J.D 1 y (fun _ => scalarParameterDirection S)) (hpoint q)).symm)
  have hline (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
      x₀ + (t * z.2) • scalarParameterDirection S ∈ sectorNeighborhood S base ε ε :=
    (hpoint (t * z.2)).symm ▸ sectorParameter_scalar_segment_mem hz (scalar_segment_mul_mem ht)
  have hbound (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
      |J.D (n + 2) (x₀ + (t * z.2) • scalarParameterDirection S)
        (Fin.snoc (fun _ : Fin (n + 1) => scalarParameterDirection S)
          (heightParameterDirection S η))| ≤
        P * (((n : ℝ) + 2 + pairGrading (sectorGrading S) realGrading high z) *
          heightPairGrading S base η + heightPairGrading S high η) := by
    have h := hJ _ (hline t ht)
      (Fin.snoc (fun _ : Fin (n + 1) => scalarParameterDirection S)
        (heightParameterDirection S η))
    have hw := congrArg (fun a : ℝ => P * a)
      (oneHighVariationWeight_scalar_height S base high (n + 1)
        (x₀ + (t * z.2) • scalarParameterDirection S) η)
    have hgrade := (congrArg (pairGrading (sectorGrading S) realGrading high)
      (hpoint (t * z.2))).trans_le
        (sectorPairGrading_scalar_segment_le S high z.1 (scalar_segment_mul_mem ht))
    have hadd : ((n + 1 : ℕ) : ℝ) + 1 +
        pairGrading (sectorGrading S) realGrading high
          (x₀ + (t * z.2) • scalarParameterDirection S) ≤
        (n : ℝ) + 2 + pairGrading (sectorGrading S) realGrading high z := by
      simp only [Nat.cast_add, Nat.cast_one]
      linarith only [hgrade]
    exact (h.trans_eq hw).trans (mul_le_mul_of_nonneg_left
      (add_le_add_right (mul_le_mul_of_nonneg_right hadd (apply_nonneg _ _)) _) hP)
  have h := J.abs_pure_scalar_jet_le_of_mixed_euler_bound x₀
    (scalarParameterDirection S) (heightParameterDirection S η) hEuler n z.2 _ hline hbound
  have heq : |J.D (n + 1) (x₀ + z.2 • scalarParameterDirection S)
      (fun _ => scalarParameterDirection S)| =
      |J.D (n + 1) z (fun _ => scalarParameterDirection S)| :=
    congrArg (fun y => |J.D (n + 1) y (fun _ => scalarParameterDirection S)|) (hpoint z.2)
  exact heq.symm.trans_le h

theorem N01Properties.sectorFlow_pure_scalar_height_bound_mod_constant
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {base loss : ℕ} {ε : ℝ}
    (hN : N01Properties D T S C base loss ε)
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T) (n s : ℕ) :
    ∃ B : ℝ, 0 < B ∧ ∀ m b θ r, b ≤ s → r ∈ Icc (C.left m) (C.right m) →
      ∃ J : SmoothDirections (sectorNeighborhood S base ε ε)
        (fun y => ordinaryFlowFamily S C m 0 b (r, θ) (liftSectorParameter S C y)),
      ∀ z ∈ sectorNeighborhood S base ε ε, ∀ η : HeightPair S,
        (∃ c : ℝ, ∀ t ∈ Ioo (C.left m) (C.right m), ∀ ψ,
          heightPairField S η (t, ψ) = stateU S (liftSectorParameter S C z).1 (t, ψ) + c) →
        |J.D (n + 1) z (fun _ => scalarParameterDirection S)| ≤
          B * T.H (T.sample (C.cell m)) ^ (3 / 4 : ℝ) *
            T.E0 (T.sample (C.cell m)) ^ B *
            (((n : ℝ) + 2 + pairGrading (sectorGrading S) realGrading (s + loss) z) *
              heightPairGrading S base η + heightPairGrading S (s + loss) η) := by
  let hdata := hN.sectorFlow_closed_tower hS hT (n + 2) s
  let B : ℝ := hdata.choose
  have hB : 0 < B := hdata.choose_spec.1
  refine ⟨B, hB, fun m b θ r hb hr => ?_⟩
  let htower := hdata.choose_spec.2 m b θ r hb hr
  let J := htower.choose
  have hJ := htower.choose_spec
  refine ⟨J, fun z hz η hη => ?_⟩
  obtain ⟨c, hη⟩ := hη
  let P : ℝ := B * T.H (T.sample (C.cell m)) ^ (3 / 4 : ℝ) *
    T.E0 (T.sample (C.cell m)) ^ B
  have hsample := materialSample_mem_radialCore hT hN.1.1.choose_spec.2.1 (C.cell m)
  have hH : 0 < T.H (T.sample (C.cell m)) := (hT.2.1 _ hsample).2.1
  have hE : 0 < T.E0 (T.sample (C.cell m)) := (hT.2.1 _ hsample).2.2.1
  have hP : 0 ≤ P := mul_nonneg
    (mul_nonneg hB.le (Real.rpow_nonneg hH.le _)) (Real.rpow_nonneg hE.le _)
  have hEuler (q : ℝ) (hq : (z.1, q) ∈ sectorNeighborhood S base ε ε) :
      J.D 1 (z.1, q) (fun _ => heightParameterDirection S η) =
        q * J.D 1 (z.1, q) (fun _ => scalarParameterDirection S) := by
    have hηq : ∀ t ∈ Ioo (C.left m) (C.right m), ∀ ψ,
        heightPairField S η (t, ψ) =
          heightPairField S (liftSectorParameter S C (z.1, q)).1.1 (t, ψ) + c := by
      intro t ht ψ
      exact hη t ht ψ
    exact (hN.ordinaryFlowFamily_first_height_jet_constant_locality hS hT hq η
      (liftSectorParameter S C (z.1, q)).1.1 m b θ hr c hηq J).trans
        (hN.ordinaryFlowFamily_height_scalar_jet hS hT hq m b θ hr J)
  exact scalar_height_bound_of_tower J (s + loss) n z hz η hP hJ hEuler


theorem N01Properties.sectorFlow_pure_scalar_height_bound
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {base loss : ℕ} {ε : ℝ}
    (hN : N01Properties D T S C base loss ε)
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T) (n s : ℕ) :
    ∃ B : ℝ, 0 < B ∧ ∀ m b θ r, b ≤ s → r ∈ Icc (C.left m) (C.right m) →
      ∃ J : SmoothDirections (sectorNeighborhood S base ε ε)
        (fun y => ordinaryFlowFamily S C m 0 b (r, θ) (liftSectorParameter S C y)),
      ∀ z ∈ sectorNeighborhood S base ε ε, ∀ η : HeightPair S,
        (∀ t ∈ Ioo (C.left m) (C.right m), ∀ ψ,
          heightPairField S η (t, ψ) = stateU S (liftSectorParameter S C z).1 (t, ψ)) →
        |J.D (n + 1) z (fun _ => scalarParameterDirection S)| ≤
          B * T.H (T.sample (C.cell m)) ^ (3 / 4 : ℝ) *
            T.E0 (T.sample (C.cell m)) ^ B *
            (((n : ℝ) + 2 + pairGrading (sectorGrading S) realGrading (s + loss) z) *
              heightPairGrading S base η + heightPairGrading S (s + loss) η) := by
  let hdata := hN.sectorFlow_pure_scalar_height_bound_mod_constant hS hT n s
  let B : ℝ := hdata.choose
  have hB : 0 < B := hdata.choose_spec.1
  refine ⟨B, hB, fun m b θ r hb hr => ?_⟩
  let htower := hdata.choose_spec.2 m b θ r hb hr
  refine ⟨htower.choose, fun z hz η hη => htower.choose_spec z hz η ⟨0, ?_⟩⟩
  intro t ht ψ
  simpa only [add_zero] using hη t ht ψ

end ContinuousFlexibility.Statements
