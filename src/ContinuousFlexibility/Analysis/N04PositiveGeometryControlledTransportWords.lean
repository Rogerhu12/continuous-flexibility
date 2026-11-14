module

public import ContinuousFlexibility.Analysis.N04PositiveGeometryControlledFactorWords
public import ContinuousFlexibility.Analysis.N04PositiveGeometryPlaneSavedTransportComposition

/-!
# Saved words of the two displayed whole-component transports

The forward transport composes the radial factor with the angular
graph. The inverse composes the inverse angle with the inverse radial
graph. Their actual geometry keeps every moving radius on the same
closed physical slab.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Function ContinuousFlexibility.Statements

theorem n04PositiveGeometry_controlledTransports_saved_prefix
    {W : N04RealizationStart} {X : N04RealizationChoice W} {order : ℕ}
    (G : N04PositiveGeometryControlledFamily W X order) (N : ℕ) (A RH : ℝ) (hA : 1 ≤ A) :
    ∃ B : ℝ, 1 ≤ B ∧ ∀ (base : ℕ) (ε : ℝ), G.base ≤ base → ε ≤ G.ε →
      ∀ i : N04PositiveComponent W.D.a W.D.b (deriv W.D.w),
      ∀ F : N04PositiveGeometryFactorData G base ε i,
      ∀ JA : SmoothDirections (sectorNeighborhood W.S base ε ε ×ˢ univ)
        (fun z : (StateDirections W.S × ℝ) × ℝ =>
          G.toN04PositiveGeometryControlData.angularCoefficients
            (liftSectorParameter W.S W.C z.1) i z.2),
      ∀ JR : SmoothDirections (sectorNeighborhood W.S base ε ε ×ˢ univ)
        (fun z : (StateDirections W.S × ℝ) × ℝ => fun side (j : Fin (order + 1)) =>
          G.toN04PositiveGeometryControlData.coefficients
            (liftSectorParameter W.S W.C z.1) i side (j + 1) z.2),
      ∀ (p q : Seminorm ℝ (StateDirections W.S × ℝ)) (R H t : ℝ),
        0 ≤ R → 0 ≤ H → H ≤ RH → 1 ≤ t →
      ∀ K s shift : ℕ, N ≤ K + s + 1 →
      ∀ x ∈ sectorNeighborhood W.S base ε ε,
      (∀ θ, N04BoundaryWordBounds JA K (s + K) 1 x θ
        (fun a => p a ≤ 1 ∧ q a ≤ R) (A * W.U.E0 (W.U.sample (X.cell i)) ^ A) H t shift) →
      (∀ θ, N04BoundaryWordBounds JR K (s + K) 1 x θ
        (fun a => p a ≤ 1 ∧ q a ≤ R) (A * W.U.E0 (W.U.sample (X.cell i)) ^ A) H t shift) →
      let Ω : Set PolarPoint := Icc (n04PositiveLeft i) (n04PositiveRight i) ×ˢ univ
      let M : ℝ := B * W.U.E0 (W.U.sample (X.cell i)) ^ B
      N04PlaneSavedWordBounds F.transport N K (shift + 1) x Ω p q R M H t ∧
      N04PlaneSavedWordBounds F.inverseTransport N K (shift + 1) x Ω p q R M H t := by
  let V := StateDirections W.S × ℝ
  haveI : IsTopologicalAddGroup V := inferInstance
  haveI : ContinuousSMul ℝ V := inferInstance
  let E := fun i => W.U.E0 (W.U.sample (X.cell i))
  have hE (i) : 1 ≤ E i := (W.floor _).trans (le_enlargedMaterialData_E0 W.T _)
  let factorData := n04PositiveGeometry_controlledFactors_saved_prefix G N A RH hA
  let B₀ : ℝ := factorData.choose
  let hfactor := factorData.choose_spec.2
  let D : ℝ := max B₀ (max 1 RH)
  have hD : 1 ≤ D := (le_max_left _ _).trans (le_max_right _ _)
  have hB₀D : B₀ ≤ D := le_max_left _ _
  have hRHD : RH ≤ D := (le_max_right _ _).trans (le_max_right _ _)
  let compositionData := n04PositiveGeometry_scalarFactors_transport_saved_prefix (E := V) N
  let Ac : ℝ := compositionData.choose
  let dc : ℕ := compositionData.choose_spec.2.choose
  let hcomp := compositionData.choose_spec.2.choose_spec
  let packData := n04PositiveGeometry_polynomial_sample_pack Ac D dc
  let B₁ : ℝ := packData.choose
  let hpack := packData.choose_spec.2
  let B : ℝ := max D B₁
  have hDB : D ≤ B := le_max_left _ _
  have hB : 1 ≤ B := hD.trans hDB
  refine ⟨B, hB, ?_⟩
  intro base ε hGb hGε i F JA JR p q R H t hR hH hHR ht K s shift hN x hx hJA hJR
  let U := sectorNeighborhood W.S base ε ε
  let state := liftSectorParameter W.S W.C
  let Ω : Set PolarPoint := Icc (n04PositiveLeft i) (n04PositiveRight i) ×ˢ univ
  let M : ℝ := D * E i ^ D
  let Mout : ℝ := B * E i ^ B
  have hU : IsOpen U := sectorNeighborhood_isOpen W.S base ε ε
  have hM : 1 ≤ M := one_le_mul_of_one_le_of_one_le hD
    (Real.one_le_rpow (hE i) (zero_le_one.trans hD))
  have hDM : D ≤ M := by
    simpa only [mul_one] using mul_le_mul_of_nonneg_left
      (Real.one_le_rpow (hE i) (zero_le_one.trans hD)) (zero_le_one.trans hD)
  have hraise {a b : ℝ} (hab : a ≤ b) (hb : 0 ≤ b) :
      a * E i ^ a ≤ b * E i ^ b :=
    mul_le_mul hab (Real.rpow_le_rpow_of_exponent_le (hE i) hab)
      (Real.rpow_nonneg (zero_le_one.trans (hE i)) _) hb
  have hM₀M : B₀ * E i ^ B₀ ≤ M := hraise hB₀D (zero_le_one.trans hD)
  have hMM : M ≤ Mout := hraise hDB (zero_le_one.trans hB)
  have hfactor' := hfactor base ε hGb hGε i F JA JR p q R H t hR hH hHR ht
    K s shift hN x hx hJA hJR
  have hφ := hfactor'.1.enlarge hH ht hM₀M
  have hα := hfactor'.2.1.enlarge hH ht hM₀M
  have hY := hfactor'.2.2.1.enlarge hH ht hM₀M
  have hρ := hfactor'.2.2.2.enlarge hH ht hM₀M
  have hσmap : MapsTo (fun y : PolarPoint =>
      (G.toN04PositiveGeometryControlData.radialInverse (state x) i y, y.2)) Ω Ω := by
    intro y hy
    have hz : state x ∈ stateNeighborhood W.S W.C G.base G.ε :=
      stateNeighborhood_mono W.S W.C hGb hGε
        (liftSectorParameter_mem_stateNeighborhood (C := W.C) hx le_rfl)
    have hs := W.through03.1.1.2.2.1.liftSectorParameter_sector x
    have hm := (G.matching (state x) hz hs i).geometry.inverse_maps_closed hy
    have he := congrArg Prod.fst
      (G.toN04PositiveGeometryControlData.inverseTransport_eq_radial_angle (state x) i y)
    exact ⟨he ▸ hm.1, mem_univ _⟩
  have hcost : Ac * M ^ dc ≤ Mout := (hpack (E i) (hE i)).trans
    (hraise (le_max_right D B₁) (zero_le_one.trans hB))
  have hout := hcomp U hU _ _ _ _
    F.angle F.angleInverse F.radial F.radialInverse _ _ F.transport F.inverseTransport
    (fun z _ => G.toN04PositiveGeometryControlData.transport_eq_radial_angle (state z.1) i z.2)
    (fun z _ => G.toN04PositiveGeometryControlData.inverseTransport_eq_radial_angle (state z.1) i z.2)
    x hx Ω (fun y hy => ⟨hy.1, mem_univ _⟩) hσmap p q R M H t
    hR hM hH (hHR.trans (hRHD.trans hDM)) ht K (shift + 1) (Nat.succ_pos shift)
    hφ hα hY hρ
  exact ⟨hout.1.enlarge hH ht (max_le hMM hcost),
    hout.2.enlarge hH ht (max_le hMM hcost)⟩

end ContinuousFlexibility.Analysis
