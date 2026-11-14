module

public import ContinuousFlexibility.Analysis.N01HeightWeightConstraint
public import ContinuousFlexibility.Analysis.N01ReverseMaterialOrderActualCell

/-!
# From actual radial height tests to one fixed material-order loss

The hypothesis is a concrete height-model direction agreeing with a
radial primitive on the component, together with its actual grading
bound. The N01 mixed flow response supplies the balanced constraint.
The two auxiliary fixed losses cost two material orders; the previously
proved balanced-height argument then gives the fixed output loss one.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Statements

local instance n01HeightTestWeightBridgeStateSMul (S : PhysicalSpacesData) : SMul ℝ (AnnularState S) := Prod.instSMul
local instance n01HeightTestWeightBridgeRealNormedSpace : NormedSpace ℝ ℝ := NormedField.toNormedSpace

open Set Filter
open ContinuousFlexibility.Analysis
open scoped Topology

theorem heightPairGrading_monotone (S : PhysicalSpacesData) : Monotone (heightPairGrading S) :=
  tamePairGrading_monotone (gradedSeminorm_monotone _ _) (fun _ _ _ _ => le_rfl)

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {base loss : ℕ} {ε : ℝ}

theorem N01Properties.balanced_constraint_of_radialHeightTests
    (hN : N01Properties D T S C base loss ε)
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    (h : ℝ → ℝ) (hh : ∀ r, HasDerivAt h (D.w r) r) :
    ∃ d₂ : ℕ, ∀ {n : ℕ}, base ≤ n → loss + d₂ ≤ n →
    ∀ {K A R : ℝ}, 0 < K → 0 ≤ R →
    (∀ m j : ℕ, Ioo (C.left m) (C.right m) ⊆ D.cells j →
      ∃ η : HeightPair S,
        (∀ r ∈ Ioo (C.left m) (C.right m), ∀ θ : ℝ,
          heightPairField S η =ᶠ[𝓝 (r, θ)] Radial.radialHeightField h) ∧
        heightPairGrading S n η ≤ K * T.H (T.sample j) ^ (-(3 / 4 : ℝ)) *
          T.E0 (T.sample j) ^ A * T.M (T.sample j) ^ (n + 1) *
            radialE (D.cellIndex j) ^ R) →
    ∃ K1 A1 N1 : ℝ, 0 < K1 ∧ ∀ m, ∃ j : ℕ,
      Ioo (C.left m) (C.right m) ⊆ D.cells j ∧
      1 ≤ K1 * T.H (T.sample (C.cell m)) ^ (3 / 4 : ℝ) *
        T.E0 (T.sample (C.cell m)) ^ A1 *
        T.H (T.sample j) ^ (-(3 / 4 : ℝ)) * T.M (T.sample j) ^ N1 := by
  obtain ⟨d₂, B0, R0, hB0, hR0, hraw⟩ := hN.radialHeightDirection_weight_constraint hS hT
  refine ⟨d₂, ?_⟩
  intro n hbase hloss K A R hK hR htest
  let N : ℝ := (n + 1 : ℕ)
  obtain ⟨KA, hKA, habsorb⟩ := materialSample_radialE_E0_M_rpow_absorb
    hT hN.1.1 (add_nonneg hR0.le hR) A N
  obtain ⟨_, hgeom⟩ := hN.1.1
  have hpos (j : ℕ) := hT.2.1 _ (materialSample_mem_radialCore hT hgeom.2.1 j)
  refine ⟨3 * B0 * K * KA, B0, N + 2,
    mul_pos (mul_pos (mul_pos (by norm_num) hB0) hK) hKA, fun m => ?_⟩
  obtain ⟨j, hj, hdetector⟩ := hraw m
  obtain ⟨η, hgerm, hnorm⟩ := htest m j hj
  refine ⟨j, hj, ?_⟩
  have hbase' := heightPairGrading_monotone S hbase η
  have hloss' := heightPairGrading_monotone S hloss η
  have hnorm' : heightPairGrading S n η ≤
      K * T.H (T.sample j) ^ (-(3 / 4 : ℝ)) * T.E0 (T.sample j) ^ A *
        T.M (T.sample j) ^ N * radialE (D.cellIndex j) ^ R := by
    simpa only [N, Real.rpow_natCast] using hnorm
  have hgrade : 2 * heightPairGrading S base η + heightPairGrading S (loss + d₂) η ≤
      3 * (K * T.H (T.sample j) ^ (-(3 / 4 : ℝ)) * T.E0 (T.sample j) ^ A *
        T.M (T.sample j) ^ N * radialE (D.cellIndex j) ^ R) := by
    have hle : 2 * heightPairGrading S base η + heightPairGrading S (loss + d₂) η ≤
        3 * heightPairGrading S n η := by linarith only [hbase', hloss']
    exact hle.trans (mul_le_mul_of_nonneg_left hnorm' (by norm_num))
  have hE : 0 < radialE (D.cellIndex j) := Real.exp_pos _
  have hfactor : 0 ≤ radialE (D.cellIndex j) ^ R0 *
      (B0 * T.H (T.sample (C.cell m)) ^ (3 / 4 : ℝ) * T.E0 (T.sample (C.cell m)) ^ B0) :=
    mul_nonneg (Real.rpow_nonneg hE.le _)
      (mul_nonneg (mul_nonneg hB0.le (Real.rpow_nonneg (hpos (C.cell m)).2.1.le _))
        (Real.rpow_nonneg (hpos (C.cell m)).2.2.1.le _))
  have houter : 0 ≤ (3 * B0 * K) * T.H (T.sample (C.cell m)) ^ (3 / 4 : ℝ) *
      T.E0 (T.sample (C.cell m)) ^ B0 * T.H (T.sample j) ^ (-(3 / 4 : ℝ)) :=
    mul_nonneg
      (mul_nonneg
        (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hB0.le) hK.le)
          (Real.rpow_nonneg (hpos (C.cell m)).2.1.le _))
        (Real.rpow_nonneg (hpos (C.cell m)).2.2.1.le _))
      (Real.rpow_nonneg (hpos j).2.1.le _)
  calc
    _ ≤ radialE (D.cellIndex j) ^ R0 *
        (B0 * T.H (T.sample (C.cell m)) ^ (3 / 4 : ℝ) *
          T.E0 (T.sample (C.cell m)) ^ B0 *
          (2 * heightPairGrading S base η + heightPairGrading S (loss + d₂) η)) :=
      hdetector η h hh hgerm
    _ = (radialE (D.cellIndex j) ^ R0 *
        (B0 * T.H (T.sample (C.cell m)) ^ (3 / 4 : ℝ) * T.E0 (T.sample (C.cell m)) ^ B0)) *
          (2 * heightPairGrading S base η + heightPairGrading S (loss + d₂) η) := by ring
    _ ≤ (radialE (D.cellIndex j) ^ R0 *
        (B0 * T.H (T.sample (C.cell m)) ^ (3 / 4 : ℝ) * T.E0 (T.sample (C.cell m)) ^ B0)) *
          (3 * (K * T.H (T.sample j) ^ (-(3 / 4 : ℝ)) * T.E0 (T.sample j) ^ A *
            T.M (T.sample j) ^ N * radialE (D.cellIndex j) ^ R)) :=
      mul_le_mul_of_nonneg_left hgrade hfactor
    _ = ((3 * B0 * K) * T.H (T.sample (C.cell m)) ^ (3 / 4 : ℝ) *
        T.E0 (T.sample (C.cell m)) ^ B0 * T.H (T.sample j) ^ (-(3 / 4 : ℝ))) *
          (radialE (D.cellIndex j) ^ (R0 + R) * T.E0 (T.sample j) ^ A *
            T.M (T.sample j) ^ N) := by
      rw [Real.rpow_add hE R0 R]
      ring
    _ ≤ ((3 * B0 * K) * T.H (T.sample (C.cell m)) ^ (3 / 4 : ℝ) *
        T.E0 (T.sample (C.cell m)) ^ B0 * T.H (T.sample j) ^ (-(3 / 4 : ℝ))) *
          (KA * T.M (T.sample j) ^ (N + 2)) :=
      mul_le_mul_of_nonneg_left (habsorb j) houter
    _ = _ := by ring

theorem N01Properties.actualCell_materialOrder_from_radialHeightTests
    (hN : N01Properties D T S C base loss ε)
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    (h : ℝ → ℝ) (hh : ∀ r, HasDerivAt h (D.w r) r) :
    ∃ d₂ : ℕ, ∀ {n : ℕ}, base ≤ n → loss + d₂ ≤ n →
    ∀ {K A R : ℝ}, 0 < K → 0 ≤ R →
    (∀ m j : ℕ, Ioo (C.left m) (C.right m) ⊆ D.cells j →
      ∃ η : HeightPair S,
        (∀ r ∈ Ioo (C.left m) (C.right m), ∀ θ : ℝ,
          heightPairField S η =ᶠ[𝓝 (r, θ)] Radial.radialHeightField h) ∧
        heightPairGrading S n η ≤ K * T.H (T.sample j) ^ (-(3 / 4 : ℝ)) *
          T.E0 (T.sample j) ^ A * T.M (T.sample j) ^ (n + 1) *
            radialE (D.cellIndex j) ^ R) →
    ∃ cell : ℕ → ℕ,
      (∀ m, Ioo (C.left m) (C.right m) ⊆ D.cells (cell m)) ∧
      ∀ s : ℕ, ∃ Cs : ℝ, 0 < Cs ∧ ∀ m,
        T.M (T.sample m) ^ s ≤ Cs * T.M (T.sample (cell m)) ^ (s + 1) := by
  classical
  obtain ⟨d₂, hbridge⟩ := hN.balanced_constraint_of_radialHeightTests hS hT h hh
  refine ⟨d₂, ?_⟩
  intro n hbase hloss K A R hK hR htest
  obtain ⟨K1, A1, N1, hK1, hbalanced⟩ :=
    hbridge hbase hloss hK hR htest
  choose cell hcell hconstraint using hbalanced
  refine ⟨cell, hcell, fun s => ?_⟩
  obtain ⟨Cs, hCs, hb⟩ := hN.material_order_transfer_of_balanced_constraint
    hT (A := A1) (N := N1) hK1 s
  exact ⟨Cs, hCs, fun m => hb m (cell m) (hconstraint m)⟩

theorem N01Properties.every_actualCell_materialOrder_from_radialHeightTests
    (hN : N01Properties D T S C base loss ε)
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    (h : ℝ → ℝ) (hh : ∀ r, HasDerivAt h (D.w r) r) :
    ∃ d₂ : ℕ, ∀ {n : ℕ}, base ≤ n → loss + d₂ ≤ n →
    ∀ {K A R : ℝ}, 0 < K → 0 ≤ R →
    (∀ m j : ℕ, Ioo (C.left m) (C.right m) ⊆ D.cells j →
      ∃ η : HeightPair S,
        (∀ r ∈ Ioo (C.left m) (C.right m), ∀ θ : ℝ,
          heightPairField S η =ᶠ[𝓝 (r, θ)] Radial.radialHeightField h) ∧
        heightPairGrading S n η ≤ K * T.H (T.sample j) ^ (-(3 / 4 : ℝ)) *
          T.E0 (T.sample j) ^ A * T.M (T.sample j) ^ (n + 1) *
            radialE (D.cellIndex j) ^ R) →
    ∀ s : ℕ, ∃ Cs : ℝ, 0 < Cs ∧ ∀ m j : ℕ,
      Ioo (C.left m) (C.right m) ⊆ D.cells j →
      T.M (T.sample m) ^ s ≤ Cs * T.M (T.sample j) ^ (s + 1) := by
  obtain ⟨d₂, hbridge⟩ := hN.balanced_constraint_of_radialHeightTests hS hT h hh
  refine ⟨d₂, ?_⟩
  intro n hbase hloss K A R hK hR htest
  obtain ⟨K1, A1, N1, hK1, hbalanced⟩ := hbridge hbase hloss hK hR htest
  exact hN.material_order_transfer_at_every_actualCell hT hK1 hbalanced

end ContinuousFlexibility.Statements
