import ContinuousFlexibility.Analysis.CanonicalRootHeightJets
import ContinuousFlexibility.Analysis.CanonicalRootDiagonalLower

/-!
# Actual finite endpoint bounds from the same Through03 witness

The low state order is increased once, before any component. The already
proved root jet families then give finite numerical envelopes. Their
inverse first jet supplies the positive diagonal lower bound. No raw
endpoint estimate or state-uniform coefficient collar is assumed.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set
open ContinuousFlexibility.Statements ContinuousFlexibility.Blueprint
open scoped BigOperators ContDiff

set_option backward.isDefEq.respectTransparency false

structure RootEndpointJetBounds (n : ℕ)
    (F : PolarPoint → PolarPoint) (q : PolarPoint → ℝ) (r κ M H : ℝ) : Prop where
  radial_lower : ∀ θ, κ ≤ radialPartial (fun p => (F p).1) (r, θ)
  angular_lower : ∀ θ, κ ≤ angularPartial (fun p => (F p).2) (r, θ)
  coordinate_jets : ∀ k, 1 ≤ k → k ≤ n + 2 → ∀ θ,
    ‖iteratedFDeriv ℝ k F (r, θ)‖ ≤ M
  height_value : ∀ θ, q (r, θ) ≤ H
  height_inverse : ∀ θ, (q (r, θ))⁻¹ ≤ H
  height_jets : ∀ k, 1 ≤ k → k ≤ n → ∀ θ,
    ‖iteratedFDeriv ℝ k q (r, θ)‖ ≤ H

private def rootFiniteEnvelope (N : ℕ) (A : ℕ → ℝ) : ℝ :=
  1 + ∑ k ∈ Finset.range (N + 1), 2 * A k

private theorem rootFiniteEnvelope_one_le (N : ℕ) {A : ℕ → ℝ}
    (hA : ∀ k, 0 < A k) : 1 ≤ rootFiniteEnvelope N A := by
  exact le_add_of_nonneg_right
    (Finset.sum_nonneg fun k _ => mul_nonneg (by norm_num) (hA k).le)

private theorem rootFiniteEnvelope_term {N k : ℕ} {A : ℕ → ℝ}
    (hA : ∀ k, 0 < A k) (hk : k ≤ N) : 2 * A k ≤ rootFiniteEnvelope N A := by
  have ht : 2 * A k ≤ ∑ j ∈ Finset.range (N + 1), 2 * A j :=
    Finset.single_le_sum (fun j _ => mul_nonneg (by norm_num) (hA j).le)
      (Finset.mem_range.mpr (Nat.lt_succ_of_le hk))
  exact ht.trans (le_add_of_nonneg_left zero_le_one)

/-- Every finite-order endpoint bound is derived for the actual maps and
heights. The output neighborhood is common to all negative components
and both ends; only the finite constants depend on the component. -/
theorem n04b_exists_common_root_finite_endpoint_bounds
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {E : ReturnEquationData S}
    {L : ReturnCorrectionData S} {K : CanonicalData S}
    {base loss : ℕ} {ε : ℝ}
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    (hN : NonlinearPropertiesThrough03 D T S C E L base loss ε)
    (hfield : N04bFieldRegularity D S C L base ε)
    (hA : N04PartA D S C K base ε) (hB : N04PartB S C L K base ε) (n : ℕ) :
    ∃ newBase : ℕ, ∃ ε' : ℝ,
      base ≤ newBase ∧ 0 < ε' ∧ ε' ≤ ε ∧
      ∀ m : ℕ, ∀ side : Bool, ∃ κ M H : ℝ,
        0 < κ ∧ κ ≤ 1 ∧ 1 ≤ M ∧ 1 ≤ H ∧
        ∀ z ∈ stateNeighborhood S C newBase ε', stateSector S z.1 →
          let i := if side then (K.cutPair m).2 else (K.cutPair m).1
          RootEndpointJetBounds n (canonicalCurrentPoint C K z i)
            (n04CoordinatesCurrentHeightRatio C K z i)
            (n01ComponentRoot C m side) κ M H := by
  have hp : Monotone (pairGrading (stateGrading S) realGrading) :=
    tamePairGrading_monotone (stateGrading_monotone S) (fun _ _ _ => le_rfl)
  obtain ⟨relativeBase, relativeLoss, ηT, hbT, _hTlow, hηT, hηTε, hrelative⟩ :=
    n04b_exists_common_root_relative_positiveJets hS hT hN hfield hA hB
  obtain ⟨heightBase, heightLoss, ηH, hbH, _hHlow, hηH, hηHε, hheight⟩ :=
    n04b_exists_common_root_heightJets hS hT hN hfield hA hB
  let newBase := max relativeBase
    (max heightBase (max (n + 2 + relativeLoss) (n + heightLoss)))
  let ε' := min (min ηT ηH) (1 / 2 : ℝ)
  have hbaseT : relativeBase ≤ newBase := le_max_left _ _
  have hbaseH : heightBase ≤ newBase := (le_max_left _ _).trans (le_max_right _ _)
  have horderT : n + 2 + relativeLoss ≤ newBase :=
    (le_max_left _ _).trans ((le_max_right _ _).trans (le_max_right _ _))
  have horderH : n + heightLoss ≤ newBase :=
    (le_max_right _ _).trans ((le_max_right _ _).trans (le_max_right _ _))
  have hε'T : ε' ≤ ηT := (min_le_left _ _).trans (min_le_left _ _)
  have hε'H : ε' ≤ ηH := (min_le_left _ _).trans (min_le_right _ _)
  have hb' : base ≤ newBase := hbT.trans hbaseT
  have hε' : 0 < ε' := lt_min (lt_min hηT hηH) (by norm_num)
  have hε'ε : ε' ≤ ε := hε'T.trans hηTε
  have href : (C.referenceState, 0) ∈ stateNeighborhood S C base ε :=
    reference_mem_stateNeighborhood S C base hN.1.1.2.1
  have hsref : stateSector S C.referenceState := hN.1.1.2.2.1.stateSector
  refine ⟨newBase, ε', hb', hε', hε'ε, ?_⟩
  intro m side
  let i := if side then (K.cutPair m).2 else (K.cutPair m).1
  let r := n01ComponentRoot C m side
  obtain ⟨A, hApos, hrel⟩ := hrelative m side
  obtain ⟨B, hBpos, hheights⟩ := hheight m side
  let M := rootFiniteEnvelope (n + 2) A
  let H := rootFiniteEnvelope n B
  have hMone : 1 ≤ M := rootFiniteEnvelope_one_le (n + 2) hApos
  have hHone : 1 ≤ H := rootFiniteEnvelope_one_le n hBpos
  have hM : 0 < M := zero_lt_one.trans_le hMone
  refine ⟨M⁻¹, M, H, inv_pos.mpr hM, inv_le_one_of_one_le₀ hMone,
    hMone, hHone, ?_⟩
  intro z hz hs
  have hzold : z ∈ stateNeighborhood S C base ε :=
    stateNeighborhood_mono S C hb' hε'ε hz
  have hzT : z ∈ stateNeighborhood S C relativeBase ηT :=
    stateNeighborhood_mono S C hbaseT hε'T hz
  have hzH : z ∈ stateNeighborhood S C heightBase ηH :=
    stateNeighborhood_mono S C hbaseH hε'H hz
  have hsmall : pairGrading (stateGrading S) realGrading newBase
      (z - (C.referenceState, 0)) ≤ 1 :=
    (pairGrading_displacement_le_two_mul_radius hz).trans (by
      have he : ε' ≤ 1 / 2 := min_le_right _ _
      linarith only [he])
  have hfinite {N k d : ℕ} {Q : ℕ → ℝ} (hQ : ∀ k, 0 < Q k)
      (hk : k ≤ N) (hNd : N + d ≤ newBase) {v : ℝ}
      (hv : v ≤ Q k * (1 + pairGrading (stateGrading S) realGrading (k + d)
        (z - (C.referenceState, 0)))) : v ≤ rootFiniteEnvelope N Q := by
    have hg : pairGrading (stateGrading S) realGrading (k + d)
        (z - (C.referenceState, 0)) ≤ 1 :=
      (hp ((Nat.add_le_add_right hk d).trans hNd) _).trans hsmall
    calc
      v ≤ Q k * (1 + pairGrading (stateGrading S) realGrading (k + d)
        (z - (C.referenceState, 0))) := hv
      _ ≤ Q k * (1 + 1) := mul_le_mul_of_nonneg_left (add_le_add_left hg 1) (hQ k).le
      _ = 2 * Q k := by ring
      _ ≤ rootFiniteEnvelope N Q := rootFiniteEnvelope_term hQ hk
  have hcoordinate (θ : ℝ) (k : ℕ) (hk : 1 ≤ k) (hkn : k ≤ n + 2) :
      ‖iteratedFDeriv ℝ k (canonicalCurrentPoint C K z i) (r, θ)‖ ≤ M :=
    hfinite hApos hkn horderT ((hrel z hzT hs θ).2.2.1 k hk)
  have hdiagonal (θ : ℝ) :
      M⁻¹ ≤ radialPartial (fun p => (canonicalCurrentPoint C K z i p).1) (r, θ) ∧
        M⁻¹ ≤ angularPartial (fun p => (canonicalCurrentPoint C K z i p).2) (r, θ) := by
    let τ := canonicalCurrentPoint C K z i
    have hy : τ (r, θ) = (r, (τ (r, θ)).2) :=
      Prod.ext (canonicalCurrentPoint_root_radial hA hB.1 href hsref hzold hs m side θ) rfl
    have hInv : ‖fderiv ℝ (canonicalReferencePoint C K z i) (τ (r, θ))‖ ≤ M := by
      rw [hy]
      simpa only [norm_iteratedFDeriv_one] using
        hfinite hApos (show 1 ≤ n + 2 by omega) horderT
          ((hrel z hzT hs (τ (r, θ)).2).2.2.2 1 le_rfl)
    exact canonicalCurrentPoint_root_diagonal_lower
      hA hB.1 href hsref hzold hs m side θ hM hInv
  refine {
    radial_lower := fun θ => (hdiagonal θ).1
    angular_lower := fun θ => (hdiagonal θ).2
    coordinate_jets := fun k hk hkn θ => hcoordinate θ k hk hkn
    height_value := ?_
    height_inverse := ?_
    height_jets := ?_ }
  · intro θ
    have hh : |n04CoordinatesCurrentHeightRatio C K z i (r, θ)| ≤ H := by
      simpa only [norm_iteratedFDeriv_zero, Real.norm_eq_abs] using
        hfinite hBpos (Nat.zero_le n) horderH ((hheights z hzH hs θ).2.2.1 0)
    exact (le_abs_self _).trans hh
  · intro θ
    have hh : |(n04CoordinatesCurrentHeightRatio C K z i (r, θ))⁻¹| ≤ H := by
      simpa only [norm_iteratedFDeriv_zero, Real.norm_eq_abs] using
        hfinite hBpos (Nat.zero_le n) horderH ((hheights z hzH hs θ).2.2.2 0)
    exact (le_abs_self _).trans hh
  · intro k _hk hkn θ
    exact hfinite hBpos hkn horderH ((hheights z hzH hs θ).2.2.1 k)

end ContinuousFlexibility.Analysis
