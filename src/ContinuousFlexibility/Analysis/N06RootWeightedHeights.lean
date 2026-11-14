module

public import ContinuousFlexibility.Analysis.N06RootNormalizedPacket

/-!
# Material decay of the actual normalized root height jets

The reference-normalized fields remain in the original height space of
weight three quarters. Applying its weighted point evaluation directly
preserves H^(3/4) M. This decay is needed before the root collar and
reference-geometry costs are absorbed; a uniform unweighted bound alone
would not suffice for that step.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Statements

open Set
open ContinuousFlexibility.Analysis
open scoped ContDiff BigOperators

set_option backward.isDefEq.respectTransparency false

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}

def n06RootJetWeight (T : MaterialData) (p : PolarPoint) : ℝ :=
  T.H p.1 ^ (3 / 4 : ℝ) * T.M p.1

theorem n06_rootJetWeight_nonneg (hT : IsMaterialData D T)
    {p : PolarPoint} (hp : p ∈ annularOpen D) : 0 ≤ n06RootJetWeight T p :=
  mul_nonneg (Real.rpow_nonneg (hT.2.1 p.1 hp.1).2.1.le _)
    (zero_le_one.trans (hT.2.1 p.1 hp.1).2.2.2)

theorem n06_root_decoded_spatial_weighted_bound
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S) (n : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (u : ScalarHeightSpace S) k, k ≤ n →
      ∀ p ∈ annularOpen D,
      ‖iteratedFDeriv ℝ k ((S.height scalarBeta).decode u) p‖ ≤
        C * n06RootJetWeight T p * scalarHeightGrading S (n + 2) u := by
  classical
  let I := Fin (n + 1) × Fin (n + 1)
  have hchoices (i : I) := mixedDerivative_decode_le_weighted_grading
    hT (hS.1 scalarBeta) i.1.val i.2.val
  choose c hc hbound using hchoices
  let A : ℝ := ∑ i : I, c i
  have hA : 0 ≤ A := Finset.sum_nonneg (fun i _ => hc i)
  refine ⟨(2 : ℝ) ^ n * A, mul_nonneg (by positivity) hA, ?_⟩
  intro u k hk p hp
  have hW := n06_rootJetWeight_nonneg hT hp
  have hP : 0 ≤ scalarHeightGrading S (n + 2) u := apply_nonneg _ _
  have hm (a b : ℕ) (hab : a + b = k) :
      ‖mixedDerivative a b ((S.height scalarBeta).decode u) p‖ ≤
        A * n06RootJetWeight T p * scalarHeightGrading S (n + 2) u := by
    let i : I := (⟨a, by omega⟩, ⟨b, by omega⟩)
    have hi : c i ≤ A := Finset.single_le_sum (fun j _ => hc j) (Finset.mem_univ i)
    have horder : i.1.val + i.2.val + 2 ≤ n + 2 := by
      change a + b + 2 ≤ n + 2
      omega
    have hfirst : ‖mixedDerivative a b ((S.height scalarBeta).decode u) p‖ ≤
        c i * n06RootJetWeight T p * scalarHeightGrading S (i.1.val + i.2.val + 2) u := by
      have hraw : |mixedDerivative a b ((S.height scalarBeta).decode u) p| ≤
          c i * T.H p.1 ^ scalarBeta * T.M p.1 *
            scalarHeightGrading S (i.1.val + i.2.val + 2) u := hbound i u p hp
      change |mixedDerivative a b ((S.height scalarBeta).decode u) p| ≤ _
      apply hraw.trans_eq
      change c i * T.H p.1 ^ scalarBeta * T.M p.1 *
          scalarHeightGrading S (i.1.val + i.2.val + 2) u =
        c i * (T.H p.1 ^ scalarBeta * T.M p.1) *
          scalarHeightGrading S (i.1.val + i.2.val + 2) u
      ring
    exact hfirst.trans ((mul_le_mul_of_nonneg_left
      (scalarHeightGrading_monotone S horder u) (mul_nonneg (hc i) hW)).trans
        (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hi hW) hP))
  have hh := norm_iteratedFDeriv_le_of_mixedDerivative (isOpen_Ioo.prod isOpen_univ)
    (scalarHeight_decode_contDiff_and_flatJets hT hS u).1.contDiffOn k hp
    (mul_nonneg (mul_nonneg hA hW) hP) hm
  exact hh.trans ((mul_le_mul_of_nonneg_right
    (pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) hk)
      (mul_nonneg (mul_nonneg hA hW) hP)).trans_eq (by ring))

theorem n06_root_decoded_and_angular_spatial_weighted_bound
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S) (n : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (u : ScalarHeightSpace S) k, k ≤ n →
      ∀ p ∈ annularOpen D,
      ‖iteratedFDeriv ℝ k ((S.height scalarBeta).decode u) p‖ ≤
          C * n06RootJetWeight T p * scalarHeightGrading S (n + 3) u ∧
        ‖iteratedFDeriv ℝ k (angularPartial ((S.height scalarBeta).decode u)) p‖ ≤
          C * n06RootJetWeight T p * scalarHeightGrading S (n + 3) u := by
  obtain ⟨C, hC, hb⟩ := n06_root_decoded_spatial_weighted_bound hT hS (n + 1)
  refine ⟨C, hC, ?_⟩
  intro u k hk p hp
  have hs := (scalarHeight_decode_contDiff_and_flatJets hT hS u).1
  constructor
  · exact hb u k (by omega) p hp
  · have h := n06_norm_iteratedFDeriv_directional_le
      (isOpen_Ioo.prod isOpen_univ) hs.contDiffOn (0, 1) k hp
    have he : ‖((0, 1) : PolarPoint)‖ = 1 := by simp
    rw [he, mul_one] at h
    exact h.trans (hb u (k + 1) (by omega) p hp)

private theorem n06_root_tame_height_spatial_weighted_bound
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (L : ScalarCommonHeight S →L[ℝ] ScalarHeightSpace S)
    (hL : IsTameLinear (scalarCommonHeightGrading S) (scalarHeightGrading S)
      L.toLinearMap 4 0) (n : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (u : ScalarCommonHeight S) k, k ≤ n → ∀ p ∈ annularOpen D,
      ‖iteratedFDeriv ℝ k ((S.height scalarBeta).decode (L u)) p‖ ≤
          C * n06RootJetWeight T p * scalarCommonHeightGrading S (n + 7) u ∧
        ‖iteratedFDeriv ℝ k (angularPartial ((S.height scalarBeta).decode (L u))) p‖ ≤
          C * n06RootJetWeight T p * scalarCommonHeightGrading S (n + 7) u := by
  obtain ⟨J, hJ, hj⟩ := n06_root_decoded_and_angular_spatial_weighted_bound hT hS n
  obtain ⟨A, ha⟩ := hL (n + 3) (Nat.zero_le _)
  refine ⟨J * A, mul_nonneg hJ A.coe_nonneg, ?_⟩
  intro u k hk p hp
  have hgrade : scalarHeightGrading S (n + 3) (L u) ≤
      (A : ℝ) * scalarCommonHeightGrading S (n + 7) u := ha u
  have hb := hj (L u) k hk p hp
  have hscale := (mul_le_mul_of_nonneg_left hgrade
    (mul_nonneg hJ (n06_rootJetWeight_nonneg hT hp))).trans_eq
      (show J * n06RootJetWeight T p * ((A : ℝ) * scalarCommonHeightGrading S (n + 7) u) =
        (J * A) * n06RootJetWeight T p * scalarCommonHeightGrading S (n + 7) u by ring)
  exact ⟨hb.1.trans hscale, hb.2.trans hscale⟩

def N06RootHeightSpatialWeightedBound (D : ReferenceData) (T : MaterialData)
    (S : PhysicalSpacesData) (n : ℕ) (C : ℝ) : Prop :=
  ∀ (u : ScalarCommonHeight S) (i : Fin 4) k, k ≤ n → ∀ p ∈ annularOpen D,
    ‖iteratedFDeriv ℝ k (n06RootNormalizedHeightFields D S u i) p‖ ≤
      C * n06RootJetWeight T p * scalarCommonHeightGrading S (n + 7) u

theorem n06_rootNormalizedHeightFields_spatial_weighted_bound
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T)
    (hS : IsPhysicalSpaces D T S) (n : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ N06RootHeightSpatialWeightedBound D T S n C := by
  have hm := weighted_scalarCommonHeightGrading_monotone S
  obtain ⟨A, hA, ha⟩ := n06_root_tame_height_spatial_weighted_bound hT hS
    (n06RootNormalizedRadialCLM hD hT hS)
    ((n06RootNormalizedRadialCLM_isTame hD hT hS).weaken hm (by norm_num) le_rfl) n
  obtain ⟨B, hB, hb⟩ := n06_root_tame_height_spatial_weighted_bound hT hS
    (n06RootAngularPrimitiveCLM hD hT hS)
    ((n06RootAngularPrimitiveCLM_isTame hD hT hS).weaken hm (by norm_num) le_rfl) n
  obtain ⟨C, hC, hc⟩ := n06_root_tame_height_spatial_weighted_bound hT hS
    (n06RootNormalizedMixedPrimitiveCLM hD hT hS)
    (n06RootNormalizedMixedPrimitiveCLM_isTame hD hT hS) n
  obtain ⟨E, hE, he⟩ := n06_root_tame_height_spatial_weighted_bound hT hS
    (n06RootNormalizedAngularSecondCLM hD hT hS)
    (n06RootNormalizedAngularSecondCLM_isTame hD hT hS) n
  refine ⟨A + B + C + E, by positivity, ?_⟩
  intro u i k hk p hp
  have hP : 0 ≤ scalarCommonHeightGrading S (n + 7) u := apply_nonneg _ _
  have hW := n06_rootJetWeight_nonneg hT hp
  have hle {a : ℝ} (ha : a ≤ A + B + C + E) :
      a * n06RootJetWeight T p * scalarCommonHeightGrading S (n + 7) u ≤
        (A + B + C + E) * n06RootJetWeight T p * scalarCommonHeightGrading S (n + 7) u :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right ha hW) hP
  fin_cases i
  · change ‖iteratedFDeriv ℝ k (fun q =>
      (D.w q.1)⁻¹ * radialPartial (scalarCommonHeightDecode S u) q) p‖ ≤ _
    rw [← funext (n06_decode_rootNormalizedRadial hD hT hS u)]
    exact (ha u k hk p hp).1.trans (hle (by linarith))
  · change ‖iteratedFDeriv ℝ k (heightAngular (scalarCommonHeightDecode S u)) p‖ ≤ _
    rw [← n06_angularPartial_decode_rootAngularPrimitive hD hT hS u]
    exact (hb u k hk p hp).2.trans (hle (by linarith))
  · change ‖iteratedFDeriv ℝ k (fun q =>
      (D.w q.1)⁻¹ * radialPartial (heightAngular (scalarCommonHeightDecode S u)) q) p‖ ≤ _
    rw [← n06_angularPartial_decode_rootNormalizedMixedPrimitive hD hT hS u]
    exact (hc u k hk p hp).2.trans (hle (by linarith))
  · change ‖iteratedFDeriv ℝ k (fun q =>
      (D.w q.1)⁻¹ * angularPartial (heightAngular (scalarCommonHeightDecode S u)) q) p‖ ≤ _
    rw [← funext (n06_decode_rootNormalizedAngularSecond hD hT hS u)]
    exact (he u k hk p hp).1.trans (hle (by linarith))

end ContinuousFlexibility.Statements
