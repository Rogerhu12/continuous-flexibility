import ContinuousFlexibility.Analysis.N01EndpointCircleTower

/-!
# Zeroth-order tame growth from the actual circle derivative

The endpoint displacement vanishes at the origin. The genuine first
circle derivative along the straight segment therefore controls the
value in every Hilbert coordinate, with the same fixed derivative loss.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

local instance n01EndpointZeroGrowthStateSMul (S : PhysicalSpacesData) :
    SMul ℝ (AnnularState S) := Prod.instSMul

open Set ContinuousFlexibility.Analysis
open scoped Topology BigOperators

private theorem oneHighVariationWeight_single_cons
    {E : Type*} [AddCommGroup E] [Module ℝ E]
    (p : ℕ → Seminorm ℝ E) (B H : ℕ) (y x : E) :
    oneHighVariationWeight p B H y (Fin.cons x (Fin.elim0 : Fin 0 → E)) =
      (1 + p H y) * p B x + p H x := by
  simp [oneHighVariationWeight, Fin.prod_univ_succ, Fin.sum_univ_succ]

theorem N01Properties.endpointFlowCircle_circleNorm_local_growth
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {base loss : ℕ} {ε : ℝ}
    (hN : N01Properties D T S C base loss ε)
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    (rsel : ℕ → ℝ) (hrsel : ∀ m, rsel m ∈ Icc (C.left m) (C.right m)) :
    ∃ B L : ℕ, base ≤ B ∧ ∀ R : ℝ, 0 ≤ R →
      ∀ s : ℕ, B ≤ s → ∃ K : ℝ, 0 ≤ K ∧
      ∀ x ∈ sectorNeighborhood S base ε ε,
      pairGrading (sectorGrading S) realGrading B x ≤ R →
      circleNorm T (3 / 4 : ℝ) s ((S.circle (3 / 4 : ℝ)).decode (hN.endpointFlowCircle hS hT rsel hrsel x)) ≤
        K * (1 + pairGrading (sectorGrading S) realGrading (s + L) x) := by
  obtain ⟨J, hJ⟩ := hN.exists_endpointFlowCircle_smoothDirections hS hT rsel hrsel
  obtain ⟨B, L, hB, hbound⟩ := hN.endpointFlowScalarJets_positive_circleNorm_oneHigh hS hT rsel hrsel
  let p := pairGrading (sectorGrading S) realGrading
  have hzero : (0 : StateDirections S × ℝ) ∈ sectorNeighborhood S base ε ε := by
    constructor
    · change sectorGrading S base (0 : StateDirections S) < ε
      rw [(sectorGrading S base).map_zero']
      exact hN.2.1
    · change |(0 : ℝ)| < ε
      rw [abs_zero]
      exact hN.2.1
  refine ⟨B, L, hB, fun R hR s hs => ?_⟩
  obtain ⟨K, hK, hk⟩ := hbound 0 R hR s hs
  refine ⟨K * (R + 1), mul_nonneg hK (add_nonneg hR zero_le_one), ?_⟩
  intro x hx hxlow
  have hpath (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
      (0 : StateDirections S × ℝ) + t • x ∈ sectorNeighborhood S base ε ε := by
    have hm := (sectorNeighborhood_convex S base ε ε) hzero hx
      (sub_nonneg.mpr ht.2) ht.1 (sub_add_cancel 1 t)
    simpa only [smul_zero, zero_add] using hm
  have hlinegrade (j : ℕ) (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
      p j ((0 : StateDirections S × ℝ) + t • x) ≤ p j x := by
    have ha : |t| ≤ 1 := by simpa only [abs_of_nonneg ht.1] using ht.2
    have h := seminorm_line_le_of_abs_le_one (p j) 0 x ha
    simpa only [(p j).map_zero', zero_add] using h
  have hderiv (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
      HasDerivWithinAt (fun u : ℝ => (J.D 0 (0 + u • x) Fin.elim0).val s)
        ((J.D 1 (0 + t • x) (Fin.cons x Fin.elim0)).val s) (Icc (0 : ℝ) 1) t :=
    (projectiveJet_hasDerivAt_line J.D J.derivative 0 s 0 x Fin.elim0 (hpath t ht)).hasDerivWithinAt
  have hnorm (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
      ‖(J.D 1 (0 + t • x) (Fin.cons x Fin.elim0)).val s‖ ≤
        (K * (R + 1)) * (1 + p (s + L) x) := by
    rw [(hS.2.1 (3 / 4 : ℝ)).2.2.2.2.2.2.2,
      hJ 1 (0 + t • x) (hpath t ht)]
    have hb := hk (0 + t • x) (hpath t ht)
      ((hlinegrade B t ht).trans hxlow) (Fin.cons x Fin.elim0)
    have hw : oneHighVariationWeight p B (s + L) (0 + t • x) (Fin.cons x Fin.elim0) ≤
        (R + 1) * (1 + p (s + L) x) := by
      rw [oneHighVariationWeight_single_cons]
      calc
        _ ≤ (1 + p (s + L) x) * R + p (s + L) x :=
          add_le_add (mul_le_mul
            (add_le_add (le_refl 1) (hlinegrade (s + L) t ht)) hxlow
            (apply_nonneg _ _) (add_nonneg zero_le_one (apply_nonneg _ _))) (le_refl _)
        _ ≤ _ := by nlinarith
    exact hb.trans ((mul_le_mul_of_nonneg_left hw hK).trans_eq (by ring))
  have hm := norm_image_sub_le_of_norm_deriv_le_segment_01' hderiv
    (fun t ht => hnorm t ⟨ht.1, ht.2.le⟩)
  have hval1 : (J.D 0 (0 + (1 : ℝ) • x) Fin.elim0).val s =
      (hN.endpointFlowCircle hS hT rsel hrsel x).val s := by
    simpa only [one_smul, zero_add] using congrArg (fun u : CircleSpace S => u.val s) (J.zero x hx)
  have hval0 : (J.D 0 (0 + (0 : ℝ) • x) Fin.elim0).val s = 0 := by
    have h := (J.zero 0 hzero).trans (hN.endpointFlowCircle_zero hS hT rsel hrsel)
    have hcoordinate := congrArg (fun u : CircleSpace S => u.val s) h
    have hz : (0 : CircleSpace S).val s = 0 :=
      (projectiveCoordinate (fun j => (S.circle (3 / 4 : ℝ)).level j)
        (S.circle (3 / 4 : ℝ)).bond s).map_zero
    simpa only [zero_smul, zero_add, hz] using hcoordinate
  change ‖(J.D 0 (0 + (1 : ℝ) • x) Fin.elim0).val s -
    (J.D 0 (0 + (0 : ℝ) • x) Fin.elim0).val s‖ ≤ _ at hm
  rw [hval1, hval0, sub_zero] at hm
  exact ((hS.2.1 (3 / 4 : ℝ)).2.2.2.2.2.2.2 (hN.endpointFlowCircle hS hT rsel hrsel x) s).symm.trans_le hm

end ContinuousFlexibility.Statements
