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

private theorem zeroGrowth_seminorm_zero_line_le
    {E : Type*} [AddCommGroup E] [Module ℝ E]
    (p : Seminorm ℝ E) (x : E) {t : ℝ} (ht : |t| ≤ 1) :
    p (0 + t • x) ≤ p x := by
  have h := seminorm_line_le_of_abs_le_one p 0 x ht
  have hz : p 0 + p x = p x :=
    (congrArg (fun a : ℝ => a + p x) p.map_zero').trans (zero_add _)
  exact h.trans_eq hz

private theorem zeroGrowth_oneHigh_single_cons_le
    {E : Type*} [AddCommGroup E] [Module ℝ E]
    (p : ℕ → Seminorm ℝ E) (B H : ℕ) (y x : E) {R : ℝ}
    (hlow : p B x ≤ R) (hline : p H y ≤ p H x) :
    oneHighVariationWeight p B H y (Fin.cons x (Fin.elim0 : Fin 0 → E)) ≤
      (R + 1) * (1 + p H x) := by
  rw [oneHighVariationWeight_single_cons]
  calc
    (1 + p H y) * p B x + p H x ≤ (1 + p H x) * R + p H x :=
      add_le_add (mul_le_mul (add_le_add (le_refl 1) hline) hlow
        (apply_nonneg _ _) (add_nonneg zero_le_one (apply_nonneg _ _))) (le_refl _)
    _ ≤ (R + 1) * (1 + p H x) := by nlinarith

/-- The constants are fixed before every choice of closed flow radii. -/
theorem N01Properties.endpointFlowCircle_circleNorm_local_growth_uniform_radius
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {base loss : ℕ} {ε : ℝ}
    (hN : N01Properties D T S C base loss ε)
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T) :
    ∃ B L : ℕ, base ≤ B ∧ ∀ R : ℝ, 0 ≤ R →
      ∀ s : ℕ, B ≤ s → ∃ K : ℝ, 0 ≤ K ∧
      ∀ (rsel : ℕ → ℝ) (hrsel : ∀ m, rsel m ∈ Icc (C.left m) (C.right m)),
      ∀ x ∈ sectorNeighborhood S base ε ε,
      pairGrading (sectorGrading S) realGrading B x ≤ R →
      circleNorm T (3 / 4 : ℝ) s ((S.circle (3 / 4 : ℝ)).decode (hN.endpointFlowCircle hS hT rsel hrsel x)) ≤
        K * (1 + pairGrading (sectorGrading S) realGrading (s + L) x) := by
  let bounds := N01Properties.endpointFlowScalarJets_positive_circleNorm_oneHigh_uniform_radius
    (D := D) (T := T) (S := S) (C := C) (base := base) (loss := loss) (ε := ε) hN hS hT 0
  let B : ℕ := bounds.choose
  let L : ℕ := bounds.choose_spec.choose
  have hB : base ≤ B := bounds.choose_spec.choose_spec.1
  let p := pairGrading (sectorGrading S) realGrading
  have hzero : (0 : StateDirections S × ℝ) ∈ sectorNeighborhood S base ε ε :=
    ⟨(sectorGrading S base).map_zero'.trans_lt hN.2.1,
      (abs_zero : |(0 : ℝ)| = 0).trans_lt hN.2.1⟩
  refine ⟨B, L, hB, fun R hR s hs => ?_⟩
  let estimate := bounds.choose_spec.choose_spec.2 R hR s hs
  let K : ℝ := estimate.choose
  have hK : 0 ≤ K := estimate.choose_spec.1
  refine ⟨K * (R + 1), mul_nonneg hK (add_nonneg hR zero_le_one), ?_⟩
  intro rsel hrsel x hx hxlow
  let tower := N01Properties.exists_endpointFlowCircle_smoothDirections
    (D := D) (T := T) (S := S) (C := C) (base := base) (loss := loss) (ε := ε)
      hN hS hT rsel hrsel
  let J : SmoothDirections (sectorNeighborhood S base ε ε)
      (hN.endpointFlowCircle hS hT rsel hrsel) := tower.choose
  have hJ (n : ℕ) (y : StateDirections S × ℝ)
      (hy : y ∈ sectorNeighborhood S base ε ε) (v : Fin n → (StateDirections S × ℝ)) :
      (S.circle (3 / 4 : ℝ)).decode (J.D n y v) =
        hN.endpointFlowScalarJets hS hT rsel hrsel n y v := tower.choose_spec n y hy v
  have hpath (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
      (0 : StateDirections S × ℝ) + t • x ∈ sectorNeighborhood S base ε ε := by
    have hm := (sectorNeighborhood_convex S base ε ε) hzero hx
      (sub_nonneg.mpr ht.2) ht.1 (sub_add_cancel 1 t)
    simpa only [smul_zero, zero_add] using hm
  have hlinegrade (j : ℕ) (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
      p j ((0 : StateDirections S × ℝ) + t • x) ≤ p j x := by
    have ha : |t| ≤ 1 := by simpa only [abs_of_nonneg ht.1] using ht.2
    exact zeroGrowth_seminorm_zero_line_le (p j) x ha
  have hderiv (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
      HasDerivWithinAt (fun u : ℝ => (J.D 0 (0 + u • x) Fin.elim0).val s)
        ((J.D 1 (0 + t • x) (Fin.cons x Fin.elim0)).val s) (Icc (0 : ℝ) 1) t :=
    (projectiveJet_hasDerivAt_line J.D J.derivative 0 s 0 x Fin.elim0 (hpath t ht)).hasDerivWithinAt
  have hnorm (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
      ‖(J.D 1 (0 + t • x) (Fin.cons x Fin.elim0)).val s‖ ≤
        (K * (R + 1)) * (1 + p (s + L) x) := by
    have heq : ‖(J.D 1 (0 + t • x) (Fin.cons x Fin.elim0)).val s‖ =
        circleNorm T (3 / 4 : ℝ) s
          (hN.endpointFlowScalarJets hS hT rsel hrsel 1 (0 + t • x)
            (Fin.cons x Fin.elim0)) :=
      ((hS.2.1 (3 / 4 : ℝ)).2.2.2.2.2.2.2
        (J.D 1 (0 + t • x) (Fin.cons x Fin.elim0)) s).trans
        (congrArg (circleNorm T (3 / 4 : ℝ) s)
          (hJ 1 (0 + t • x) (hpath t ht) (Fin.cons x Fin.elim0)))
    have hb := estimate.choose_spec.2 rsel hrsel (0 + t • x) (hpath t ht)
      ((hlinegrade B t ht).trans hxlow) (Fin.cons x Fin.elim0)
    have hw := zeroGrowth_oneHigh_single_cons_le p B (s + L) (0 + t • x) x
      hxlow (hlinegrade (s + L) t ht)
    exact heq.trans_le (hb.trans
      ((mul_le_mul_of_nonneg_left hw hK).trans_eq
        (mul_assoc K (R + 1) (1 + p (s + L) x)).symm))
  have hm := norm_image_sub_le_of_norm_deriv_le_segment_01' hderiv
    (fun t ht => hnorm t ⟨ht.1, ht.2.le⟩)
  have hval1 : (J.D 0 (0 + (1 : ℝ) • x) Fin.elim0).val s =
      (hN.endpointFlowCircle hS hT rsel hrsel x).val s :=
    (congrArg (fun y : StateDirections S × ℝ => (J.D 0 y Fin.elim0).val s)
      ((zero_add ((1 : ℝ) • x)).trans (one_smul ℝ x))).trans
        (congrArg (fun u : CircleSpace S => u.val s) (J.zero x hx))
  have hval0 : (J.D 0 (0 + (0 : ℝ) • x) Fin.elim0).val s = 0 := by
    have h := (J.zero 0 hzero).trans (hN.endpointFlowCircle_zero hS hT rsel hrsel)
    have hcoordinate := congrArg (fun u : CircleSpace S => u.val s) h
    have hz : (0 : CircleSpace S).val s = 0 :=
      (projectiveCoordinate (fun j => (S.circle (3 / 4 : ℝ)).level j)
        (S.circle (3 / 4 : ℝ)).bond s).map_zero
    exact (congrArg (fun y : StateDirections S × ℝ => (J.D 0 y Fin.elim0).val s)
      ((zero_add ((0 : ℝ) • x)).trans (zero_smul ℝ x))).trans (hcoordinate.trans hz)
  have hdiff : (J.D 0 (0 + (1 : ℝ) • x) Fin.elim0).val s -
      (J.D 0 (0 + (0 : ℝ) • x) Fin.elim0).val s =
        (hN.endpointFlowCircle hS hT rsel hrsel x).val s :=
    (congrArg₂ (fun u v : (S.circle (3 / 4 : ℝ)).level s => u - v) hval1 hval0).trans
      (sub_zero _)
  have hnormvalue : ‖(hN.endpointFlowCircle hS hT rsel hrsel x).val s‖ ≤
      (K * (R + 1)) * (1 + p (s + L) x) :=
    (congrArg (fun u : (S.circle (3 / 4 : ℝ)).level s => ‖u‖) hdiff).symm.trans_le hm
  exact ((hS.2.1 (3 / 4 : ℝ)).2.2.2.2.2.2.2
    (hN.endpointFlowCircle hS hT rsel hrsel x) s).symm.trans_le hnormvalue

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
  let bounds := N01Properties.endpointFlowCircle_circleNorm_local_growth_uniform_radius
    (D := D) (T := T) (S := S) (C := C) (base := base) (loss := loss) (ε := ε) hN hS hT
  let B : ℕ := bounds.choose
  let L : ℕ := bounds.choose_spec.choose
  have hB : base ≤ B := bounds.choose_spec.choose_spec.1
  refine ⟨B, L, hB, fun R hR s hs => ?_⟩
  let estimate := bounds.choose_spec.choose_spec.2 R hR s hs
  exact ⟨estimate.choose, estimate.choose_spec.1, estimate.choose_spec.2 rsel hrsel⟩

end ContinuousFlexibility.Statements
