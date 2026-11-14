module

public import ContinuousFlexibility.Analysis.N06ReferenceNullTransport
public import ContinuousFlexibility.Analysis.N06IrrationalCircleRigidity
public import ContinuousFlexibility.Analysis.N05N06ClosedChartBridge

/-!
# The actual reference cut bisects the optical travel

At a physical root the two null coordinates have the same circle value.
At the actual cut their difference is constant.  The lift condition fixes
this constant to the true optical displacement.  This determines the
directions of both characteristics and the two equal half travels,
without assigning values to the inverse chart at a boundary.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Statements

open Set Filter MeasureTheory
open scoped Topology ContDiff

set_option backward.isDefEq.respectTransparency false

theorem n06_null_cut_displacement
    {β : ℝ → ℝ} {t c τp τn : ℝ} (hβ : Continuous β)
    (hlift : ∀ θ, β (θ + Real.pi) = β θ + Real.pi)
    (hc : 0 < c) (hτp : τp ^ 2 = 1) (hτn : τn ^ 2 = 1)
    (hcut : ∀ θ, β (θ + τp * t) - β (θ + τn * t) = 2 * c) :
    τn = -τp ∧ τp * t = c ∧ ∀ θ, β (θ + 2 * c) = β θ + 2 * c := by
  have hstep (θ : ℝ) :
      β (θ + (τp - τn) * t) = β θ + 2 * c := by
    have he := hcut (θ - τn * t)
    have harg₁ : θ - τn * t + τp * t = θ + (τp - τn) * t := by ring
    have harg₂ : θ - τn * t + τn * t = θ := by ring
    rw [harg₁, harg₂] at he
    linarith only [he]
  have hdis : 2 * c = (τp - τn) * t :=
    n06_circleLift_translation_displacement hβ hlift hstep
  have hopp : τn = -τp := by
    rcases sq_eq_sq_iff_eq_or_eq_neg.mp (hτn.trans hτp.symm) with heq | heq
    · rw [heq, sub_self, zero_mul] at hdis
      linarith only [hc, hdis]
    · exact heq
  have htime : τp * t = c := by
    rw [hopp] at hdis
    nlinarith only [hdis]
  refine ⟨hopp, htime, fun θ => ?_⟩
  simpa only [hdis] using hstep θ

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {R : ReturnEquationData S}
  {L : ReturnCorrectionData S} {K : CanonicalData S} {base loss : ℕ} {ε : ℝ}

/-- Root and cut values of the actual forward chart determine its full
null characteristic formula and the boundary circle's second period. -/
theorem n06_reference_null_root_cut
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (h : NonlinearPropertiesThrough04 D T S C R L K base loss ε)
    {i : ℕ} (hi : K.positive i = false)
    (hinside : Icc (K.physicalLeft i) (K.physicalRight i) ⊆ radialCore D)
    {root cut y : ℝ} (hroot : root ∈ Icc (K.physicalLeft i) (K.physicalRight i))
    (hcut : cut ∈ Icc (K.physicalLeft i) (K.physicalRight i))
    (hwroot : deriv D.w root = 0) (hy : 0 < y)
    (hcutImage : ∀ θ, (K.chart (C.referenceState, 0) i (cut, θ)).1 = y) :
    let β : ℝ → ℝ := fun θ => (K.chart (C.referenceState, 0) i (root, θ)).2
    ∃ τ : ℝ, τ ^ 2 = 1 ∧ τ * opticalTravel D.w root cut = n05TricomiTime y ∧
      (∀ θ, β (θ + 2 * n05TricomiTime y) = β θ + 2 * n05TricomiTime y) ∧
      ∀ r ∈ Icc (K.physicalLeft i) (K.physicalRight i), ∀ θ,
        n05NullCoordinate (K.chart (C.referenceState, 0) i) 1 (r, θ) =
          β (θ + τ * opticalTravel D.w root r) ∧
        n05NullCoordinate (K.chart (C.referenceState, 0) i) (-1) (r, θ) =
          β (θ - τ * opticalTravel D.w root r) := by
  let Ψ : PolarPoint → PolarPoint := K.chart (C.referenceState, 0) i
  let β : ℝ → ℝ := fun θ => (Ψ (root, θ)).2
  change ∃ τ : ℝ, τ ^ 2 = 1 ∧ τ * opticalTravel D.w root cut = n05TricomiTime y ∧
      (∀ θ, β (θ + 2 * n05TricomiTime y) = β θ + 2 * n05TricomiTime y) ∧
      ∀ r ∈ Icc (K.physicalLeft i) (K.physicalRight i), ∀ θ,
        n05NullCoordinate Ψ 1 (r, θ) = β (θ + τ * opticalTravel D.w root r) ∧
        n05NullCoordinate Ψ (-1) (r, θ) = β (θ - τ * opticalTravel D.w root r)
  have h01 := h.1.1.1
  have href := n05_referenceState_mem (S := S) (C := C) (base := base) h01.2.1
  have hs := n05_referenceState_sector h01.2.2.1
  have hA := h.2.2.2.2.1.1
  have hrootClosed (θ : ℝ) : (root, θ) ∈ physicalPieceClosed S K (C.referenceState, 0) i := by
    rw [n05_referencePhysicalPieceClosed_eq hA i]
    exact ⟨hroot, mem_univ _⟩
  have hβ : Continuous β := continuous_iff_continuousAt.mpr fun θ =>
    ((n05_reference_boundary_regular hA href hs i (p := (root, θ)) hroot).1.snd.continuousAt).comp
      (continuousAt_const.prodMk continuousAt_id)
  have hlift (θ : ℝ) : β (θ + Real.pi) = β θ + Real.pi := by
    simpa only [β, Ψ, Prod.mk_add_mk, Prod.snd_add, Prod.fst_add, add_zero] using
      congrArg Prod.snd (n05_canonical_closed_periodicity h.2.2.2.2.1 href hs i
        (p := (root, θ)) (hrootClosed θ)).1
  have hrootImage (θ : ℝ) : (Ψ (root, θ)).1 = 0 :=
    n05_negative_reference_root_image hT hS h hi (x := (root, θ)) hroot hwroot
  have hrootN (σ θ : ℝ) : n05NullCoordinate Ψ σ (root, θ) = β θ := by
    simp only [n05NullCoordinate, hrootImage, n05TricomiTime_zero, mul_zero, add_zero, β]
  obtain ⟨τp, hτp, hplus⟩ := n06_negative_reference_null_transport hT hS h hi hinside
    (σ := 1) (by norm_num)
  obtain ⟨τn, hτn, hminus⟩ := n06_negative_reference_null_transport hT hS h hi hinside
    (σ := -1) (by norm_num)
  have hplus' (r : ℝ) (hr : r ∈ Icc (K.physicalLeft i) (K.physicalRight i)) (θ : ℝ) :
      n05NullCoordinate Ψ 1 (r, θ) = β (θ + τp * opticalTravel D.w root r) := by
    exact (hplus r hr root hroot θ).trans (hrootN 1 _)
  have hminus' (r : ℝ) (hr : r ∈ Icc (K.physicalLeft i) (K.physicalRight i)) (θ : ℝ) :
      n05NullCoordinate Ψ (-1) (r, θ) = β (θ + τn * opticalTravel D.w root r) := by
    exact (hminus r hr root hroot θ).trans (hrootN (-1) _)
  have hdiff (θ : ℝ) : β (θ + τp * opticalTravel D.w root cut) -
      β (θ + τn * opticalTravel D.w root cut) = 2 * n05TricomiTime y := by
    rw [← hplus' cut hcut θ, ← hminus' cut hcut θ]
    change ((Ψ (cut, θ)).2 + 1 * n05TricomiTime (Ψ (cut, θ)).1) -
      ((Ψ (cut, θ)).2 + (-1) * n05TricomiTime (Ψ (cut, θ)).1) = _
    have hci : (Ψ (cut, θ)).1 = y := hcutImage θ
    rw [hci]
    ring
  have htime : 0 < n05TricomiTime y :=
    mul_pos (mul_pos (by norm_num) hy) (Real.sqrt_pos.mpr hy)
  obtain ⟨hopp, htravel, hperiod⟩ := n06_null_cut_displacement hβ hlift htime hτp hτn hdiff
  refine ⟨τp, hτp, htravel, hperiod, fun r hr θ => ⟨hplus' r hr θ, ?_⟩⟩
  simpa only [hopp, neg_mul, sub_eq_add_neg] using hminus' r hr θ

/-- The original forward cut necessarily bisects the physical optical
travel, and its Tricomi time is exactly half the original return angle. -/
theorem n06_reference_cut_travel
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (h : NonlinearPropertiesThrough04 D T S C R L K base loss ε) (m : ℕ) :
    opticalTravel D.w (C.left m) (K.physicalRight (K.cutPair m).1) =
        n05TricomiTime (K.cutRadius m) ∧
      opticalTravel D.w (K.physicalRight (K.cutPair m).1) (C.right m) =
        n05TricomiTime (K.cutRadius m) ∧
      radialTravel D (C.left m) (C.right m) = 2 * n05TricomiTime (K.cutRadius m) := by
  have h01 := h.1.1.1
  have hg : controlGeometryConditions D S C := h01.2.2.2.1
  have hpieces := h.2.2.2.2.1.1.referenceBounds
  have hcuts := h.2.2.2.2.1.2.1.1.1
  obtain ⟨hnegL, hnegR, hl, hr, hmeet, hy, _, _, _, _⟩ := hcuts m
  let c := K.physicalRight (K.cutPair m).1
  let t := n05TricomiTime (K.cutRadius m)
  have ht : 0 < t := mul_pos (mul_pos (by norm_num) hy) (Real.sqrt_pos.mpr hy)
  have hlc : C.left m < c := by
    rw [← hl]
    exact (hpieces (K.cutPair m).1).1
  have hcr : c < C.right m := by
    dsimp only [c]
    rw [hmeet, ← hr]
    exact (hpieces (K.cutPair m).2).1
  have hrootL : C.left m ∈ Icc (K.physicalLeft (K.cutPair m).1)
      (K.physicalRight (K.cutPair m).1) := by
    rw [hl]
    exact ⟨le_rfl, hlc.le⟩
  have hrootR : C.right m ∈ Icc (K.physicalLeft (K.cutPair m).2)
      (K.physicalRight (K.cutPair m).2) := by
    rw [hr]
    exact ⟨by simpa only [c, hmeet] using hcr.le, le_rfl⟩
  have hcutL : c ∈ Icc (K.physicalLeft (K.cutPair m).1)
      (K.physicalRight (K.cutPair m).1) := ⟨(hpieces (K.cutPair m).1).1.le, le_rfl⟩
  have hcutR : c ∈ Icc (K.physicalLeft (K.cutPair m).2)
      (K.physicalRight (K.cutPair m).2) := by
    dsimp only [c]
    rw [hmeet]
    exact ⟨le_rfl, (hpieces (K.cutPair m).2).1.le⟩
  obtain ⟨τL, hτL, htravelL, _⟩ := n06_reference_null_root_cut hT hS h hnegL
    (n06_cutPiece_closed_subset h m (Or.inl rfl)) hrootL hcutL (hg.2.1 m).1 hy
    (fun θ => n05_cut_reference_image hT hS h m (Or.inl rfl) θ)
  obtain ⟨τR, hτR, htravelR, _⟩ := n06_reference_null_root_cut hT hS h hnegR
    (n06_cutPiece_closed_subset h m (Or.inr rfl)) hrootR hcutR (hg.2.1 m).2.1 hy
    (fun θ => n05_cut_reference_image hT hS h m (Or.inr rfl) θ)
  have hnonnegL : 0 ≤ opticalTravel D.w (C.left m) c :=
    intervalIntegral.integral_nonneg_of_forall hlc.le (fun _ => Real.sqrt_nonneg _)
  have hnonnegR : 0 ≤ opticalTravel D.w c (C.right m) :=
    intervalIntegral.integral_nonneg_of_forall hcr.le (fun _ => Real.sqrt_nonneg _)
  have hleft : opticalTravel D.w (C.left m) c = t := by
    rcases sq_eq_one_iff.mp hτL with hτ | hτ
    · simpa only [hτ, one_mul] using htravelL
    · rw [hτ, neg_one_mul] at htravelL
      change -opticalTravel D.w (C.left m) c = t at htravelL
      linarith only [htravelL, hnonnegL, ht]
  have hright : opticalTravel D.w c (C.right m) = t := by
    have hswap : opticalTravel D.w (C.right m) c =
        -opticalTravel D.w c (C.right m) := intervalIntegral.integral_symm _ _
    rw [hswap] at htravelR
    rcases sq_eq_one_iff.mp hτR with hτ | hτ
    · rw [hτ, one_mul] at htravelR
      change -opticalTravel D.w c (C.right m) = t at htravelR
      linarith only [htravelR, hnonnegR, ht]
    · simpa only [hτ, neg_one_mul, neg_neg] using htravelR
  refine ⟨hleft, hright, ?_⟩
  obtain ⟨B, hB⟩ := h01.1.1
  have hv : ContinuousOn (opticalSpeed D.w) (Icc (C.left m) (C.right m)) :=
    continuousOn_opticalSpeed_of_profile hB.1.2.2.1.1
      (hB.1.1.trans (hg.1 m).1) (fun r hri =>
        hB.1.2.2.2.2.1 r ⟨(hg.1 m).1.trans_le hri.1,
          hri.2.trans_lt (hg.1 m).2.2⟩)
  have hil : IntervalIntegrable (opticalSpeed D.w) volume (C.left m) c :=
    (hv.mono (Icc_subset_Icc le_rfl hcr.le)).intervalIntegrable_of_Icc hlc.le
  have hir : IntervalIntegrable (opticalSpeed D.w) volume c (C.right m) :=
    (hv.mono (Icc_subset_Icc hlc.le le_rfl)).intervalIntegrable_of_Icc hcr.le
  change (∫ x in C.left m..C.right m, opticalSpeed D.w x) = 2 * t
  rw [← intervalIntegral.integral_add_adjacent_intervals hil hir]
  change opticalTravel D.w (C.left m) c + opticalTravel D.w c (C.right m) = 2 * t
  rw [hleft, hright]
  ring

end ContinuousFlexibility.Statements
