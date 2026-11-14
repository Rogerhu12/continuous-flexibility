module

public import ContinuousFlexibility.Analysis.N06RootNormalizedHeights
public import ContinuousFlexibility.Analysis.N06RootNormalizedFormula

/-!
# The actual normalized physical root packet

All entries below are functions of the original height pair. The weighted
maps identify them globally, including their smooth extensions. Their
finite spatial jets are bounded in the original state grading at n+7.
Changing only q changes just the last constant entry of this packet.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set
open scoped ContDiff

def n06RootNormalizedPacket (w a c b e : PolarPoint → ℝ) (q : ℝ)
    (p : PolarPoint) : N06RootNormalizedCoordinates :=
  ![w p, a p, c p, b p, e p, q]

theorem n06RootNormalizedPacket_contDiff
    {w a c b e : PolarPoint → ℝ}
    (hw : ContDiff ℝ ∞ w) (ha : ContDiff ℝ ∞ a) (hc : ContDiff ℝ ∞ c)
    (hb : ContDiff ℝ ∞ b) (he : ContDiff ℝ ∞ e) (q : ℝ) :
    ContDiff ℝ ∞ (n06RootNormalizedPacket w a c b e q) := by
  apply contDiff_pi.mpr
  intro i
  fin_cases i <;> first | exact hw | exact ha | exact hc | exact hb | exact he | exact contDiff_const

theorem n06RootNormalizedPacket_parameter_affine
    (w a c b e : PolarPoint → ℝ) (q t : ℝ) (p : PolarPoint) :
    n06RootNormalizedPacket w a c b e (t * q) p =
      n06RootNormalizedPacket w a c b e 0 p +
        t • (n06RootNormalizedPacket w a c b e q p -
          n06RootNormalizedPacket w a c b e 0 p) := by
  funext i
  fin_cases i <;>
    simp only [n06RootNormalizedPacket, Pi.add_apply, Pi.sub_apply, Pi.smul_apply,
      Matrix.cons_val_zero', Matrix.cons_val_succ', smul_eq_mul] <;> ring

theorem n06RootNormalizedPacket_spatial_bound
    {w a c b e : PolarPoint → ℝ}
    (hw : ContDiff ℝ ∞ w) (ha : ContDiff ℝ ∞ a) (hc : ContDiff ℝ ∞ c)
    (hb : ContDiff ℝ ∞ b) (he : ContDiff ℝ ∞ e)
    (q : ℝ) (n : ℕ) (p : PolarPoint) {M : ℝ} (hM : 0 ≤ M)
    (hwB : ‖iteratedFDeriv ℝ n w p‖ ≤ M)
    (haB : ‖iteratedFDeriv ℝ n a p‖ ≤ M)
    (hcB : ‖iteratedFDeriv ℝ n c p‖ ≤ M)
    (hbB : ‖iteratedFDeriv ℝ n b p‖ ≤ M)
    (heB : ‖iteratedFDeriv ℝ n e p‖ ≤ M) (hq : |q| ≤ M) :
    ‖iteratedFDeriv ℝ n (n06RootNormalizedPacket w a c b e q) p‖ ≤ M := by
  apply n06_norm_iteratedFDeriv_pi_le
    (n06RootNormalizedPacket_contDiff hw ha hc hb he q).contDiffAt n hM
  intro i
  fin_cases i
  · exact hwB
  · exact haB
  · exact hcB
  · exact hbB
  · exact heB
  · change ‖iteratedFDeriv ℝ n (fun _ : PolarPoint => q) p‖ ≤ M
    cases n with
    | zero => simpa only [norm_iteratedFDeriv_zero, Real.norm_eq_abs] using hq
    | succ n => simpa only [iteratedFDeriv_succ_const, Pi.zero_apply, norm_zero] using hM

theorem n06RootNormalizedPacket_parameter_jet_difference
    {w a c b e : PolarPoint → ℝ}
    (hw : ContDiff ℝ ∞ w) (ha : ContDiff ℝ ∞ a) (hc : ContDiff ℝ ∞ c)
    (hb : ContDiff ℝ ∞ b) (he : ContDiff ℝ ∞ e) (q : ℝ) (n : ℕ) (p : PolarPoint) :
    ‖iteratedFDeriv ℝ n (n06RootNormalizedPacket w a c b e q) p -
      iteratedFDeriv ℝ n (n06RootNormalizedPacket w a c b e 0) p‖ ≤ |q| := by
  have hu := n06RootNormalizedPacket_contDiff hw ha hc hb he q
  have hv := n06RootNormalizedPacket_contDiff hw ha hc hb he 0
  have hd : n06RootNormalizedPacket w a c b e q - n06RootNormalizedPacket w a c b e 0 =
      fun _ => (![0, 0, 0, 0, 0, q] : N06RootNormalizedCoordinates) := by
    funext x i
    fin_cases i <;> simp only [Pi.sub_apply, n06RootNormalizedPacket,
      Matrix.cons_val_zero', Matrix.cons_val_succ', sub_self, sub_zero]
  rw [← iteratedFDeriv_sub_apply (hu.contDiffAt.of_le (by simp : (n : ℕ∞ω) ≤ ∞))
    (hv.contDiffAt.of_le (by simp : (n : ℕ∞ω) ≤ ∞)), hd]
  cases n with
  | zero =>
    rw [norm_iteratedFDeriv_zero]
    apply (pi_norm_le_iff_of_nonneg (abs_nonneg q)).mpr
    intro i
    fin_cases i <;> simp only [Matrix.cons_val_zero', Matrix.cons_val_succ', norm_zero,
      Real.norm_eq_abs] <;> first | exact abs_nonneg q | exact le_rfl
  | succ n =>
    simpa only [iteratedFDeriv_succ_const, Pi.zero_apply, norm_zero] using abs_nonneg q

end ContinuousFlexibility.Analysis

namespace ContinuousFlexibility.Statements

open Set
open ContinuousFlexibility.Analysis
open scoped ContDiff BigOperators

set_option backward.isDefEq.respectTransparency false

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}

def n06ActualRootNormalizedCoordinates (D : ReferenceData) (S : PhysicalSpacesData)
    (z : AnnularState S × ℝ) (p : PolarPoint) : N06RootNormalizedCoordinates :=
  n06NormalizeRootCoordinates (n06ActualNuJetCoordinates D S z p)

def n06RootNormalizedHeightFields (D : ReferenceData) (S : PhysicalSpacesData)
    (u : ScalarCommonHeight S) : Fin 4 → PolarPoint → ℝ :=
  ![fun p => (D.w p.1)⁻¹ * radialPartial (scalarCommonHeightDecode S u) p,
    heightAngular (scalarCommonHeightDecode S u),
    fun p => (D.w p.1)⁻¹ * radialPartial (heightAngular (scalarCommonHeightDecode S u)) p,
    fun p => (D.w p.1)⁻¹ * angularPartial (heightAngular (scalarCommonHeightDecode S u)) p]

theorem n06_rootNormalizedHeightFields_contDiff
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T)
    (hS : IsPhysicalSpaces D T S) (u : ScalarCommonHeight S) (i : Fin 4) :
    ContDiff ℝ ∞ (n06RootNormalizedHeightFields D S u i) := by
  have hdecode (v : ScalarHeightSpace S) : ContDiff ℝ ∞ ((S.height scalarBeta).decode v) :=
    (scalarHeight_decode_contDiff_and_flatJets hT hS v).1
  have hangle (v : ScalarHeightSpace S) :
      ContDiff ℝ ∞ (angularPartial ((S.height scalarBeta).decode v)) :=
    ((hdecode v).fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const
  fin_cases i
  · change ContDiff ℝ ∞ (fun p => (D.w p.1)⁻¹ * radialPartial (scalarCommonHeightDecode S u) p)
    rw [← funext (n06_decode_rootNormalizedRadial hD hT hS u)]
    exact hdecode _
  · change ContDiff ℝ ∞ (heightAngular (scalarCommonHeightDecode S u))
    rw [← n06_angularPartial_decode_rootAngularPrimitive hD hT hS u]
    exact hangle _
  · change ContDiff ℝ ∞ (fun p =>
      (D.w p.1)⁻¹ * radialPartial (heightAngular (scalarCommonHeightDecode S u)) p)
    rw [← n06_angularPartial_decode_rootNormalizedMixedPrimitive hD hT hS u]
    exact hangle _
  · change ContDiff ℝ ∞ (fun p =>
      (D.w p.1)⁻¹ * angularPartial (heightAngular (scalarCommonHeightDecode S u)) p)
    rw [← funext (n06_decode_rootNormalizedAngularSecond hD hT hS u)]
    exact hdecode _

theorem n06_actualRootNormalizedCoordinates_eq_packet
    (D : ReferenceData) (S : PhysicalSpacesData) (z : AnnularState S × ℝ) :
    n06ActualRootNormalizedCoordinates D S z = n06RootNormalizedPacket
      (fun p => D.w p.1) (n06RootNormalizedHeightFields D S z.1.1 0)
      (n06RootNormalizedHeightFields D S z.1.1 1)
      (n06RootNormalizedHeightFields D S z.1.1 2)
      (n06RootNormalizedHeightFields D S z.1.1 3) z.2 := rfl

theorem n06_actualRootNormalizedCoordinates_contDiff
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T)
    (hS : IsPhysicalSpaces D T S) (z : AnnularState S × ℝ) :
    ContDiff ℝ ∞ (n06ActualRootNormalizedCoordinates D S z) := by
  rw [n06_actualRootNormalizedCoordinates_eq_packet]
  exact n06RootNormalizedPacket_contDiff
    (hD.choose_spec.1.2.2.1.1.comp contDiff_fst)
    (n06_rootNormalizedHeightFields_contDiff hD hT hS z.1.1 0)
    (n06_rootNormalizedHeightFields_contDiff hD hT hS z.1.1 1)
    (n06_rootNormalizedHeightFields_contDiff hD hT hS z.1.1 2)
    (n06_rootNormalizedHeightFields_contDiff hD hT hS z.1.1 3) z.2

private theorem n06_root_tame_height_spatial_bound
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T)
    (hS : IsPhysicalSpaces D T S)
    (L : ScalarCommonHeight S →L[ℝ] ScalarHeightSpace S)
    (hL : IsTameLinear (scalarCommonHeightGrading S) (scalarHeightGrading S)
      L.toLinearMap 4 0) (n : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (u : ScalarCommonHeight S) k, k ≤ n → ∀ p ∈ annularOpen D,
      ‖iteratedFDeriv ℝ k ((S.height scalarBeta).decode (L u)) p‖ ≤
          C * scalarCommonHeightGrading S (n + 7) u ∧
        ‖iteratedFDeriv ℝ k (angularPartial ((S.height scalarBeta).decode (L u))) p‖ ≤
          C * scalarCommonHeightGrading S (n + 7) u := by
  obtain ⟨J, hJ, hj⟩ := n06_root_decoded_and_angular_spatial_bound hD hT hS n
  obtain ⟨A, ha⟩ := hL (n + 3) (Nat.zero_le _)
  refine ⟨J * A, mul_nonneg hJ A.coe_nonneg, ?_⟩
  intro u k hk p hp
  have hgrade : scalarHeightGrading S (n + 3) (L u) ≤
      (A : ℝ) * scalarCommonHeightGrading S (n + 7) u := ha u
  have hb := hj (L u) k hk p hp
  have hscale := (mul_le_mul_of_nonneg_left hgrade hJ).trans_eq (mul_assoc _ _ _).symm
  exact ⟨hb.1.trans hscale, hb.2.trans hscale⟩

def N06RootHeightSpatialBound (D : ReferenceData) (S : PhysicalSpacesData)
    (n : ℕ) (C : ℝ) : Prop :=
  ∀ (u : ScalarCommonHeight S) (i : Fin 4) k, k ≤ n → ∀ p ∈ annularOpen D,
    ‖iteratedFDeriv ℝ k (n06RootNormalizedHeightFields D S u i) p‖ ≤
      C * scalarCommonHeightGrading S (n + 7) u

theorem n06_rootNormalizedHeightFields_spatial_bound
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T)
    (hS : IsPhysicalSpaces D T S) (n : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ N06RootHeightSpatialBound D S n C := by
  have hm := weighted_scalarCommonHeightGrading_monotone S
  obtain ⟨A, hA, ha⟩ := n06_root_tame_height_spatial_bound hD hT hS
    (n06RootNormalizedRadialCLM hD hT hS)
    ((n06RootNormalizedRadialCLM_isTame hD hT hS).weaken hm (by norm_num) le_rfl) n
  obtain ⟨B, hB, hb⟩ := n06_root_tame_height_spatial_bound hD hT hS
    (n06RootAngularPrimitiveCLM hD hT hS)
    ((n06RootAngularPrimitiveCLM_isTame hD hT hS).weaken hm (by norm_num) le_rfl) n
  obtain ⟨C, hC, hc⟩ := n06_root_tame_height_spatial_bound hD hT hS
    (n06RootNormalizedMixedPrimitiveCLM hD hT hS)
    (n06RootNormalizedMixedPrimitiveCLM_isTame hD hT hS) n
  obtain ⟨E, hE, he⟩ := n06_root_tame_height_spatial_bound hD hT hS
    (n06RootNormalizedAngularSecondCLM hD hT hS)
    (n06RootNormalizedAngularSecondCLM_isTame hD hT hS) n
  refine ⟨A + B + C + E, by positivity, ?_⟩
  intro u i k hk p hp
  have hP : 0 ≤ scalarCommonHeightGrading S (n + 7) u := apply_nonneg _ _
  fin_cases i
  · change ‖iteratedFDeriv ℝ k (fun q =>
      (D.w q.1)⁻¹ * radialPartial (scalarCommonHeightDecode S u) q) p‖ ≤ _
    rw [← funext (n06_decode_rootNormalizedRadial hD hT hS u)]
    exact (ha u k hk p hp).1.trans (mul_le_mul_of_nonneg_right (by linarith) hP)
  · change ‖iteratedFDeriv ℝ k (heightAngular (scalarCommonHeightDecode S u)) p‖ ≤ _
    rw [← n06_angularPartial_decode_rootAngularPrimitive hD hT hS u]
    exact (hb u k hk p hp).2.trans (mul_le_mul_of_nonneg_right (by linarith) hP)
  · change ‖iteratedFDeriv ℝ k (fun q =>
      (D.w q.1)⁻¹ * radialPartial (heightAngular (scalarCommonHeightDecode S u)) q) p‖ ≤ _
    rw [← n06_angularPartial_decode_rootNormalizedMixedPrimitive hD hT hS u]
    exact (hc u k hk p hp).2.trans (mul_le_mul_of_nonneg_right (by linarith) hP)
  · change ‖iteratedFDeriv ℝ k (fun q =>
      (D.w q.1)⁻¹ * angularPartial (heightAngular (scalarCommonHeightDecode S u)) q) p‖ ≤ _
    rw [← funext (n06_decode_rootNormalizedAngularSecond hD hT hS u)]
    exact (he u k hk p hp).1.trans (mul_le_mul_of_nonneg_right (by linarith) hP)

theorem n06_root_commonHeightGrading_le_state (S : PhysicalSpacesData) (s : ℕ)
    (x : AnnularState S) : scalarCommonHeightGrading S s x.1 ≤ stateGrading S s x := by
  change (S.height (3 / 4 : ℝ)).grading s x.1.1 + ‖x.1.2‖ ≤
    (S.height (3 / 4 : ℝ)).grading s x.1.1 + ‖x.1.2‖ +
      (‖x.2.1‖ + ((S.circle (3 / 4 : ℝ)).grading s x.2.2.1 +
        (S.circle (3 / 4 : ℝ)).grading s x.2.2.2))
  exact le_add_of_nonneg_right (add_nonneg (norm_nonneg _)
    (add_nonneg (apply_nonneg _ _) (apply_nonneg _ _)))

def N06RootNormalizedSpatialBound (D : ReferenceData) (S : PhysicalSpacesData)
    (n : ℕ) (R M : ℝ) : Prop :=
  ∀ z : AnnularState S × ℝ, stateGrading S (n + 7) z.1 ≤ R → |z.2| ≤ 1 →
    ∀ k, k ≤ n → ∀ p ∈ annularOpen D,
      ‖iteratedFDeriv ℝ k (n06ActualRootNormalizedCoordinates D S z) p‖ ≤ M

private theorem n06_root_packet_bound_of_fields
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T)
    (hS : IsPhysicalSpaces D T S) (n : ℕ) {R C B : ℝ}
    (hR : 0 ≤ R) (hC : 0 ≤ C) (hB : 0 ≤ B)
    (hc : N06RootHeightSpatialBound D S n C)
    (hb : ∀ k, k ≤ n → ∀ p : PolarPoint, p.1 ∈ Icc D.a D.b →
      ‖iteratedFDeriv ℝ k (fun q : PolarPoint => D.w q.1) p‖ ≤ B) :
    N06RootNormalizedSpatialBound D S n R (B + C * R + 1) := by
  let M : ℝ := B + C * R + 1
  have hCR : 0 ≤ C * R := mul_nonneg hC hR
  have hM : 0 ≤ M := by dsimp [M]; positivity
  intro z hz hq k hk p hp
  have hcommon := (n06_root_commonHeightGrading_le_state S (n + 7) z.1).trans hz
  have hfields (i : Fin 4) :
      ‖iteratedFDeriv ℝ k (n06RootNormalizedHeightFields D S z.1.1 i) p‖ ≤ M :=
    (hc z.1.1 i k hk p hp).trans
      ((mul_le_mul_of_nonneg_left hcommon hC).trans (by dsimp [M]; linarith))
  have hradial : ‖iteratedFDeriv ℝ k (fun q : PolarPoint => D.w q.1) p‖ ≤ M :=
    (hb k hk p ⟨hp.1.1.le, hp.1.2.le⟩).trans (by dsimp [M]; linarith)
  have hMone : 1 ≤ M := by dsimp [M]; linarith
  rw [n06_actualRootNormalizedCoordinates_eq_packet]
  exact n06RootNormalizedPacket_spatial_bound
    (hD.choose_spec.1.2.2.1.1.comp contDiff_fst)
    (n06_rootNormalizedHeightFields_contDiff hD hT hS z.1.1 0)
    (n06_rootNormalizedHeightFields_contDiff hD hT hS z.1.1 1)
    (n06_rootNormalizedHeightFields_contDiff hD hT hS z.1.1 2)
    (n06_rootNormalizedHeightFields_contDiff hD hT hS z.1.1 3) z.2 k p hM
    hradial (hfields 0) (hfields 1) (hfields 2) (hfields 3) (hq.trans hMone)

theorem n06_actualRootNormalizedCoordinates_spatial_bound
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T)
    (hS : IsPhysicalSpaces D T S) (n : ℕ) {R : ℝ} (hR : 0 ≤ R) :
    ∃ M : ℝ, 0 ≤ M ∧ N06RootNormalizedSpatialBound D S n R M := by
  obtain ⟨C, hC, hc⟩ := n06_rootNormalizedHeightFields_spatial_bound
    (D := D) (T := T) (S := S) hD hT hS n
  obtain ⟨B, hB, hb⟩ := n06_radialLift_finite_frechet_bound (b := D.b)
    hD.choose_spec.1.1 hD.choose_spec.1.2.2.1.1.contDiffOn n
  exact ⟨B + C * R + 1, by positivity,
    n06_root_packet_bound_of_fields hD hT hS n hR hC hB hc hb⟩

theorem n06_actualRootNormalizedCoordinates_parameter_jet_difference
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T)
    (hS : IsPhysicalSpaces D T S) (z : AnnularState S × ℝ) (n : ℕ) (p : PolarPoint) :
    ‖iteratedFDeriv ℝ n (n06ActualRootNormalizedCoordinates D S z) p -
      iteratedFDeriv ℝ n (n06ActualRootNormalizedCoordinates D S (z.1, 0)) p‖ ≤ |z.2| := by
  rw [n06_actualRootNormalizedCoordinates_eq_packet,
    n06_actualRootNormalizedCoordinates_eq_packet]
  exact n06RootNormalizedPacket_parameter_jet_difference
    (hD.choose_spec.1.2.2.1.1.comp contDiff_fst)
    (n06_rootNormalizedHeightFields_contDiff hD hT hS z.1.1 0)
    (n06_rootNormalizedHeightFields_contDiff hD hT hS z.1.1 1)
    (n06_rootNormalizedHeightFields_contDiff hD hT hS z.1.1 2)
    (n06_rootNormalizedHeightFields_contDiff hD hT hS z.1.1 3) z.2 n p

end ContinuousFlexibility.Statements
