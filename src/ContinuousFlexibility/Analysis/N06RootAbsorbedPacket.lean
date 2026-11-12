import ContinuousFlexibility.Analysis.N06RootWeightedHeights

/-!
# Absorbing q into the actual decaying root inputs

The finite root formula is unchanged when q is put into each of its four
height entries and the last coordinate is set to one. The resulting
packet difference from q=0 retains the original material decay, rather
than treating q itself as an unweighted coordinate difference.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set
open scoped ContDiff

def n06AbsorbRootParameter (v : N06RootNormalizedCoordinates) : N06RootNormalizedCoordinates :=
  ![v 0, v 5 * v 1, v 5 * v 2, v 5 * v 3, v 5 * v 4, 1]

theorem n06_absorbRoot_denominators (v : N06RootNormalizedCoordinates) :
    n06RootNormalizedQ (n06AbsorbRootParameter v) = n06RootNormalizedQ v ∧
      n06RootNormalizedDiscriminant (n06AbsorbRootParameter v) =
        n06RootNormalizedDiscriminant v := by
  constructor
  · change 1 + 1 * (v 5 * v 1 + (1 + v 0 ^ 2) * (v 5 * v 4)) =
      1 + v 5 * (v 1 + (1 + v 0 ^ 2) * v 4)
    ring
  · change (1 + v 0 ^ 2) * (1 - (1 * (v 5 * v 2)) ^ 2) -
      (v 0 * (1 + 1 * (v 5 * v 1))) ^ 2 =
        (1 + v 0 ^ 2) * (1 - (v 5 * v 2) ^ 2) - (v 0 * (1 + v 5 * v 1)) ^ 2
    simp only [one_mul]

theorem n06_absorbRoot_fields (v : N06RootNormalizedCoordinates) :
    n06RootNormalizedFields (n06AbsorbRootParameter v) = n06RootNormalizedFields v := by
  obtain ⟨hQ, hD⟩ := n06_absorbRoot_denominators v
  apply Prod.ext
  · change -(1 + v 0 ^ 2) * 1 * (v 5 * v 3) /
      n06RootNormalizedQ (n06AbsorbRootParameter v) =
        -(1 + v 0 ^ 2) * v 5 * v 3 / n06RootNormalizedQ v
    rw [hQ]
    ring
  · change Real.sqrt (n06RootNormalizedDiscriminant (n06AbsorbRootParameter v)) /
      n06RootNormalizedQ (n06AbsorbRootParameter v) = _
    rw [hD, hQ]
    rfl

def n06RootAbsorbedPacket (w a c b e : PolarPoint → ℝ) (q : ℝ) :
    PolarPoint → N06RootNormalizedCoordinates :=
  n06RootNormalizedPacket w (fun p => q * a p) (fun p => q * c p)
    (fun p => q * b p) (fun p => q * e p) 1

theorem n06RootAbsorbedPacket_contDiff
    {w a c b e : PolarPoint → ℝ}
    (hw : ContDiff ℝ ∞ w) (ha : ContDiff ℝ ∞ a) (hc : ContDiff ℝ ∞ c)
    (hb : ContDiff ℝ ∞ b) (he : ContDiff ℝ ∞ e) (q : ℝ) :
    ContDiff ℝ ∞ (n06RootAbsorbedPacket w a c b e q) :=
  n06RootNormalizedPacket_contDiff hw (contDiff_const.mul ha)
    (contDiff_const.mul hc) (contDiff_const.mul hb) (contDiff_const.mul he) 1

theorem n06RootAbsorbedPacket_parameter_affine
    (w a c b e : PolarPoint → ℝ) (q t : ℝ) (p : PolarPoint) :
    n06RootAbsorbedPacket w a c b e (t * q) p =
      n06RootAbsorbedPacket w a c b e 0 p +
        t • (n06RootAbsorbedPacket w a c b e q p -
          n06RootAbsorbedPacket w a c b e 0 p) := by
  funext i
  fin_cases i <;>
    simp only [n06RootAbsorbedPacket, n06RootNormalizedPacket,
      Pi.add_apply, Pi.sub_apply, Pi.smul_apply,
      Matrix.cons_val_zero', Matrix.cons_val_succ', smul_eq_mul] <;> ring

theorem n06_norm_iteratedFDeriv_real_mul {f : PolarPoint → ℝ}
    (hf : ContDiff ℝ ∞ f) (q : ℝ) (n : ℕ) (p : PolarPoint) :
    ‖iteratedFDeriv ℝ n (fun x => q * f x) p‖ = |q| * ‖iteratedFDeriv ℝ n f p‖ := by
  have h := iteratedFDeriv_const_smul_apply' (a := q) (x := p)
    (hf.contDiffAt.of_le (by simp : (n : ℕ∞ω) ≤ ∞))
  exact (congrArg norm h).trans (norm_smul q _)

theorem n06RootAbsorbedPacket_jet_difference_bound
    {w a c b e : PolarPoint → ℝ}
    (hw : ContDiff ℝ ∞ w) (ha : ContDiff ℝ ∞ a) (hc : ContDiff ℝ ∞ c)
    (hb : ContDiff ℝ ∞ b) (he : ContDiff ℝ ∞ e)
    (q : ℝ) (n : ℕ) (p : PolarPoint) {A : ℝ} (hA : 0 ≤ A)
    (haB : ‖iteratedFDeriv ℝ n a p‖ ≤ A)
    (hcB : ‖iteratedFDeriv ℝ n c p‖ ≤ A)
    (hbB : ‖iteratedFDeriv ℝ n b p‖ ≤ A)
    (heB : ‖iteratedFDeriv ℝ n e p‖ ≤ A) :
    ‖iteratedFDeriv ℝ n (n06RootAbsorbedPacket w a c b e q) p -
      iteratedFDeriv ℝ n (n06RootAbsorbedPacket w a c b e 0) p‖ ≤ |q| * A := by
  have hu := n06RootAbsorbedPacket_contDiff hw ha hc hb he q
  have hv := n06RootAbsorbedPacket_contDiff hw ha hc hb he 0
  have hd : n06RootAbsorbedPacket w a c b e q - n06RootAbsorbedPacket w a c b e 0 =
      n06RootNormalizedPacket (fun _ => 0) (fun x => q * a x) (fun x => q * c x)
        (fun x => q * b x) (fun x => q * e x) 0 := by
    funext x i
    fin_cases i <;> simp only [Pi.sub_apply, n06RootAbsorbedPacket, n06RootNormalizedPacket,
      Matrix.cons_val_zero', Matrix.cons_val_succ', sub_self, sub_zero, zero_mul]
  rw [← iteratedFDeriv_sub_apply (x := p)
    (hu.contDiffAt.of_le (by simp : (n : ℕ∞ω) ≤ ∞))
    (hv.contDiffAt.of_le (by simp : (n : ℕ∞ω) ≤ ∞)), hd]
  have hM : 0 ≤ |q| * A := mul_nonneg (abs_nonneg _) hA
  have hzero : ‖iteratedFDeriv ℝ n (fun _ : PolarPoint => (0 : ℝ)) p‖ ≤ |q| * A := by
    cases n with
    | zero => simpa only [norm_iteratedFDeriv_zero, norm_zero] using hM
    | succ n => simpa only [iteratedFDeriv_succ_const, Pi.zero_apply, norm_zero] using hM
  have hmul {f : PolarPoint → ℝ} (hf : ContDiff ℝ ∞ f)
      (hb : ‖iteratedFDeriv ℝ n f p‖ ≤ A) :
      ‖iteratedFDeriv ℝ n (fun x => q * f x) p‖ ≤ |q| * A :=
    (n06_norm_iteratedFDeriv_real_mul hf q n p).trans_le
      (mul_le_mul_of_nonneg_left hb (abs_nonneg _))
  exact n06RootNormalizedPacket_spatial_bound contDiff_const
    (contDiff_const.mul ha) (contDiff_const.mul hc) (contDiff_const.mul hb)
    (contDiff_const.mul he) 0 n p hM hzero
    (hmul ha haB) (hmul hc hcB) (hmul hb hbB) (hmul he heB)
    (by simpa only [abs_zero] using hM)

theorem n06RootAbsorbedPacket_spatial_bound
    {w a c b e : PolarPoint → ℝ}
    (hw : ContDiff ℝ ∞ w) (ha : ContDiff ℝ ∞ a) (hc : ContDiff ℝ ∞ c)
    (hb : ContDiff ℝ ∞ b) (he : ContDiff ℝ ∞ e)
    (q : ℝ) (n : ℕ) (p : PolarPoint) {M : ℝ} (hM : 1 ≤ M) (hq : |q| ≤ 1)
    (hwB : ‖iteratedFDeriv ℝ n w p‖ ≤ M)
    (haB : ‖iteratedFDeriv ℝ n a p‖ ≤ M)
    (hcB : ‖iteratedFDeriv ℝ n c p‖ ≤ M)
    (hbB : ‖iteratedFDeriv ℝ n b p‖ ≤ M)
    (heB : ‖iteratedFDeriv ℝ n e p‖ ≤ M) :
    ‖iteratedFDeriv ℝ n (n06RootAbsorbedPacket w a c b e q) p‖ ≤ M := by
  have hmul {f : PolarPoint → ℝ} (hf : ContDiff ℝ ∞ f)
      (hb : ‖iteratedFDeriv ℝ n f p‖ ≤ M) :
      ‖iteratedFDeriv ℝ n (fun x => q * f x) p‖ ≤ M :=
    (n06_norm_iteratedFDeriv_real_mul hf q n p).trans_le
      ((mul_le_mul_of_nonneg_left hb (abs_nonneg _)).trans
        ((mul_le_mul_of_nonneg_right hq (zero_le_one.trans hM)).trans_eq (one_mul _)))
  exact n06RootNormalizedPacket_spatial_bound hw (contDiff_const.mul ha)
    (contDiff_const.mul hc) (contDiff_const.mul hb) (contDiff_const.mul he) 1 n p
    (zero_le_one.trans hM) hwB (hmul ha haB) (hmul hc hcB) (hmul hb hbB) (hmul he heB)
    (by simpa only [abs_one] using hM)

end ContinuousFlexibility.Analysis

namespace ContinuousFlexibility.Statements

open Set
open ContinuousFlexibility.Analysis
open scoped ContDiff

set_option backward.isDefEq.respectTransparency false

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}

def n06ActualRootAbsorbedCoordinates (D : ReferenceData) (S : PhysicalSpacesData)
    (z : AnnularState S × ℝ) (p : PolarPoint) : N06RootNormalizedCoordinates :=
  n06AbsorbRootParameter (n06ActualRootNormalizedCoordinates D S z p)

theorem n06_actualRootAbsorbedCoordinates_eq_packet
    (D : ReferenceData) (S : PhysicalSpacesData) (z : AnnularState S × ℝ) :
    n06ActualRootAbsorbedCoordinates D S z = n06RootAbsorbedPacket
      (fun p => D.w p.1) (n06RootNormalizedHeightFields D S z.1.1 0)
      (n06RootNormalizedHeightFields D S z.1.1 1)
      (n06RootNormalizedHeightFields D S z.1.1 2)
      (n06RootNormalizedHeightFields D S z.1.1 3) z.2 := rfl

theorem n06_actualRootAbsorbedCoordinates_contDiff
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T)
    (hS : IsPhysicalSpaces D T S) (z : AnnularState S × ℝ) :
    ContDiff ℝ ∞ (n06ActualRootAbsorbedCoordinates D S z) := by
  rw [n06_actualRootAbsorbedCoordinates_eq_packet]
  exact n06RootAbsorbedPacket_contDiff
    (hD.choose_spec.1.2.2.1.1.comp contDiff_fst)
    (n06_rootNormalizedHeightFields_contDiff hD hT hS z.1.1 0)
    (n06_rootNormalizedHeightFields_contDiff hD hT hS z.1.1 1)
    (n06_rootNormalizedHeightFields_contDiff hD hT hS z.1.1 2)
    (n06_rootNormalizedHeightFields_contDiff hD hT hS z.1.1 3) z.2

def N06RootAbsorbedWeightedDifferenceBound (D : ReferenceData) (T : MaterialData)
    (S : PhysicalSpacesData) (n : ℕ) (C : ℝ) : Prop :=
  ∀ z : AnnularState S × ℝ, ∀ k, k ≤ n → ∀ p ∈ annularOpen D,
    ‖iteratedFDeriv ℝ k (n06ActualRootAbsorbedCoordinates D S z) p -
      iteratedFDeriv ℝ k (n06ActualRootAbsorbedCoordinates D S (z.1, 0)) p‖ ≤
        C * n06RootJetWeight T p * stateGrading S (n + 7) z.1 * |z.2|

private theorem n06_root_absorbed_difference_of_fields
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T)
    (hS : IsPhysicalSpaces D T S) (n : ℕ) {C : ℝ} (hC : 0 ≤ C)
    (hc : N06RootHeightSpatialWeightedBound D T S n C) :
    N06RootAbsorbedWeightedDifferenceBound D T S n C := by
  intro z k hk p hp
  let A := C * n06RootJetWeight T p * scalarCommonHeightGrading S (n + 7) z.1.1
  have hA : 0 ≤ A := mul_nonneg (mul_nonneg hC (n06_rootJetWeight_nonneg hT hp))
    (apply_nonneg _ _)
  have h := n06RootAbsorbedPacket_jet_difference_bound
    (hD.choose_spec.1.2.2.1.1.comp contDiff_fst)
    (n06_rootNormalizedHeightFields_contDiff hD hT hS z.1.1 0)
    (n06_rootNormalizedHeightFields_contDiff hD hT hS z.1.1 1)
    (n06_rootNormalizedHeightFields_contDiff hD hT hS z.1.1 2)
    (n06_rootNormalizedHeightFields_contDiff hD hT hS z.1.1 3) z.2 k p hA
    (hc z.1.1 0 k hk p hp) (hc z.1.1 1 k hk p hp)
    (hc z.1.1 2 k hk p hp) (hc z.1.1 3 k hk p hp)
  have hgrade := n06_root_commonHeightGrading_le_state S (n + 7) z.1
  have hscale : A ≤ C * n06RootJetWeight T p * stateGrading S (n + 7) z.1 :=
    mul_le_mul_of_nonneg_left hgrade (mul_nonneg hC (n06_rootJetWeight_nonneg hT hp))
  change ‖iteratedFDeriv ℝ k (n06RootAbsorbedPacket
      (fun q => D.w q.1) (n06RootNormalizedHeightFields D S z.1.1 0)
      (n06RootNormalizedHeightFields D S z.1.1 1)
      (n06RootNormalizedHeightFields D S z.1.1 2)
      (n06RootNormalizedHeightFields D S z.1.1 3) z.2) p -
    iteratedFDeriv ℝ k (n06RootAbsorbedPacket
      (fun q => D.w q.1) (n06RootNormalizedHeightFields D S z.1.1 0)
      (n06RootNormalizedHeightFields D S z.1.1 1)
      (n06RootNormalizedHeightFields D S z.1.1 2)
      (n06RootNormalizedHeightFields D S z.1.1 3) 0) p‖ ≤ _
  exact h.trans ((mul_le_mul_of_nonneg_left hscale (abs_nonneg _)).trans_eq (mul_comm _ _))

theorem n06_actualRootAbsorbedCoordinates_weighted_difference_bound
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T)
    (hS : IsPhysicalSpaces D T S) (n : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ N06RootAbsorbedWeightedDifferenceBound D T S n C := by
  obtain ⟨C, hC, hc⟩ := n06_rootNormalizedHeightFields_spatial_weighted_bound
    (D := D) (T := T) (S := S) hD hT hS n
  exact ⟨C, hC, n06_root_absorbed_difference_of_fields hD hT hS n hC hc⟩

def N06RootAbsorbedSpatialBound (D : ReferenceData) (S : PhysicalSpacesData)
    (n : ℕ) (R M : ℝ) : Prop :=
  ∀ z : AnnularState S × ℝ, stateGrading S (n + 7) z.1 ≤ R → |z.2| ≤ 1 →
    ∀ k, k ≤ n → ∀ p ∈ annularOpen D,
      ‖iteratedFDeriv ℝ k (n06ActualRootAbsorbedCoordinates D S z) p‖ ≤ M

private theorem n06_root_absorbed_bound_of_fields
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T)
    (hS : IsPhysicalSpaces D T S) (n : ℕ) {R C B : ℝ}
    (hR : 0 ≤ R) (hC : 0 ≤ C) (hB : 0 ≤ B)
    (hc : N06RootHeightSpatialBound D S n C)
    (hb : ∀ k, k ≤ n → ∀ p : PolarPoint, p.1 ∈ Icc D.a D.b →
      ‖iteratedFDeriv ℝ k (fun q : PolarPoint => D.w q.1) p‖ ≤ B) :
    N06RootAbsorbedSpatialBound D S n R (B + C * R + 1) := by
  let M : ℝ := B + C * R + 1
  have hCR : 0 ≤ C * R := mul_nonneg hC hR
  have hM : 1 ≤ M := by dsimp [M]; linarith
  intro z hz hq k hk p hp
  have hcommon := (n06_root_commonHeightGrading_le_state S (n + 7) z.1).trans hz
  have hfields (i : Fin 4) :
      ‖iteratedFDeriv ℝ k (n06RootNormalizedHeightFields D S z.1.1 i) p‖ ≤ M :=
    (hc z.1.1 i k hk p hp).trans
      ((mul_le_mul_of_nonneg_left hcommon hC).trans (by dsimp [M]; linarith))
  have hradial : ‖iteratedFDeriv ℝ k (fun q : PolarPoint => D.w q.1) p‖ ≤ M :=
    (hb k hk p ⟨hp.1.1.le, hp.1.2.le⟩).trans (by dsimp [M]; linarith)
  rw [n06_actualRootAbsorbedCoordinates_eq_packet]
  exact n06RootAbsorbedPacket_spatial_bound
    (hD.choose_spec.1.2.2.1.1.comp contDiff_fst)
    (n06_rootNormalizedHeightFields_contDiff hD hT hS z.1.1 0)
    (n06_rootNormalizedHeightFields_contDiff hD hT hS z.1.1 1)
    (n06_rootNormalizedHeightFields_contDiff hD hT hS z.1.1 2)
    (n06_rootNormalizedHeightFields_contDiff hD hT hS z.1.1 3) z.2 k p hM hq
    hradial (hfields 0) (hfields 1) (hfields 2) (hfields 3)

theorem n06_actualRootAbsorbedCoordinates_spatial_bound
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T)
    (hS : IsPhysicalSpaces D T S) (n : ℕ) {R : ℝ} (hR : 0 ≤ R) :
    ∃ M : ℝ, 0 ≤ M ∧ N06RootAbsorbedSpatialBound D S n R M := by
  obtain ⟨C, hC, hc⟩ := n06_rootNormalizedHeightFields_spatial_bound
    (D := D) (T := T) (S := S) hD hT hS n
  obtain ⟨B, hB, hb⟩ := n06_radialLift_finite_frechet_bound (b := D.b)
    hD.choose_spec.1.1 hD.choose_spec.1.2.2.1.1.contDiffOn n
  exact ⟨B + C * R + 1, by positivity,
    n06_root_absorbed_bound_of_fields hD hT hS n hR hC hB hc hb⟩

end ContinuousFlexibility.Statements
