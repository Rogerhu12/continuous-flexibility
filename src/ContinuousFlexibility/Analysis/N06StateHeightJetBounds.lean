module

public import ContinuousFlexibility.Analysis.NeighborhoodStateBounds
public import ContinuousFlexibility.Analysis.SolveNormalization
public import ContinuousFlexibility.Analysis.SpacesCylinderEvenJets

/-!
# Uniform mixed jets of the original state height

The original state contains both a decoded height and its free coefficient
of S.chiLeft. Each fixed mixed derivative is bounded by the original state
grading at order a+b+2. Linearity gives the identical bound for differences
of two states. The cutoff in this argument remains the actual S.chiLeft.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Statements

open Set
open scoped ContDiff

set_option backward.isDefEq.respectTransparency false

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}

theorem n06_radialLift_mixedDerivative (f : ℝ → ℝ) (a b : ℕ) (p : PolarPoint) :
    mixedDerivative a b (fun q => f q.1) p =
      if b = 0 then iteratedDeriv a f p.1 else 0 := by
  by_cases hb : b = 0
  · simp [hb, mixedDerivative, iteratedDeriv_zero]
  · simp [mixedDerivative, iteratedDeriv_const, hb]

theorem n06_cutoff_mixedDerivative_bound
    (hS : IsPhysicalSpaces D T S) (a b : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ p ∈ annularOpen D,
      |mixedDerivative a b (fun q => S.chiLeft q.1) p| ≤ C := by
  have hc : Continuous (iteratedDeriv a S.chiLeft) :=
    hS.2.2.1.1.continuous_iteratedDeriv a (by simp)
  obtain ⟨C, hC⟩ := (isCompact_Icc : IsCompact (Icc D.a D.b)).bddAbove_image hc.abs.continuousOn
  refine ⟨max C 0, le_max_right _ _, ?_⟩
  intro p hp
  rw [n06_radialLift_mixedDerivative]
  split_ifs
  · exact (hC ⟨p.1, ⟨hp.1.1.le, hp.1.2.le⟩, rfl⟩).trans (le_max_left _ _)
  · simpa only [abs_zero] using le_max_right C 0

private def N06DecodedHeightJetBound (D : ReferenceData) (S : PhysicalSpacesData)
    (a b : ℕ) (C : ℝ) : Prop :=
  ∀ (v : ScalarHeightSpace S) (p : PolarPoint), p ∈ annularOpen D →
    |mixedDerivative a b ((S.height scalarBeta).decode v) p| ≤
      C * scalarHeightGrading S (a + b + 2) v

private theorem n06_decoded_mixedDerivative_bound
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T)
    (hS : IsPhysicalSpaces D T S) (a b : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ N06DecodedHeightJetBound D S a b C := by
  obtain ⟨J, hJ, hdecoded⟩ :=
    scalarMixedDerivative_le_reference_grading (D := D) (T := T) (S := S)
      hD hT hS a b (a + b + 2) le_rfl
  obtain ⟨M, hM, hprofile⟩ := referenceProfile_uniform_upper_bound (D := D) hD
  refine ⟨J * M, mul_nonneg hJ hM, ?_⟩
  intro v p hp
  calc
    _ ≤ J * scalarHeightGrading S (a + b + 2) v * D.w p.1 := hdecoded v p hp
    _ ≤ J * scalarHeightGrading S (a + b + 2) v * M :=
      mul_le_mul_of_nonneg_left (hprofile p.1 hp.1)
        (mul_nonneg hJ (apply_nonneg _ _))
    _ = _ := by ring

def N06StateHeightJetBound (D : ReferenceData) (S : PhysicalSpacesData)
    (a b : ℕ) (C : ℝ) : Prop :=
  ∀ (x : AnnularState S) (p : PolarPoint), p ∈ annularOpen D →
    |mixedDerivative a b (stateU S x) p| ≤ C * stateGrading S (a + b + 2) x

private theorem n06_abs_scalar_jet_le {c v P K : ℝ}
    (hc : |c| ≤ P) (hv : |v| ≤ K) : |c * v| ≤ K * P :=
  (abs_mul c v).trans_le
    ((mul_le_mul hc hv (abs_nonneg v) ((abs_nonneg c).trans hc)).trans_eq (mul_comm P K))

private theorem n06_abs_sum_jet_le {u v J K P : ℝ}
    (hu : |u| ≤ J * P) (hv : |v| ≤ K * P) : |u + v| ≤ (J + K) * P :=
  (abs_add_le u v).trans ((add_le_add hu hv).trans_eq (add_mul J K P).symm)

theorem n06_stateU_mixedDerivative_eq
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (x : AnnularState S) (a b : ℕ) (p : PolarPoint) :
    mixedDerivative a b (stateU S x) p =
      mixedDerivative a b ((S.height (3 / 4 : ℝ)).decode x.1.1) p +
        x.1.2 * mixedDerivative a b (fun q => S.chiLeft q.1) p := by
  have hdecodedSmooth := (physical_height_contDiff_and_flatJets
    (D := D) (T := T) (S := S) hT hS
      (by norm_num : (0 : ℝ) < 3 / 4) x.1.1).1
  change mixedDerivative a b (fun q =>
    (S.height (3 / 4 : ℝ)).decode x.1.1 q + x.1.2 * S.chiLeft q.1) p = _
  exact (spaces_mixedDerivative_add hdecodedSmooth
    (contDiff_const.mul (hS.2.2.1.1.comp contDiff_fst)) a b p).trans
      (congrArg (fun v : ℝ =>
        mixedDerivative a b ((S.height (3 / 4 : ℝ)).decode x.1.1) p + v)
          (spaces_mixedDerivative_const_mul (fun q => S.chiLeft q.1) x.1.2 a b p))

theorem n06_stateU_mixedDerivative_bound
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T)
    (hS : IsPhysicalSpaces D T S) (a b : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ N06StateHeightJetBound D S a b C := by
  obtain ⟨J, hJ, hdecoded⟩ :=
    n06_decoded_mixedDerivative_bound (D := D) (T := T) (S := S) hD hT hS a b
  obtain ⟨K, hK, hcutoff⟩ := n06_cutoff_mixedDerivative_bound (D := D) (T := T) (S := S) hS a b
  refine ⟨J + K, add_nonneg hJ hK, ?_⟩
  intro x p hp
  have hx := neighborhoodStateGrading_height_le S (a + b + 2) x
  have hd : |mixedDerivative a b ((S.height (3 / 4 : ℝ)).decode x.1.1) p| ≤
      J * stateGrading S (a + b + 2) x :=
    (hdecoded x.1.1 p hp).trans (mul_le_mul_of_nonneg_left hx.1 hJ)
  have hleft : |x.1.2 * mixedDerivative a b (fun q => S.chiLeft q.1) p| ≤
      K * stateGrading S (a + b + 2) x :=
    n06_abs_scalar_jet_le hx.2 (hcutoff p hp)
  exact (congrArg abs (n06_stateU_mixedDerivative_eq
    (D := D) (T := T) (S := S) hT hS x a b p)).trans_le
      (n06_abs_sum_jet_le hd hleft)

theorem n06_mixedDerivative_sub {f g : PolarPoint → ℝ}
    (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g) (a b : ℕ) (p : PolarPoint) :
    mixedDerivative a b (fun q => f q - g q) p =
      mixedDerivative a b f p - mixedDerivative a b g p := by
  have heq : (fun q => f q - g q) = (fun q => f q + (-1 : ℝ) * g q) := by
    funext q
    ring
  rw [heq, spaces_mixedDerivative_add hf (contDiff_const.mul hg),
    spaces_mixedDerivative_const_mul]
  ring

theorem n06_stateU_sub (S : PhysicalSpacesData) (x y : AnnularState S) :
    stateU S (x - y) = (fun p => stateU S x p - stateU S y p) := by
  exact (heightPairFieldLinear S).map_sub x.1 y.1

def N06StateHeightJetDifferenceBound (D : ReferenceData) (S : PhysicalSpacesData)
    (a b : ℕ) (C : ℝ) : Prop :=
  ∀ (x y : AnnularState S) (p : PolarPoint), p ∈ annularOpen D →
    |mixedDerivative a b (stateU S x) p - mixedDerivative a b (stateU S y) p| ≤
      C * stateGrading S (a + b + 2) (x - y)

/-- The difference is bounded in one original fixed seminorm; no separate
bound or smoothness assumption on the height difference is introduced. -/
theorem n06_stateU_mixedDerivative_difference_bound
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T)
    (hS : IsPhysicalSpaces D T S) (a b : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ N06StateHeightJetDifferenceBound D S a b C := by
  obtain ⟨C, hC, hbound⟩ :=
    n06_stateU_mixedDerivative_bound (D := D) (T := T) (S := S) hD hT hS a b
  refine ⟨C, hC, ?_⟩
  intro x y p hp
  have hjet : mixedDerivative a b (stateU S (x - y)) p =
      mixedDerivative a b (stateU S x) p - mixedDerivative a b (stateU S y) p :=
    (congrArg (fun f : PolarPoint → ℝ => mixedDerivative a b f p)
      (n06_stateU_sub S x y)).trans
        (n06_mixedDerivative_sub
          (neighborhood_stateU_contDiff (D := D) (T := T) (S := S) hT hS x)
          (neighborhood_stateU_contDiff (D := D) (T := T) (S := S) hT hS y) a b p)
  exact (congrArg abs hjet).symm.trans_le (hbound (x - y) p hp)

end ContinuousFlexibility.Statements
