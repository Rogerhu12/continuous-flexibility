import ContinuousFlexibility.Analysis.N01cStateSeminorms
import ContinuousFlexibility.Analysis.TameElementaryCalculus
import ContinuousFlexibility.Analysis.ProjectiveJetEvaluation
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Tactic.Abel

/-!
# Recovering the zeroth difference from the actual first parameter jet

A first-jet estimate along a closed state segment controls the actual
difference from the reference value by the ordinary real mean value
inequality. On a unit low-order ball, the one-high expression along that
segment is bounded by twice its order-zero counterpart. This preserves
every external material weight without treating the reference profile
itself as a small height-weight factor.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set
open ContinuousFlexibility.Statements
open scoped BigOperators

section ScalarDifference

variable {E : Type*} [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
  [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]

/-- The genuine first parameter jet gives the actual scalar difference,
without any normability hypothesis on the state space. -/
theorem smoothDirections_abs_sub_le_of_firstJet_bound
    {U : Set E} {f : E → ℝ} (J : SmoothDirections U f) {x d : E}
    (hseg : ∀ t ∈ Icc (0 : ℝ) 1, x + t • d ∈ U) {M : ℝ}
    (hM : ∀ t ∈ Icc (0 : ℝ) 1,
      |J.D 1 (x + t • d) (Fin.cons d Fin.elim0)| ≤ M) :
    |f (x + d) - f x| ≤ M := by
  have hd (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
      HasDerivAt (fun s : ℝ => f (x + s • d))
        (J.D 1 (x + t • d) (Fin.cons d Fin.elim0)) t := by
    apply hasDerivAt_iff_tendsto_slope_zero.mpr
    have h := J.hasProjectiveJetsOn.hasLineDerivAt J.open_domain (hseg t ht) d
    simpa only [HasProjectiveLineDerivAt, HasProjectiveCurveDerivAt,
      projectiveFirstJetValue, zero_add, zero_smul, add_zero, add_smul, add_assoc] using h
  have h := norm_image_sub_le_of_norm_deriv_le_segment_01'
    (fun t ht => (hd t ht).hasDerivWithinAt)
    (fun t ht => by
      simpa only [Real.norm_eq_abs] using hM t (Ico_subset_Icc_self ht))
  simpa only [one_smul, zero_smul, add_zero, Real.norm_eq_abs] using h

/-- Only the low norm of the displacement is bounded. Its high norm
remains an unrestricted single factor. -/
theorem oneHighVariationWeight_segment_one_le
    (p : ℕ → Seminorm ℝ E) (base high : ℕ) (x d : E)
    (hbase : p base d ≤ 1) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    oneHighVariationWeight p base high ((x + t • d) - x)
      (Fin.cons d Fin.elim0 : Fin 1 → E) ≤ 2 * (1 + p high d) := by
  have hdiff : (x + t • d) - x = t • d := by abel
  have hscale : p high (t • d) ≤ p high d := by
    rw [map_smul_eq_mul, Real.norm_of_nonneg ht.1]
    exact mul_le_of_le_one_left (apply_nonneg _ _) ht.2
  have hformula :
      oneHighVariationWeight p base high ((x + t • d) - x)
        (Fin.cons d Fin.elim0 : Fin 1 → E) =
      (1 + p high (t • d)) * p base d + p high d := by
    rw [hdiff]
    simp [oneHighVariationWeight]
  rw [hformula]
  calc
    (1 + p high (t • d)) * p base d + p high d ≤
        (1 + p high d) * 1 + p high d :=
      add_le_add (mul_le_mul (add_le_add le_rfl hscale) hbase
        (apply_nonneg _ _) (by positivity)) le_rfl
    _ ≤ 2 * (1 + p high d) := by linarith

/-- A first-jet one-high estimate implies the actual zeroth difference
estimate on the same segment, with the identical material factor. -/
theorem smoothDirections_difference_oneHigh_bound
    {U : Set E} {f : E → ℝ} (J : SmoothDirections U f)
    (p : ℕ → Seminorm ℝ E) (base high : ℕ) (x d : E)
    (hseg : ∀ t ∈ Icc (0 : ℝ) 1, x + t • d ∈ U)
    (hbase : p base d ≤ 1) {M : ℝ} (hM : 0 ≤ M)
    (hfirst : ∀ y ∈ U, ∀ v : Fin 1 → E,
      |J.D 1 y v| ≤ M * oneHighVariationWeight p base high (y - x) v) :
    |f (x + d) - f x| ≤ (2 * M) * (1 + p high d) := by
  apply smoothDirections_abs_sub_le_of_firstJet_bound J hseg
  intro t ht
  calc
    _ ≤ M * oneHighVariationWeight p base high ((x + t • d) - x)
        (Fin.cons d Fin.elim0 : Fin 1 → E) :=
      hfirst (x + t • d) (hseg t ht) _
    _ ≤ M * (2 * (1 + p high d)) :=
      mul_le_mul_of_nonneg_left
        (oneHighVariationWeight_segment_one_le p base high x d hbase ht) hM
    _ = (2 * M) * (1 + p high d) := by ring

end ScalarDifference

/-- The actual product neighbourhood contains the entire segment from its
reference point to any of its points. -/
theorem pair_seminorm_reference_segment
    {E : Type*} [AddCommGroup E] [Module ℝ E]
    (p : Seminorm ℝ E) (x : E) {z : E × ℝ} {ε t : ℝ}
    (hz : p (z.1 - x) < ε ∧ |z.2| < ε) (ht : t ∈ Icc (0 : ℝ) 1) :
    p (((x, (0 : ℝ)) + t • (z - (x, (0 : ℝ)))).1 - x) < ε ∧
      |((x, (0 : ℝ)) + t • (z - (x, (0 : ℝ)))).2| < ε := by
  have hfst : ((x, (0 : ℝ)) + t • (z - (x, (0 : ℝ)))).1 - x =
      t • (z.1 - x) := by
    simp only [Prod.fst_add, Prod.fst_smul, Prod.fst_sub]
    abel
  have hsnd : ((x, (0 : ℝ)) + t • (z - (x, (0 : ℝ)))).2 = t * z.2 := by
    change t * (z.2 - 0) = t * z.2
    rw [sub_zero]
  constructor
  · rw [hfst, map_smul_eq_mul, Real.norm_of_nonneg ht.1]
    exact (mul_le_of_le_one_left (apply_nonneg p _) ht.2).trans_lt hz.1
  · rw [hsnd, abs_mul, abs_of_nonneg ht.1]
    exact (mul_le_of_le_one_left (abs_nonneg _) ht.2).trans_lt hz.2

end ContinuousFlexibility.Analysis

namespace ContinuousFlexibility.Statements

open Set ContinuousFlexibility.Analysis

private abbrev n01cDifferenceStateGroup (S : PhysicalSpacesData) :
    AddCommGroup (AnnularState S) := inferInstance
attribute [local instance] n01cDifferenceStateGroup

private abbrev n01cDifferenceStateModule (S : PhysicalSpacesData) :
    Module ℝ (AnnularState S) := inferInstance
attribute [local instance] n01cDifferenceStateModule

private abbrev n01cDifferenceStateSMul (S : PhysicalSpacesData) :
    SMul ℝ (AnnularState S) :=
  (n01cDifferenceStateModule S).toDistribMulAction.toDistribSMul.toSMul
attribute [local instance] n01cDifferenceStateSMul

private abbrev n01cDifferenceJointGroup (S : PhysicalSpacesData) :
    AddCommGroup (AnnularState S × ℝ) := inferInstance
attribute [local instance] n01cDifferenceJointGroup

private abbrev n01cDifferenceJointModule (S : PhysicalSpacesData) :
    Module ℝ (AnnularState S × ℝ) := inferInstance
attribute [local instance] n01cDifferenceJointModule

private abbrev n01cDifferenceJointSMul (S : PhysicalSpacesData) :
    SMul ℝ (AnnularState S × ℝ) :=
  (n01cDifferenceJointModule S).toDistribMulAction.toDistribSMul.toSMul
attribute [local instance] n01cDifferenceJointSMul

set_option backward.isDefEq.respectTransparency true in
/-- No smaller neighbourhood is required for the reference-segment
argument used to estimate actual coefficient differences. -/
theorem stateNeighborhood_reference_segment
    (S : PhysicalSpacesData) (C : NonlinearGeometryData S)
    {base : ℕ} {ε t : ℝ} {z : AnnularState S × ℝ}
    (hz : z ∈ stateNeighborhood S C base ε) (ht : t ∈ Icc (0 : ℝ) 1) :
    (C.referenceState, (0 : ℝ)) +
        t • (z - (C.referenceState, (0 : ℝ))) ∈ stateNeighborhood S C base ε :=
  pair_seminorm_reference_segment (stateGrading S base) C.referenceState hz ht

end ContinuousFlexibility.Statements
