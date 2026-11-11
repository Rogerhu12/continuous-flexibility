import ContinuousFlexibility.Analysis.PhysicalJetClosedGraph

/-!
# Restriction and projective compatibility for the physical jet levels

Restriction deletes the coordinates of higher total order. It contracts
the finite Hilbert product and preserves the actual unweighted weak
derivatives recovered from the retained weighted coordinates.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open MeasureTheory
open scoped BigOperators

/-- Inclusion of the lower order triples, preserving all three exponents. -/
def physicalJetIndexOfLE {s t : ℕ} (hst : s ≤ t) : JetIndex s ↪ JetIndex t where
  toFun j := ⟨fun i => Fin.castLE (Nat.succ_le_succ hst) (j.val i), j.property.trans hst⟩
  inj' := by
    intro j k hjk
    apply Subtype.ext
    funext i
    apply Fin.ext
    exact congrArg (fun z : JetIndex t => (z.val i).val) hjk

@[simp] theorem physicalJetIndexOfLE_val {s t : ℕ} (hst : s ≤ t) (j : JetIndex s) (i : Fin 3) :
    ((physicalJetIndexOfLE hst j).val i).val = (j.val i).val := rfl

@[simp] theorem physicalJetIndexOfLE_zero {s t : ℕ} (hst : s ≤ t) :
    physicalJetIndexOfLE hst (zeroJetIndex s) = zeroJetIndex t := by
  apply Subtype.ext
  funext i
  apply Fin.ext
  rfl

private def physicalJetHilbertRestrictFun {s t : ℕ} (hst : s ≤ t)
    (z : PhysicalJetHilbert t) : PhysicalJetHilbert s :=
  WithLp.toLp 2 (fun j => z (physicalJetIndexOfLE hst j))

private theorem physicalJetHilbertRestrictFun_norm_le {s t : ℕ} (hst : s ≤ t)
    (z : PhysicalJetHilbert t) : ‖physicalJetHilbertRestrictFun hst z‖ ≤ ‖z‖ := by
  apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [PiLp.norm_sq_eq_of_L2, PiLp.norm_sq_eq_of_L2]
  calc
    (∑ j : JetIndex s, ‖physicalJetHilbertRestrictFun hst z j‖ ^ 2) =
        ∑ j ∈ Finset.univ.map (physicalJetIndexOfLE hst), ‖z j‖ ^ 2 := by
      change (∑ j : JetIndex s, ‖z (physicalJetIndexOfLE hst j)‖ ^ 2) = _
      rw [Finset.sum_map]
    _ ≤ ∑ j : JetIndex t, ‖z j‖ ^ 2 :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun _ _ _ => sq_nonneg _)

/-- Continuous linear restriction in the actual finite `PiLp 2` norm. -/
def physicalJetHilbertRestrict {s t : ℕ} (hst : s ≤ t) :
    PhysicalJetHilbert t →L[ℝ] PhysicalJetHilbert s :=
  (show PhysicalJetHilbert t →ₗ[ℝ] PhysicalJetHilbert s from
    { toFun := physicalJetHilbertRestrictFun hst
      map_add' := by
        intro u v
        apply PiLp.ext
        intro j
        rfl
      map_smul' := by
        intro c u
        apply PiLp.ext
        intro j
        rfl }).mkContinuous 1 (by
    intro z
    change ‖physicalJetHilbertRestrictFun hst z‖ ≤ 1 * ‖z‖
    rw [one_mul]
    exact physicalJetHilbertRestrictFun_norm_le hst z)

@[simp] theorem physicalJetHilbertRestrict_apply {s t : ℕ} (hst : s ≤ t)
    (z : PhysicalJetHilbert t) (j : JetIndex s) :
    physicalJetHilbertRestrict hst z j = z (physicalJetIndexOfLE hst j) := rfl

theorem physicalJetHilbertRestrict_norm_le {s t : ℕ} (hst : s ≤ t) (z : PhysicalJetHilbert t) :
    ‖physicalJetHilbertRestrict hst z‖ ≤ ‖z‖ := physicalJetHilbertRestrictFun_norm_le hst z

@[simp] theorem physicalJetHilbertRestrict_zero {s t : ℕ} (hst : s ≤ t) (z : PhysicalJetHilbert t) :
    physicalJetHilbertRestrict hst z (zeroJetIndex s) = z (zeroJetIndex t) := by
  rw [physicalJetHilbertRestrict_apply, physicalJetIndexOfLE_zero]

@[simp] theorem physicalJetWeight_indexOfLE (T : MaterialData) {s t : ℕ}
    (hst : s ≤ t) (j : JetIndex s) (p : PolarPoint) :
    physicalJetWeight T (physicalJetIndexOfLE hst j) p = physicalJetWeight T j p := rfl

/-- The recovered unweighted derivative is the same `L²` class in either level. -/
theorem physicalJetNormalizedDerivative_restrict {D : ReferenceData} {T : MaterialData}
    (hT : IsMaterialData D T) {s t : ℕ} (hst : s ≤ t) (j : JetIndex s) (z : PhysicalJetHilbert t) :
    physicalJetNormalizedDerivative hT j (physicalJetHilbertRestrict hst z) =
      physicalJetNormalizedDerivative hT (physicalJetIndexOfLE hst j) z := by
  apply Lp.ext
  filter_upwards [physicalJetNormalizedDerivative_ae hT j (physicalJetHilbertRestrict hst z),
    physicalJetNormalizedDerivative_ae hT (physicalJetIndexOfLE hst j) z] with p hlow hhigh
  rw [hlow, hhigh, physicalJetHilbertRestrict_apply, physicalJetWeight_indexOfLE]

theorem physicalJetHilbertRestrict_mem_physicalJetGraph {D : ReferenceData} {T : MaterialData}
    (hT : IsMaterialData D T) {s t : ℕ} (hst : s ≤ t) {z : PhysicalJetHilbert t}
    (hz : z ∈ physicalJetGraph T t) : physicalJetHilbertRestrict hst z ∈ physicalJetGraph T s := by
  obtain ⟨href, hweak⟩ := (mem_physicalJetGraph_iff_normalized hT z).mp hz
  apply (mem_physicalJetGraph_iff_normalized hT (physicalJetHilbertRestrict hst z)).mpr
  refine ⟨?_, fun j => ?_⟩
  · simpa only [physicalJetHilbertRestrict_zero] using href
  · rw [physicalJetNormalizedDerivative_restrict, physicalJetHilbertRestrict_zero]
    simpa only [physicalJetIndexOfLE_val] using hweak (physicalJetIndexOfLE hst j)

/-- The same restriction on the closed graph levels. -/
def physicalJetGraphRestrict {D : ReferenceData} {T : MaterialData} (hT : IsMaterialData D T)
    {s t : ℕ} (hst : s ≤ t) : physicalJetClosedSubmodule hT t →L[ℝ] physicalJetClosedSubmodule hT s :=
  ((physicalJetHilbertRestrict hst).comp (physicalJetClosedSubmodule hT t).subtypeL).codRestrict
    (physicalJetClosedSubmodule hT s) (by
      intro z
      change physicalJetHilbertRestrict hst z.val ∈
        (physicalJetClosedSubmodule hT s : Set (PhysicalJetHilbert s))
      rw [physicalJetClosedSubmodule_carrier hT s]
      have hz : z.val ∈ physicalJetGraph T t := by
        rw [← physicalJetClosedSubmodule_carrier hT t]
        exact z.property
      exact physicalJetHilbertRestrict_mem_physicalJetGraph hT hst hz)

@[simp] theorem physicalJetGraphRestrict_apply {D : ReferenceData} {T : MaterialData}
    (hT : IsMaterialData D T) {s t : ℕ} (hst : s ≤ t) (z : physicalJetClosedSubmodule hT t)
    (j : JetIndex s) : (physicalJetGraphRestrict hT hst z).val j = z.val (physicalJetIndexOfLE hst j) := rfl

theorem physicalJetGraphRestrict_norm_le {D : ReferenceData} {T : MaterialData}
    (hT : IsMaterialData D T) {s t : ℕ} (hst : s ≤ t) (z : physicalJetClosedSubmodule hT t) :
    ‖physicalJetGraphRestrict hT hst z‖ ≤ ‖z‖ := physicalJetHilbertRestrict_norm_le hst z.val

def physicalJetBond {D : ReferenceData} {T : MaterialData} (hT : IsMaterialData D T) (s : ℕ) :
    physicalJetClosedSubmodule hT (s + 1) →L[ℝ] physicalJetClosedSubmodule hT s :=
  physicalJetGraphRestrict hT (Nat.le_succ s)

/-- The actual closed projective carrier of compatible weighted physical jets. -/
abbrev PhysicalJetProjectiveLimit {D : ReferenceData} {T : MaterialData} (hT : IsMaterialData D T) :=
  Analysis.ProjectiveLimit (fun s => ↥(physicalJetClosedSubmodule hT s)) (physicalJetBond hT)

theorem isClosed_physicalJetProjectiveCarrier {D : ReferenceData} {T : MaterialData}
    (hT : IsMaterialData D T) :
    IsClosed (Analysis.compatibleSubmodule (fun s => ↥(physicalJetClosedSubmodule hT s)) (physicalJetBond hT) :
      Set (∀ s, physicalJetClosedSubmodule hT s)) := Analysis.isClosed_compatibleSubmodule _ _

theorem physicalJetProjectiveLimit_complete {D : ReferenceData} {T : MaterialData}
    (hT : IsMaterialData D T) : CompleteSpace (PhysicalJetProjectiveLimit hT) :=
  Analysis.projectiveLimit_completeSpace _ _

theorem physicalJetProjective_level_norm_mono {D : ReferenceData} {T : MaterialData}
    {hT : IsMaterialData D T} (u : PhysicalJetProjectiveLimit hT) : Monotone (fun s => ‖u.val s‖) := by
  apply monotone_nat_of_le_succ
  intro s
  rw [← u.property s]
  exact physicalJetGraphRestrict_norm_le hT (Nat.le_succ s) (u.val (s + 1))

theorem physicalJetProjective_zero_eq {D : ReferenceData} {T : MaterialData}
    {hT : IsMaterialData D T} (u : PhysicalJetProjectiveLimit hT) (s : ℕ) :
    (u.val s).val (zeroJetIndex s) = (u.val 0).val (zeroJetIndex 0) := by
  induction s with
  | zero => rfl
  | succ s ih =>
    have h := congrArg (fun z : physicalJetClosedSubmodule hT s => z.val (zeroJetIndex s)) (u.property s)
    rw [physicalJetBond, physicalJetGraphRestrict_apply, physicalJetIndexOfLE_zero] at h
    exact h.trans ih

/-- The common zero coordinate as an actual continuous linear map on the limit. -/
def physicalJetProjectiveZero {D : ReferenceData} {T : MaterialData} (hT : IsMaterialData D T) :
    PhysicalJetProjectiveLimit hT →L[ℝ] CylinderL2 :=
  (physicalJetCoordinate 0 (zeroJetIndex 0)).comp
    ((physicalJetClosedSubmodule hT 0).subtypeL.comp
      (Analysis.projectiveCoordinate (fun s => ↥(physicalJetClosedSubmodule hT s)) (physicalJetBond hT) 0))

theorem physicalJetProjectiveZero_apply {D : ReferenceData} {T : MaterialData}
    (hT : IsMaterialData D T) (u : PhysicalJetProjectiveLimit hT) (s : ℕ) :
    physicalJetProjectiveZero hT u = (u.val s).val (zeroJetIndex s) :=
  (physicalJetProjective_zero_eq u s).symm

end ContinuousFlexibility.Statements
