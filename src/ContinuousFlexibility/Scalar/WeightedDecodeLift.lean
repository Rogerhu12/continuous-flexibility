module

public import ContinuousFlexibility.Analysis.PhysicalJetBonding
public import ContinuousFlexibility.Scalar.WeightedTowerCalculus

/-!
# Exact physical norms and lifts through the Sobolev decoder

The frozen Sobolev-model hypotheses identify every coordinate norm with an
actual weighted physical norm.  Monotonicity of those physical norms therefore
identifies the increasing projective grading with the physical norm itself.

Surjectivity and injectivity of the decoder give a unique algebraic lift.
Continuity of a lifted linear field map is then proved from physical-norm
estimates in the actual projective topology.  No inverse continuity for the
pointwise topology on all scalar fields is used.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Statements

open Set MeasureTheory ContinuousFlexibility.Analysis
open scoped BigOperators ENNReal

/-- Retaining more actual weighted jets increases the physical norm. -/
theorem physicalNorm_monotone_of_heightMember
    {D : ReferenceData} {T : MaterialData} {γ : ℝ} {f : PolarPoint → ℝ}
    (hf : HeightMember D T γ f) : Monotone (fun s => physicalNorm T γ s f) := by
  classical
  intro s t hst
  unfold physicalNorm
  apply Real.sqrt_le_sqrt
  apply ENNReal.toReal_mono
  · apply ENNReal.sum_ne_top.mpr
    intro j _
    exact ENNReal.pow_ne_top
      (hf.2.2.2.2 (j.val 0).val (j.val 1).val (j.val 2).val).eLpNorm_ne_top
  · calc
      (∑ j : JetIndex s,
          eLpNorm (weightedPhysicalJet T γ (j.val 0).val (j.val 1).val (j.val 2).val f)
            2 materialCylinderMeasure ^ 2) =
          ∑ j ∈ Finset.univ.map (physicalJetIndexOfLE hst),
            eLpNorm (weightedPhysicalJet T γ (j.val 0).val (j.val 1).val (j.val 2).val f)
              2 materialCylinderMeasure ^ 2 := by
        rw [Finset.sum_map]
        simp only [physicalJetIndexOfLE_val]
      _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
        (fun _ _ _ => bot_le)

/-- The frozen norm identity and the actual weighted-jet inclusion eliminate
the finite maximum in the model grading, without assumptions on its bonds. -/
theorem sobolevGrading_eq_physicalNorm
    {D : ReferenceData} {T : MaterialData} {γ : ℝ} {A : SobolevModelData}
    (hA : IsSobolevModel D T γ A) (u : A.Space) (s : ℕ) :
    A.grading s u = physicalNorm T γ s (A.decode u) := by
  apply le_antisymm
  · apply (gradedSeminorm_le_iff (fun n => A.level n) A.bond s u
      (Real.sqrt_nonneg _)).mpr
    intro i hi
    rw [hA.2.2.2.2.2.2.2 u i]
    exact physicalNorm_monotone_of_heightMember (hA.2.2.2.1 u) hi
  · rw [← hA.2.2.2.2.2.2.2 u s]
    exact norm_coordinate_le_graded (fun n => A.level n) A.bond le_rfl u

namespace SobolevModelData

variable {D : ReferenceData} {T : MaterialData} {γ : ℝ} {A : SobolevModelData}

/-- The unique preimage of an actual height member under the frozen decoder. -/
def liftHeight (hA : IsSobolevModel D T γ A) (f : PolarPoint → ℝ)
    (hf : HeightMember D T γ f) : A.Space :=
  Classical.choose (hA.2.2.2.2.1 f hf)

theorem decode_liftHeight (hA : IsSobolevModel D T γ A) (f : PolarPoint → ℝ)
    (hf : HeightMember D T γ f) : A.decode (liftHeight hA f hf) = f :=
  Classical.choose_spec (hA.2.2.2.2.1 f hf)

theorem eq_liftHeight (hA : IsSobolevModel D T γ A) (f : PolarPoint → ℝ)
    (hf : HeightMember D T γ f) (u : A.Space) (hu : A.decode u = f) :
    u = liftHeight hA f hf :=
  hA.2.2.2.2.2.1 (hu.trans (decode_liftHeight hA f hf).symm)

section Linear

variable {E : Type*} [AddCommGroup E] [Module ℝ E]

/-- An actual linear field map with height-member values lifts linearly.
Linearity is proved by decoder injectivity, so the choice of preimages cannot
introduce a separate representation of the operation. -/
def liftLinear (hA : IsSobolevModel D T γ A)
    (L : E →ₗ[ℝ] (PolarPoint → ℝ)) (hL : ∀ x, HeightMember D T γ (L x)) :
    E →ₗ[ℝ] A.Space where
  toFun := fun x => liftHeight hA (L x) (hL x)
  map_add' := by
    intro x y
    apply hA.2.2.2.2.2.1
    simp only [map_add, decode_liftHeight]
  map_smul' := by
    intro c x
    apply hA.2.2.2.2.2.1
    simp only [map_smul, decode_liftHeight, RingHom.id_apply]

theorem decode_liftLinear (hA : IsSobolevModel D T γ A)
    (L : E →ₗ[ℝ] (PolarPoint → ℝ)) (hL : ∀ x, HeightMember D T γ (L x)) (x : E) :
    A.decode (liftLinear hA L hL x) = L x :=
  decode_liftHeight hA (L x) (hL x)

theorem grading_liftLinear (hA : IsSobolevModel D T γ A)
    (L : E →ₗ[ℝ] (PolarPoint → ℝ)) (hL : ∀ x, HeightMember D T γ (L x))
    (s : ℕ) (x : E) :
    A.grading s (liftLinear hA L hL x) = physicalNorm T γ s (L x) := by
  rw [sobolevGrading_eq_physicalNorm hA, decode_liftLinear]

/-- A physical linear estimate transfers with exactly the same base, loss
and constants.  The target map is constructed from its actual decoded field. -/
theorem liftLinear_isTame (hA : IsSobolevModel D T γ A)
    (L : E →ₗ[ℝ] (PolarPoint → ℝ)) (hL : ∀ x, HeightMember D T γ (L x))
    {p : ℕ → Seminorm ℝ E} {base loss : ℕ}
    (hbound : ∀ s, base ≤ s → ∃ C : ℝ, 0 ≤ C ∧
      ∀ x, physicalNorm T γ s (L x) ≤ C * p (s + loss) x) :
    IsTameLinear p A.grading (liftLinear hA L hL) loss base := by
  intro s hs
  obtain ⟨C, hC, hCx⟩ := hbound s hs
  refine ⟨⟨C, hC⟩, fun x => ?_⟩
  rw [grading_liftLinear]
  exact hCx x

variable [TopologicalSpace E]

/-- The lift is continuous for the actual Sobolev-model topology once its
physical norms have fixed-loss control by a defining source grading. -/
def liftCLM (hA : IsSobolevModel D T γ A)
    (L : E →ₗ[ℝ] (PolarPoint → ℝ)) (hL : ∀ x, HeightMember D T γ (L x))
    {p : ℕ → Seminorm ℝ E} (hp : WithSeminorms p) {base loss : ℕ}
    (hbound : ∀ s, base ≤ s → ∃ C : ℝ, 0 ≤ C ∧
      ∀ x, physicalNorm T γ s (L x) ≤ C * p (s + loss) x) :
    E →L[ℝ] A.Space :=
  (liftLinear_isTame hA L hL hbound).toContinuousLinearMap hp
    (withSeminorms_graded (fun n => A.level n) A.bond)
    (gradedSeminorm_monotone (fun n => A.level n) A.bond)

theorem liftCLM_apply (hA : IsSobolevModel D T γ A)
    (L : E →ₗ[ℝ] (PolarPoint → ℝ)) (hL : ∀ x, HeightMember D T γ (L x))
    {p : ℕ → Seminorm ℝ E} (hp : WithSeminorms p) {base loss : ℕ}
    (hbound : ∀ s, base ≤ s → ∃ C : ℝ, 0 ≤ C ∧
      ∀ x, physicalNorm T γ s (L x) ≤ C * p (s + loss) x) (x : E) :
    liftCLM hA L hL hp hbound x = liftLinear hA L hL x :=
  IsTameLinear.toContinuousLinearMap_apply _ _ _ _ x

theorem decode_liftCLM (hA : IsSobolevModel D T γ A)
    (L : E →ₗ[ℝ] (PolarPoint → ℝ)) (hL : ∀ x, HeightMember D T γ (L x))
    {p : ℕ → Seminorm ℝ E} (hp : WithSeminorms p) {base loss : ℕ}
    (hbound : ∀ s, base ≤ s → ∃ C : ℝ, 0 ≤ C ∧
      ∀ x, physicalNorm T γ s (L x) ≤ C * p (s + loss) x) (x : E) :
    A.decode (liftCLM hA L hL hp hbound x) = L x := by
  rw [liftCLM_apply, decode_liftLinear]

/-- The constructed linear lift has an actual derivative tower with one
base and loss on every chosen open source domain. -/
theorem liftCLM_fixedNeighborhoodSmoothTame (hA : IsSobolevModel D T γ A)
    (L : E →ₗ[ℝ] (PolarPoint → ℝ)) (hL : ∀ x, HeightMember D T γ (L x))
    {p : ℕ → Seminorm ℝ E} (hp : WithSeminorms p) {base loss : ℕ}
    (hbound : ∀ s, base ≤ s → ∃ C : ℝ, 0 ≤ C ∧
      ∀ x, physicalNorm T γ s (L x) ≤ C * p (s + loss) x)
    {U : Set E} (hU : IsOpen U) :
    FixedNeighborhoodSmoothTame p A.grading U base loss (liftCLM hA L hL hp hbound) := by
  have ht : IsTameLinear p A.grading
      (liftCLM hA L hL hp hbound).toLinearMap loss base :=
    liftLinear_isTame hA L hL hbound
  exact (fixedNeighborhoodSmoothTame_continuousLinear _ ht).restrict hU (subset_univ U)

end Linear

section ChangeModel

variable {B : SobolevModelData}

private theorem changeModel_physicalBound (hA : IsSobolevModel D T γ A) :
    ∀ s, 0 ≤ s → ∃ C : ℝ, 0 ≤ C ∧ ∀ u : A.Space,
      physicalNorm T γ s (A.decode u) ≤ C * A.grading (s + 0) u := by
  intro s _
  refine ⟨1, zero_le_one, fun u => ?_⟩
  rw [Nat.add_zero, one_mul, sobolevGrading_eq_physicalNorm hA]

/-- Two realizations of the same weighted physical space are linked by an
actual continuous linear map.  This needs no additional analytic estimate. -/
def changeModel (hA : IsSobolevModel D T γ A) (hB : IsSobolevModel D T γ B) :
    A.Space →L[ℝ] B.Space :=
  liftCLM hB A.decode hA.2.2.2.1
    (withSeminorms_graded (fun n => A.level n) A.bond) (changeModel_physicalBound hA)

theorem decode_changeModel (hA : IsSobolevModel D T γ A)
    (hB : IsSobolevModel D T γ B) (u : A.Space) :
    B.decode (changeModel hA hB u) = A.decode u :=
  decode_liftCLM hB A.decode hA.2.2.2.1
    (withSeminorms_graded (fun n => A.level n) A.bond) (changeModel_physicalBound hA) u

theorem grading_changeModel (hA : IsSobolevModel D T γ A)
    (hB : IsSobolevModel D T γ B) (u : A.Space) (s : ℕ) :
    B.grading s (changeModel hA hB u) = A.grading s u := by
  rw [sobolevGrading_eq_physicalNorm hB, decode_changeModel,
    sobolevGrading_eq_physicalNorm hA]

theorem changeModel_inverse (hA : IsSobolevModel D T γ A)
    (hB : IsSobolevModel D T γ B) (u : A.Space) :
    changeModel hB hA (changeModel hA hB u) = u := by
  apply hA.2.2.2.2.2.1
  rw [decode_changeModel, decode_changeModel]

theorem changeModel_isTame (hA : IsSobolevModel D T γ A)
    (hB : IsSobolevModel D T γ B) :
    IsTameLinear A.grading B.grading (changeModel hA hB).toLinearMap 0 0 :=
  liftLinear_isTame hB A.decode hA.2.2.2.1 (changeModel_physicalBound hA)

end ChangeModel

end SobolevModelData

end ContinuousFlexibility.Statements
