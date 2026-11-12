import ContinuousFlexibility.Analysis.ProjectiveNewtonRecurrence
import ContinuousFlexibility.Analysis.StateNeighborhood

/-!
# Actual N02 residual values on one common tame neighborhood

The zeroth jet of the actual residual map supplies its value bounds. A
fixed order shift removes the lower-order restriction in that estimate.
The numerical elimination is performed before specializing the physical
projective spaces, and one low-order ball precedes every output order.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set
open ContinuousFlexibility.Statements

set_option backward.isDefEq.respectTransparency false

def TameValueBoundAtOrder
    {Z Y : Type*} [AddCommGroup Z] [Module ℝ Z]
    [AddCommGroup Y] [Module ℝ Y]
    (p : ℕ → Seminorm ℝ Z) (q : ℕ → Seminorm ℝ Y)
    (U : Set Z) (f : Z → Y) (low : ℕ) (δ : ℝ) (loss s : ℕ) (B : ℝ) : Prop :=
  ∀ z ∈ U, p low z < δ → q s (f z) ≤ B * (1 + p (s + loss) z)

theorem exists_tameValueBoundAtOrder_zero
    {Z Y : Type*} [TopologicalSpace Z] [AddCommGroup Z] [Module ℝ Z]
    [TopologicalSpace Y] [AddCommGroup Y] [Module ℝ Y]
    {p : ℕ → Seminorm ℝ Z} {q : ℕ → Seminorm ℝ Y}
    (hp : Monotone p) (hq : Monotone q) {U : Set Z} {f : Z → Y}
    (hT : SmoothTameOn p q U f) (hzero : (0 : Z) ∈ U) :
    ∃ loss low : ℕ, ∃ δ : ℝ, 0 < δ ∧ ∀ s : ℕ, ∃ B : ℝ, 0 ≤ B ∧
      TameValueBoundAtOrder p q U f low δ loss s B := by
  obtain ⟨loss, low, δ, hδ, hbound⟩ := exists_zero_tame_bound hT hzero
  refine ⟨low + loss, low, δ, hδ, ?_⟩
  intro s
  obtain ⟨B, hB, hvalue⟩ := hbound (max s low) (le_max_right _ _)
  refine ⟨B, hB, ?_⟩
  intro z hz hlow
  have hv := hvalue z hz (by simpa only [sub_zero] using hlow)
  calc
    q s (f z) ≤ q (max s low) (f z) := hq (le_max_left _ _) _
    _ ≤ B * (1 + p (max s low + loss) z) := hv
    _ ≤ B * (1 + p (s + (low + loss)) z) :=
      mul_le_mul_of_nonneg_left
        (add_le_add_left (hp (by omega : max s low + loss ≤ s + (low + loss)) z) 1) hB

def N02ResidualValueBoundAtOrder
    (S : PhysicalSpacesData) (C : NonlinearGeometryData S) (R : ReturnEquationData S)
    (base : ℕ) (ε : ℝ) (low : ℕ) (δ : ℝ) (loss s : ℕ) (B : ℝ) : Prop :=
  TameValueBoundAtOrder (pairGrading (sectorGrading S) realGrading)
    (S.circle (3 / 4 : ℝ)).grading (sectorNeighborhood S base ε ε)
    (fun v => R.residual (liftSectorParameter S C v)) low δ loss s B

private theorem seminorm_real_zero_mem_pair_ball
    {E : Type*} [AddCommGroup E] [Module ℝ E]
    (p : Seminorm ℝ E) {ε : ℝ} (hε : 0 < ε) :
    p 0 < ε ∧ |(0 : ℝ)| < ε := by
  simpa only [map_zero, abs_zero] using And.intro hε hε

/-- This uses the supplied N02 residual itself and introduces no
component-dependent neighborhood or additional residual assumption. -/
theorem n02Residual_allOrder_value_bound
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {R : ReturnEquationData S}
    {base : ℕ} {ε : ℝ} (hε : 0 < ε)
    (hN02 : N02Properties D T S C R base ε) :
    ∃ loss low : ℕ, ∃ δ : ℝ, 0 < δ ∧ ∀ s : ℕ, ∃ B : ℝ, 0 ≤ B ∧
      N02ResidualValueBoundAtOrder S C R base ε low δ loss s B := by
  have hzero : (0 : StateDirections S × ℝ) ∈ sectorNeighborhood S base ε ε := by
    change sectorGrading S base (0 : StateDirections S) < ε ∧ |(0 : ℝ)| < ε
    exact seminorm_real_zero_mem_pair_ball (sectorGrading S base) hε
  exact exists_tameValueBoundAtOrder_zero
    (Z := StateDirections S × ℝ) (Y := CircleSpace S)
    (p := pairGrading (sectorGrading S) realGrading)
    (q := (S.circle (3 / 4 : ℝ)).grading)
    (U := sectorNeighborhood S base ε ε)
    (f := fun v => R.residual (liftSectorParameter S C v))
    (tamePairGrading_monotone (sectorGrading_monotone S) (fun _ _ _ => le_rfl))
    (gradedSeminorm_monotone (fun n => (S.circle (3 / 4 : ℝ)).level n)
      (S.circle (3 / 4 : ℝ)).bond)
    hN02.2.2.2.2.2.2.2.2.2.2 hzero

end ContinuousFlexibility.Analysis
