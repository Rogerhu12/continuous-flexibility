import ContinuousFlexibility.Radial.OuterPhysicalHilbert
import ContinuousFlexibility.Radial.TailDeepInverse

/-!
# The actual physical Dirichlet inverse on the deep tail

The operator is obtained from the constructed deep-tail Friedrichs inverse
by the exact physical Hilbert isometry. Its norm is at most 64/j^4. The
factor 12 is retained in both the graph and the differential identity.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open Set MeasureTheory Real
open ContinuousFlexibility.Statements

set_option backward.isDefEq.respectTransparency false

/-- The physical Dirichlet realization of B_j, transported from the
actual Friedrichs form by the exact coordinate and gauge isometry. -/
def OuterPhysicalDirichletGraph
    {D : ReferenceData} {T : DeepTailData} {right : Bool} {j start : ℕ}
    (hD : IsAccumulatingProfile D) (hphysical : TailPhysicalRelation D T right j start)
    (u f : OuterPhysicalTailL2 D T right) : Prop :=
  TailFriedrichsGraph T T.endpoint
    (outerPhysicalTailEquiv hD hphysical u)
    ((12 : ℝ) • outerPhysicalTailEquiv hD hphysical f +
      T.Λ • outerPhysicalTailEquiv hD hphysical u)

def outerPhysicalDirichletInverse
    {D : ReferenceData} {T : DeepTailData} {right : Bool} {j start : ℕ}
    (hD : IsAccumulatingProfile D) (hphysical : TailPhysicalRelation D T right j start)
    (G : DeepTailL2 T →L[ℝ] DeepTailL2 T) :
    OuterPhysicalTailL2 D T right →L[ℝ] OuterPhysicalTailL2 D T right :=
  (outerPhysicalTailEquiv hD hphysical).symm.toContinuousLinearEquiv.toContinuousLinearMap.comp
    (G.comp ((12 : ℝ) •
      (outerPhysicalTailEquiv hD hphysical).toContinuousLinearEquiv.toContinuousLinearMap))

theorem outerPhysicalDirichletInverse_apply
    {D : ReferenceData} {T : DeepTailData} {right : Bool} {j start : ℕ}
    (hD : IsAccumulatingProfile D) (hphysical : TailPhysicalRelation D T right j start)
    (G : DeepTailL2 T →L[ℝ] DeepTailL2 T) (f : OuterPhysicalTailL2 D T right) :
    outerPhysicalTailEquiv hD hphysical (outerPhysicalDirichletInverse hD hphysical G f) =
      G ((12 : ℝ) • outerPhysicalTailEquiv hD hphysical f) := by
  exact (outerPhysicalTailEquiv hD hphysical).apply_symm_apply _

theorem outerPhysicalDirichletInverse_norm_le
    {D : ReferenceData} {T : DeepTailData} {right : Bool} {j start : ℕ}
    (hD : IsAccumulatingProfile D) (hphysical : TailPhysicalRelation D T right j start)
    (G : DeepTailL2 T →L[ℝ] DeepTailL2 T) {M : ℝ} (hM : 0 ≤ M) (hG : ‖G‖ ≤ M) :
    ‖outerPhysicalDirichletInverse hD hphysical G‖ ≤ 12 * M := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro f
  rw [← (outerPhysicalTailEquiv hD hphysical).norm_map
    (outerPhysicalDirichletInverse hD hphysical G f),
    outerPhysicalDirichletInverse_apply]
  calc
    _ ≤ ‖G‖ * ‖(12 : ℝ) • outerPhysicalTailEquiv hD hphysical f‖ := G.le_opNorm _
    _ ≤ M * ‖(12 : ℝ) • outerPhysicalTailEquiv hD hphysical f‖ :=
      mul_le_mul_of_nonneg_right hG (norm_nonneg _)
    _ = (12 * M) * ‖f‖ := by
      rw [norm_smul, Real.norm_of_nonneg (by norm_num : (0 : ℝ) ≤ 12),
        (outerPhysicalTailEquiv hD hphysical).norm_map]
      ring

theorem deepTail_physical_frequency_bound {j : ℕ} (hj : 2 ≤ j) :
    48 / ((j : ℝ) ^ 2 * ((j : ℝ) ^ 2 - 1)) ≤ 64 / (j : ℝ) ^ 4 := by
  have hjR : 2 ≤ (j : ℝ) := by exact_mod_cast hj
  have hj2 : 4 ≤ (j : ℝ) ^ 2 := by nlinarith
  have hΛ : 0 < (j : ℝ) ^ 2 * ((j : ℝ) ^ 2 - 1) := by positivity
  have hj4 : 0 < (j : ℝ) ^ 4 := by positivity
  apply (div_le_div_iff₀ hΛ hj4).2
  have hprod : 0 ≤ (j : ℝ) ^ 2 * ((j : ℝ) ^ 2 - 4) := mul_nonneg (sq_nonneg _) (by linarith)
  nlinarith

/-- The inverse and its norm are constructed from the actual tail form,
rather than supplied as hypotheses. -/
theorem exists_outerPhysicalDirichletInverse
    {D : ReferenceData} {T : DeepTailData} {right : Bool} {j start : ℕ}
    (hD : IsAccumulatingProfile D) (hT : DeepTailHypotheses T)
    (hphysical : TailPhysicalRelation D T right j start) (hj : 2 ≤ j)
    (hη : T.η ≤ 1 / 10) (hK : 10 * tailSmoothStepConstant + 2 ≤ T.K) :
    ∃ A : OuterPhysicalTailL2 D T right →L[ℝ] OuterPhysicalTailL2 D T right,
      ‖A‖ ≤ 64 / (j : ℝ) ^ 4 ∧
      (∀ f, OuterPhysicalDirichletGraph hD hphysical (A f) f) ∧
      (∀ u f, OuterPhysicalDirichletGraph hD hphysical u f → A f = u) := by
  obtain ⟨G, hGn, hGe, hGu⟩ :=
    exists_tailDeepInverse T hT hη hK T.endpoint (Or.inl rfl)
  refine ⟨outerPhysicalDirichletInverse hD hphysical G, ?_, ?_, ?_⟩
  · calc
      _ ≤ 12 * (4 / T.Λ) := outerPhysicalDirichletInverse_norm_le hD hphysical G
        (div_nonneg (by norm_num) hT.2.2.1.le) hGn
      _ = 48 / T.Λ := by ring
      _ = 48 / ((j : ℝ) ^ 2 * ((j : ℝ) ^ 2 - 1)) := by rw [hphysical.1]
      _ ≤ _ := deepTail_physical_frequency_bound hj
  · intro f
    unfold OuterPhysicalDirichletGraph
    rw [outerPhysicalDirichletInverse_apply]
    exact hGe _
  · intro u f hu
    apply (outerPhysicalTailEquiv hD hphysical).injective
    rw [outerPhysicalDirichletInverse_apply]
    exact hGu _ _ hu

/-- The transported operator is the manuscript's B_j=-varpi^{-1}L_j
on every smooth local representative. -/
theorem outerPhysical_B_source_identity
    {D : ReferenceData} {T : DeepTailData} {right : Bool} {j start : ℕ}
    {V : ℝ → ℝ} {x : ℝ}
    (hD : IsAccumulatingProfile D) (hphysical : TailPhysicalRelation D T right j start)
    (hV : ContDiffAt ℝ 2 V x) (hx : x ∈ Ioo T.entrance T.endpoint) :
    -(tailPhysicalRadius right x ^ 2 /
        (12 * D.w (tailPhysicalRadius right x))) *
      radialJacobi ((j : ℝ) ^ 2) D.w (tailPhysicalLift D right j V)
        (tailPhysicalRadius right x) =
      outerLogGauge D right j x / 12 *
        (-(T.p x)⁻¹ * deriv (fun y => T.p y * deriv V y) x - T.Λ * V x) := by
  obtain ⟨C, hC⟩ := hD
  have hw : D.w (tailPhysicalRadius right x) ≠ 0 :=
    (hC.1.2.2.2.2.1 _ (hphysical.2.2.1 x hx).1).ne'
  rw [tailPhysicalSourceIdentity_at_of_relation ⟨C, hC⟩ hphysical hV
    (fun y _ => tailPhysicalLift_radius D right j V y) hx,
    outerLogGauge_eq_rpow]
  change -(tailPhysicalRadius right x ^ 2 / (12 * D.w (tailPhysicalRadius right x))) *
    (-((tailPhysicalRadius right x / tailPhysicalEndpoint D right) ^ ((j : ℝ) ^ 2) *
      D.w (tailPhysicalRadius right x) / tailPhysicalRadius right x ^ 2) *
        (-(T.p x)⁻¹ * deriv (fun y => T.p y * deriv V y) x - T.Λ * V x)) = _
  field_simp [hw, (tailPhysicalRadius_pos right x).ne'] <;> ring

end ContinuousFlexibility.Radial
