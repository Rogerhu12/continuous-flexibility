module

public import ContinuousFlexibility.Analysis.N07aPhysicalLpFamilyTame
public import ContinuousFlexibility.Analysis.N07aAngularPrimitiveOn

/-!
# Actual parameter towers for the odd coefficient's even primitive

Each cylinder coordinate is either the fixed bounded angular-integration
map applied to an original L² jet, or the original jet with one fewer
angular derivative. The closed Sobolev graphs then give the genuine height
tower, with the original one-high base and loss.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set MeasureTheory
open scoped ContDiff BigOperators
open ContinuousFlexibility.Statements

variable {E : Type*} [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
  [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [FirstCountableTopology E]
  {D : ReferenceData} {T : MaterialData} {A : SobolevModelData} {γ δ : ℝ}
  {U : Set E} {p : ℕ → Seminorm ℝ E} {base loss : ℕ} {g : E → A.Space}

/-- Coordinatewise one-high estimates imply the same estimate in the
original Sobolev grading. Only the finite product norm changes its constant. -/
theorem n07a_sobolevFamily_fixedTame_of_coordinateBounds
    (hA : IsSobolevModel D T γ A) (hU : IsOpen U)
    (J : ∀ s (j : JetIndex s), SmoothDirections U (fun x => ((g x).val s).val j))
    (hJ : ∀ k s (j : JetIndex s), ∃ B : ℝ, 0 ≤ B ∧
      ∀ x ∈ U, ∀ v : Fin k → E,
        ‖(J s j).D k x v‖ ≤ B * oneHighVariationWeight p base (s + loss) x v) :
    FixedNeighborhoodSmoothTame p A.grading U base loss g := by
  classical
  apply fixedNeighborhoodSmoothTame_of_uniform (n07aSobolevParameterTower hA hU J)
  intro k s _
  let L := (PiLp.continuousLinearEquiv 2 ℝ
    (fun _ : JetIndex s => CylinderL2)).symm.toContinuousLinearMap
  let B : JetIndex s → ℝ := fun j => (hJ k s j).choose
  have hB (j : JetIndex s) : 0 ≤ B j := (hJ k s j).choose_spec.1
  have hb (j : JetIndex s) := (hJ k s j).choose_spec.2
  refine ⟨‖L‖ * ∑ j, B j,
    mul_nonneg (norm_nonneg _) (Finset.sum_nonneg fun j _ => hB j), fun x hx v => ?_⟩
  let V := oneHighVariationWeight p base (s + loss) x v
  have hV : 0 ≤ V := by dsimp only [V]; unfold oneHighVariationWeight; positivity
  have hsum : 0 ≤ ∑ j, B j := Finset.sum_nonneg fun j _ => hB j
  have hcoord (j : JetIndex s) :
      ‖(((n07aSobolevParameterTower hA hU J).D k x v).val s).val j‖ ≤
        (∑ j, B j) * V := by
    rw [n07aSobolevParameterTower_D_coordinate hA hU J k hx v s j]
    exact (hb j x hx v).trans (mul_le_mul_of_nonneg_right
      (Finset.single_le_sum (fun j _ => hB j) (Finset.mem_univ j)) hV)
  change A.grading s ((n07aSobolevParameterTower hA hU J).D k x v) ≤
    (‖L‖ * ∑ j, B j) * V
  exact (n07a_sobolevGrading_le_coordinate_bound hA _ s
    (mul_nonneg hsum hV) hcoord).trans_eq (by dsimp only [L]; ring)

variable {f : E → PolarPoint → ℝ}
  (hT : IsMaterialData D T) (hA : IsSobolevModel D T γ A)
  (hU : IsOpen U) (hp : WithSeminorms p) (hmono : Monotone p)
  (hf : ∀ x ∈ U, ContDiffOn ℝ ∞ (f x) (annularOpen D))
  (hg : ∀ x ∈ U, A.decode (g x) = scalarAngularPrimitive (f x))
  (J : ∀ a b (q : annularOpen D),
    SmoothDirections U (fun x => mixedDerivative a b (f x) q.val))
  (hJ : ∀ k s : ℕ, ∃ B : ℝ, 0 ≤ B ∧
    ∀ (a b : ℕ) (q : annularOpen D), a + b ≤ s →
      ∀ x ∈ U, ∀ v : Fin k → E,
        |(J a b q).D k x v| ≤ B * T.H q.val.1 ^ δ *
          oneHighVariationWeight p base (s + loss) x v)
  (hγδ : γ < δ)

include hT hA hU hp hmono hf hg J hJ hγδ in
private theorem n07a_primitive_coordinate_uniformTower (s : ℕ) (j : JetIndex s) :
    ∃ K : SmoothDirections U (fun x => ((g x).val s).val j),
      ∀ k : ℕ, ∃ B : ℝ, 0 ≤ B ∧ ∀ x ∈ U, ∀ v : Fin k → E,
        ‖K.D k x v‖ ≤ B * oneHighVariationWeight p base (s + loss) x v := by
  classical
  let a := (j.val 0).val
  let b := (j.val 1).val
  let c := (j.val 2).val
  obtain ⟨f₀, K, hKae, hKb⟩ := n07a_physicalJetLp_uniformTower hT hU hp hf J hJ hγδ
    a (b - 1) c
  let M : CylinderL2 →L[ℝ] CylinderL2 :=
    if b = 0 then n07aAngularPrimitiveLp else ContinuousLinearMap.id ℝ CylinderL2
  have hM (u : CylinderL2) : ‖M u‖ ≤ Real.pi * ‖u‖ := by
    dsimp only [M]
    split_ifs
    · exact n07aAngularPrimitiveLp_norm_le u
    · simpa only [ContinuousLinearMap.id_apply] using
        le_mul_of_one_le_left (norm_nonneg u) (by linarith [Real.one_le_pi_div_two])
  have hvalue (x : E) (hx : x ∈ U) : M (f₀ x) = ((g x).val s).val j := by
    have hmem : MemLp (weightedPhysicalJet T γ a (b - 1) c (f x))
        2 materialCylinderMeasure := (memLp_congr_ae (hKae x hx)).mp (Lp.memLp (f₀ x))
    have hrep : f₀ x = hmem.toLp (weightedPhysicalJet T γ a (b - 1) c (f x)) :=
      Lp.ext ((hKae x hx).trans hmem.coeFn_toLp.symm)
    have hcoord := n07a_sobolev_coordinate_ae hT hA (g x) s j
    rw [hg x hx] at hcoord
    change (((g x).val s).val j : PolarPoint → ℝ) =ᵐ[materialCylinderMeasure]
      weightedPhysicalJet T γ a b c (scalarAngularPrimitive (f x)) at hcoord
    cases hb : b with
    | zero =>
        have hmem₀ : MemLp (weightedPhysicalJet T γ a 0 c (f x))
            2 materialCylinderMeasure := by simpa only [hb, Nat.zero_sub] using hmem
        have hrep₀ : f₀ x = hmem₀.toLp (weightedPhysicalJet T γ a 0 c (f x)) := by
          simpa only [hb, Nat.zero_sub] using hrep
        simp only [M, hb, ite_true]
        rw [hrep₀, n07aAngularPrimitiveLp_toLp (contDiff_weightedPhysicalJet hT (hf x hx) a 0 c)]
        apply Lp.ext
        have he := (scalarAngularPrimitive_memLp_and_norm_le
          (contDiff_weightedPhysicalJet hT (hf x hx) a 0 c) hmem₀).1.coeFn_toLp
        rw [hb, n07a_weightedPhysicalJet_scalarAngularPrimitive_zero hT (hf x hx)] at hcoord
        exact he.trans hcoord.symm
    | succ b₀ =>
        simp only [M, hb, Nat.succ_ne_zero, ite_false, ContinuousLinearMap.id_apply]
        apply Lp.ext
        rw [hb,
          n07a_weightedPhysicalJet_scalarAngularPrimitive_succ hT (hf x hx)] at hcoord
        exact (hKae x hx).trans (by simpa only [hb, Nat.add_sub_cancel] using hcoord.symm)
  let K' := (smoothDirectionsScalarPostcompose K M).congr hvalue
  refine ⟨K', fun k => ?_⟩
  obtain ⟨B, hB, hBb⟩ := hKb k
  refine ⟨Real.pi * B, mul_nonneg Real.pi_pos.le hB, fun x hx v => ?_⟩
  have hord : a + (b - 1) + loss ≤ s + loss := by
    have hj := j.property
    dsimp only [a, b]
    omega
  have hw := n07a_oneHighVariationWeight_mono hmono base hord x v
  change ‖(smoothDirectionsScalarPostcompose K M).D k x v‖ ≤ _
  rw [smoothDirectionsScalarPostcompose_apply]
  calc
    _ ≤ Real.pi * ‖K.D k x v‖ := hM _
    _ ≤ Real.pi * (B * oneHighVariationWeight p base (a + (b - 1) + loss) x v) :=
      mul_le_mul_of_nonneg_left (hBb x hx v) Real.pi_pos.le
    _ ≤ Real.pi * (B * oneHighVariationWeight p base (s + loss) x v) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hw hB) Real.pi_pos.le
    _ = _ := by ring

include hT hA hU hp hmono hf hg J hJ hγδ in
/-- The original odd physical family yields the actual even primitive
height family, with exactly the original fixed base and derivative loss. -/
theorem n07a_primitiveHeightFamily_fixedNeighborhoodSmoothTame :
    FixedNeighborhoodSmoothTame p A.grading U base loss g := by
  classical
  let K : ∀ s (j : JetIndex s), SmoothDirections U (fun x => ((g x).val s).val j) :=
    fun s j => (n07a_primitive_coordinate_uniformTower hT hA hU hp hmono hf hg J hJ hγδ s j).choose
  apply n07a_sobolevFamily_fixedTame_of_coordinateBounds hA hU K
  intro k s j
  exact (n07a_primitive_coordinate_uniformTower hT hA hU hp hmono hf hg J hJ hγδ s j).choose_spec k

end ContinuousFlexibility.Analysis
