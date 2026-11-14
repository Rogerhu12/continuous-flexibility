module

public import ContinuousFlexibility.Analysis.MaterialHeightRegularity
public import ContinuousFlexibility.Analysis.SpacesSmoothEvaluation
public import Mathlib.Topology.Baire.CompleteMetrizable

/-!
# Flat physical heights, including smooth parameter families

Individual heights already extend smoothly by the weighted endpoint
estimates. The weak-graph levels are closed Hilbert subspaces, so their
projective limit is a Fréchet space. Its continuous linear pointwise
decoding therefore satisfies the barrelled-space evaluation theorem.
Applying that theorem to the derivative tower in `SmoothTameOn` proves
joint smoothness on the original parameter interval.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Statements

open Set ContinuousFlexibility.Analysis
open scoped Topology ContDiff

set_option backward.isDefEq.respectTransparency false

/-- Pointwise decoding with the continuity required in the model statement. -/
def spaces_heightDecode {D : ReferenceData} {T : MaterialData} {γ : ℝ}
    (H : SobolevModelData) (hH : IsSobolevModel D T γ H) :
    H.Space →L[ℝ] (PolarPoint → ℝ) where
  toLinearMap := H.decode
  cont := hH.2.2.1

@[simp] theorem spaces_heightDecode_apply {D : ReferenceData} {T : MaterialData} {γ : ℝ}
    (H : SobolevModelData) (hH : IsSobolevModel D T γ H) (u : H.Space) :
    spaces_heightDecode H hH u = H.decode u := rfl

/-- A smooth tame curve of heights and endpoint constants gives a jointly
smooth physical height on the same, unshrunk parameter interval. -/
theorem spaces_physical_height_family_contDiff
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    {γ q₀ : ℝ} (hγ : 0 < γ)
    (c : ℝ → (S.height γ).Space × ℝ)
    (hc : SmoothTameOn realGrading (pairGrading (S.height γ).grading realGrading)
      (Ioo (-q₀) q₀) c) :
    ContDiffOn ℝ ∞ (fun p : PolarPoint × ℝ =>
      (S.height γ).decode (c p.2).1 p.1 + (c p.2).2 * S.chiLeft p.1.1)
      (univ ×ˢ Ioo (-q₀) q₀) := by
  let : ∀ s, CompleteSpace ((S.height γ).level s) :=
    fun s => ((hS.1 γ).2.1 s).isComplete.completeSpace_coe
  let : IsUniformAddGroup (S.height γ).Space :=
    (compatibleSubmodule (fun s => (S.height γ).level s)
      (S.height γ).bond).toAddSubgroup.isUniformAddGroup
  let E := (S.height γ).Space × ℝ
  let L (p : PolarPoint) : E →L[ℝ] ℝ :=
    ((ContinuousLinearMap.proj p).comp (spaces_heightDecode (S.height γ) (hS.1 γ))).comp
      (ContinuousLinearMap.fst ℝ (S.height γ).Space ℝ) +
      (ContinuousLinearMap.snd ℝ (S.height γ).Space ℝ).smulRight (S.chiLeft p.1)
  have hLapp (p : PolarPoint) (u : E) :
      L p u = (S.height γ).decode u.1 p + u.2 * S.chiLeft p.1 := by
    have hfst : ContinuousLinearMap.fst ℝ (S.height γ).Space ℝ u = u.1 :=
      congrFun (ContinuousLinearMap.coe_fst' (R := ℝ)
        (M₁ := (S.height γ).Space) (M₂ := ℝ)) u
    have hsnd : ContinuousLinearMap.snd ℝ (S.height γ).Space ℝ u = u.2 :=
      congrFun (ContinuousLinearMap.coe_snd' (R := ℝ)
        (M₁ := (S.height γ).Space) (M₂ := ℝ)) u
    simp only [L, add_apply, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.proj_apply, spaces_heightDecode_apply,
      ContinuousLinearMap.smulRight_apply, smul_eq_mul]
    exact congrArg₂ (fun (v : (S.height γ).Space) (r : ℝ) =>
      (S.height γ).decode v p + r * S.chiLeft p.1) hfst hsnd
  have hL : ∀ u : E, ContDiff ℝ ∞ (fun p => L p u) := by
    intro u
    simpa only [hLapp] using physical_height_with_cutoff_contDiff hT hS hγ u.1 u.2
  obtain ⟨J, _⟩ := hc
  let a (k : ℕ) (t : ℝ) : E := J.D k t (fun _ => 1)
  have ha (k : ℕ) : ContinuousOn (a k) (Ioo (-q₀) q₀) :=
    (J.continuous k).comp (continuousOn_id.prodMk continuousOn_const)
      (fun _ ht => ⟨ht, mem_univ _⟩)
  have ha₀ : ∀ t ∈ Ioo (-q₀) q₀, a 0 t = c t := by
    intro t ht
    have hempty : (fun _ : Fin 0 => (1 : ℝ)) = Fin.elim0 := by
      funext i
      exact i.elim0
    simpa only [a, hempty] using J.zero t ht
  have had (k : ℕ) (t : ℝ) (ht : t ∈ Ioo (-q₀) q₀) :
      HasProjectiveCurveDerivAt (a k) (a (k + 1) t) t := by
    have h := J.derivative k t ht (fun _ => 1) 1
    have hcons : Fin.cons (α := fun _ : Fin (k + 1) => ℝ) 1 (fun _ => 1) =
        (fun _ : Fin (k + 1) => (1 : ℝ)) := by
      funext i
      exact Fin.cases (Fin.cons_zero _ _) (fun j => Fin.cons_succ _ _ j) i
    simpa only [a, HasProjectiveLineDerivAt, HasProjectiveCurveDerivAt, zero_add,
      zero_smul, add_zero, smul_eq_mul, mul_one, hcons] using h
  have h := spaces_contDiffOn_evaluation_curve L hL isOpen_Ioo a ha had
  apply h.congr
  intro p hp
  rw [ha₀ p.2 hp.2, hLapp]

/-- W03, with the genuine smooth zero extension and the original parameter
interval in all three clauses of the frozen statement. -/
theorem spaces_W03_statement : W03Statement := by
  intro D T S _ hT hS
  refine ⟨?_, ?_, ?_⟩
  · intro γ hγ u
    exact physical_height_contDiff_and_flatJets hT hS hγ u
  · intro γ hγ u c
    exact physical_height_with_cutoff_contDiff hT hS hγ u c
  · intro γ q₀ hγ _ c hc
    exact spaces_physical_height_family_contDiff hT hS hγ c hc

end ContinuousFlexibility.Statements
