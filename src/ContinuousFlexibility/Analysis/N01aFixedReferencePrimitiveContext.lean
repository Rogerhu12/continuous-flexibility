import ContinuousFlexibility.Analysis.N01aFinalAssembly
import ContinuousFlexibility.Analysis.N01aReferenceHeight
import ContinuousFlexibility.Analysis.SpacesConclusion
import ContinuousFlexibility.Analysis.TameCalculusTheorem

/-!
# The actual material and control context on a fixed reference

The reference is an input throughout the material, space and control
constructions. The physical spaces use the proved tame-calculus theorem,
and the reference eigenfield membership is derived from this same radial
reference. The actual host cells and the primitive certificate are kept.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open Set
open scoped ContDiff

theorem n01a_exists_fixedReference_primitive_context (D : RadialReference)
    (hprimitive : N01RadialPrimitiveGeometry D.val)
    (henumerate : ∀ host : N01aNegativeComponent D.val → ℕ,
      (∀ J, J.interval ⊆ D.val.cells (host J)) →
      ∃ e : ℕ ≃ N01aNegativeComponent D.val, ∃ B : ℝ, 0 < B ∧ ∀ m,
        |(D.val.cellIndex (host (e m)) : ℝ) - D.val.cellIndex m| ≤ B) :
    ∃ T : MaterialData, ∃ S : PhysicalSpacesData, ∃ C : NonlinearGeometryData S,
      IsMaterialData D.val T ∧ IsPhysicalSpaces D.val T S ∧
      Blueprint.N01PartA D.val T S C ∧ Blueprint.N01PrimitiveGeometry D.val T S C ∧
      (∀ r ∈ Ioo D.val.a D.val.b, 1 ≤ T.E0 r) := by
  classical
  have hD := D.property
  have hheight := n01a_reference_heightMember hD
  have hW02 : W02Statement := spaces_W02_statement Analysis.h01Statement
  obtain ⟨sample, hT, hsample, _⟩ := exists_n01a_affineMaterialData hD.1
  let T : MaterialData := affineMaterialData D.val sample
  obtain ⟨S, hS⟩ := hW02 D.val T hD.1 hT
  have hE : ∀ r ∈ Ioo D.val.a D.val.b, 1 ≤ T.E0 r := by
    obtain ⟨A, K, _, _, hlog⟩ := affineMaterialData_cell_log_bounds (sample := sample) hD.1
    intro r hr
    obtain ⟨m, hm⟩ := radialPartition_exists_cell hD.1.choose_spec.2.1 hr
    have hp : 0 < T.E0 r := (hT.2.1 r hr).2.2.1
    have hl : 0 ≤ Real.log (T.E0 r) := zero_le_one.trans (hlog m r hm).1
    have he := Real.exp_le_exp.mpr hl
    simpa only [Real.exp_zero, Real.exp_log hp] using he
  obtain ⟨host, χ, hhost, hχ, hderiv, hjets⟩ :=
    exists_n01a_opticalControls_of_radialReference hD
      (l := fun J : N01aNegativeComponent D.val => J.left)
      (h := fun J : N01aNegativeComponent D.val => J.right)
      (fun J : N01aNegativeComponent D.val => J.property)
  obtain ⟨e, B, hB, he⟩ := henumerate host hhost
  let χe : ℕ → ℝ → ℝ := fun m => χ (e m)
  have hraw : ∀ s : ℕ, ∃ C : ℝ, 0 < C ∧ ∀ m r,
      |iteratedDeriv s (χe m) r| ≤ C * radialE (D.val.cellIndex (host (e m))) ^ C := by
    intro s
    obtain ⟨C, hC, hbound⟩ := hjets s
    exact ⟨C, hC, fun m r => hbound (e m) r⟩
  obtain ⟨C, hC⟩ := exists_n01c_controlGeometry_with_hosts hD hT hS
    (hheight sample) hE hprimitive host hhost e ⟨B, hB, he⟩ χe
    (fun m => hχ (e m)) (fun m => hderiv (e m)) hraw
  exact ⟨T, S, C, hC.1, hC.2.1, hC.2.2.1, hC.2.2.2, hE⟩

end ContinuousFlexibility.Statements
