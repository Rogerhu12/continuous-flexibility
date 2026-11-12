import ContinuousFlexibility.Analysis.N01cActualControlAssembly
import ContinuousFlexibility.Analysis.N01aMaterialContext
import ContinuousFlexibility.Analysis.N01aOpticalProfile

/-!
# Assembling the actual reference and control geometry

The actual construction supplies a component enumeration with bounded
host-index discrepancy and the pointwise primitive optical bound. The
material data, spaces, controls and reference state are then constructed
on that same reference and its actual host cells.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open Set
open scoped ContDiff

theorem n01aStatement_of_quantitative_reference (D : RadialReference)
    (hprimitive : N01RadialPrimitiveGeometry D.val)
    (henumerate : ∀ host : N01aNegativeComponent D.val → ℕ,
      (∀ J, J.interval ⊆ D.val.cells (host J)) →
      ∃ e : ℕ ≃ N01aNegativeComponent D.val, ∃ B : ℝ, 0 < B ∧ ∀ m,
        |(D.val.cellIndex (host (e m)) : ℝ) - D.val.cellIndex m| ≤ B)
    (hheight : ∀ sample : ℕ → ℝ,
      HeightMember D.val (affineMaterialData D.val sample) referenceBeta
        (fun p : PolarPoint => D.val.phi p.1 * Radial.cosineMode 2 p.2))
    (hW02 : W02Statement) : Blueprint.N01aStatement := by
  classical
  have hD := D.property
  obtain ⟨sample, hT, hsample, _⟩ := exists_n01a_affineMaterialData hD.1
  let T : MaterialData := affineMaterialData D.val sample
  obtain ⟨S, hS⟩ := hW02 D.val T hD.1 hT
  have hE : ∀ r ∈ Ioo D.val.a D.val.b, 1 ≤ T.E0 r := by
    obtain ⟨A, K, _, _, hlog⟩ := affineMaterialData_cell_log_bounds (sample := sample) hD.1
    intro r hr
    obtain ⟨m, hm⟩ := radialPartition_exists_cell hD.1.choose_spec.2.1 hr
    have hp : 0 < T.E0 r := (hT.2.1 r hr).2.2.1
    have he := Real.exp_le_exp.mpr (zero_le_one.trans (hlog m r hm).1)
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
  exact ⟨D, T, S, C, hC⟩

end ContinuousFlexibility.Statements
