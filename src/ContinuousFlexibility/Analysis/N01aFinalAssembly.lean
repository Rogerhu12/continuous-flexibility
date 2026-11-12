import ContinuousFlexibility.Analysis.N01aComponentEnumeration
import ContinuousFlexibility.Analysis.N01aControlGeometryAssembly
import ContinuousFlexibility.Analysis.N01aControlMaterialWeights
import ContinuousFlexibility.Analysis.N01aMaterialContext
import ContinuousFlexibility.Analysis.N01aOpticalProfile

/-!
# Assembling the quantitative reference and control geometry

This assembly consumes the actual height and good-point estimates proved
from the spare reference exponent. All controls, material data, physical
spaces, cell indices and travel derivatives are constructed here.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open Set
open scoped ContDiff

theorem n01aStatement_of_quantitative_reference (D : RadialReference)
    (hindex : ∀ m, m ≤ 2 * D.val.cellIndex m + 1)
    (hheight : ∀ sample : ℕ → ℝ,
      HeightMember D.val (affineMaterialData D.val sample) referenceBeta
        (fun p : PolarPoint => D.val.phi p.1 * Radial.cosineMode 2 p.2))
    (hgood : ∀ p : ℝ, p ∈ radialCore D.val → ∃ A c N₀ : ℝ, 0 < A ∧ 0 < c ∧
      ∀ N : ℝ, N₀ ≤ N → ∃ r : ℝ, r ∈ radialCore D.val ∧ p ≤ r ∧
        r ≤ D.val.b - (1 / 2 : ℝ) * Real.exp (-N ^ 2) ∧
        n01aJacobiEnergy D.val.phi r ≤ A * Real.exp (-c * N ^ 3))
    (hW02 : W02Statement) : Blueprint.N01aStatement := by
  classical
  have hD := D.property
  have hgeom : RadialProfileGeometry D.val := hD.1.choose_spec.1
  obtain ⟨sample, hT, hsample, _⟩ := exists_n01a_affineMaterialData hD.1
  let T : MaterialData := affineMaterialData D.val sample
  obtain ⟨S, hS⟩ := hW02 D.val T hD.1 hT
  obtain ⟨host, χ, hhost, hχ, hderiv, hjets⟩ :=
    exists_n01a_opticalControls_of_radialReference hD
      (l := fun J : N01aNegativeComponent D.val => J.left)
      (h := fun J : N01aNegativeComponent D.val => J.right)
      (fun J : N01aNegativeComponent D.val => J.property)
  obtain ⟨p, hp, hφ⟩ := hgeom.2.2.2.2.2.1
  obtain ⟨A, c, N₀, hA, hc, hpoints⟩ := hgood p hp
  obtain ⟨e, B, hB, he⟩ := exists_n01a_component_enumeration_linear_of_good_points
    hD.1 hD.2.2.1 hgeom.2.2.2.1.1 hD.2.1.1 hp
    (n01aJacobiEnergy_pos hφ) hA hc host hhost hpoints
  let χe : ℕ → ℝ → ℝ := fun m => χ (e m)
  have hraw : ∀ s : ℕ, ∃ C : ℝ, 0 < C ∧ ∀ m r, r ∈ (Set.univ : Set ℝ) →
      |iteratedDeriv s (χe m) r| ≤ C * radialE (D.val.cellIndex (host (e m))) ^ C := by
    intro s
    obtain ⟨C, hC, hbound⟩ := hjets s
    exact ⟨C, hC, fun m r _ => hbound (e m) r⟩
  have hmaterial := n01a_control_jets_affineMaterialData hD.1 hsample
    (fun m => D.val.cellIndex (host (e m))) hB.le he hindex χe (fun _ => Set.univ) hraw
  have hfinal : ∀ s : ℕ, ∃ C : ℝ, 0 < C ∧ ∀ m r,
      |iteratedDeriv s (χe m) r| ≤ C * T.E0 (T.sample m) ^ C := by
    intro s
    obtain ⟨C, hC, hbound⟩ := hmaterial s
    exact ⟨C, hC, fun m r => hbound m r (Set.mem_univ r)⟩
  obtain ⟨C, hC⟩ := exists_n01a_controlGeometry hD hT hS (hheight sample) e χe
    (fun m => hχ (e m)) (fun m => hderiv (e m)) hfinal
  exact ⟨D, T, S, C, hC⟩

end ContinuousFlexibility.Statements
