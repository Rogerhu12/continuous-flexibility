import ContinuousFlexibility.Radial.SimpleKernelBorderInverse
import ContinuousFlexibility.Radial.CentralStatementBridges
import ContinuousFlexibility.Statements.RadialTargets

/-!
# The true column inverse for the ordinary central model

This construction acts in ordinary Lebesgue L² for the central
Schrodinger operator used in R09. It uses the original finite-Hermite
closed graph and the existing bridge to the frozen weak differential
graph. The radial weighted operator is not used here.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open scoped InnerProductSpace RealInnerProductSpace
open ContinuousFlexibility.Statements

/-- The genuine normalized Gaussian ground vector in ordinary Lebesgue L². -/
abbrev centralModelGroundVector : HermiteL2 :=
  hermiteL2Vector (by norm_num : (0 : ℝ) < 2) 0

theorem centralModelGroundVector_norm : ‖centralModelGroundVector‖ = 1 :=
  (hermiteL2Vector_orthonormal (by norm_num : (0 : ℝ) < 2)).norm_eq_one 0

theorem centralModelGroundVector_pairing (f : HermiteL2) :
    ⟪centralModelGroundVector, f⟫_ℝ = hermiteCoefficient 2 f 0 :=
  inner_hermiteL2Vector_left (by norm_num : (0 : ℝ) < 2) f 0

/-- Normalize the original kernel against this actual column. -/
def centralModelColumnKernel (g : HermiteL2) : HermiteL2 :=
  (⟪centralModelGroundVector, g⟫_ℝ)⁻¹ • centralModelGroundVector

theorem centralModelColumnKernel_graph (g : HermiteL2) :
    (centralModelColumnKernel g, 0) ∈
      centralClosedGraph (by norm_num : (0 : ℝ) < 2) := by
  apply (centralClosedGraph_two_kernel_iff _).mpr
  exact ⟨(⟪centralModelGroundVector, g⟫_ℝ)⁻¹, rfl⟩

theorem centralModelColumnKernel_pairing (g : HermiteL2)
    (hg : ⟪centralModelGroundVector, g⟫_ℝ ≠ 0) :
    ⟪centralModelColumnKernel g, g⟫_ℝ = 1 := by
  rw [centralModelColumnKernel, real_inner_smul_left, inv_mul_cancel₀ hg]

theorem centralModelColumnKernel_source_compatible (g u f : HermiteL2)
    (hf : (u, f) ∈ centralClosedGraph (by norm_num : (0 : ℝ) < 2)) :
    ⟪centralModelColumnKernel g, f⟫_ℝ = 0 := by
  rw [centralModelColumnKernel, real_inner_smul_left,
    centralModelGroundVector_pairing f, centralClosedGraph_two_source_compatible u f hf,
    mul_zero]

theorem centralModelColumnKernel_spans (g : HermiteL2)
    (hg : ⟪centralModelGroundVector, g⟫_ℝ ≠ 0)
    (u : HermiteL2)
    (hu : (u, 0) ∈ centralClosedGraph (by norm_num : (0 : ℝ) < 2)) :
    ∃ c : ℝ, u = c • centralModelColumnKernel g := by
  obtain ⟨a, ha⟩ := (centralClosedGraph_two_kernel_iff u).mp hu
  refine ⟨a * ⟪centralModelGroundVector, g⟫_ℝ, ?_⟩
  rw [centralModelColumnKernel, smul_smul, mul_assoc, mul_inv_cancel₀ hg, mul_one]
  exact ha

theorem centralModelColumn_reduced_solves (g : HermiteL2)
    (hg : ⟪centralModelGroundVector, g⟫_ℝ ≠ 0)
    (f : HermiteL2) (hf : ⟪centralModelColumnKernel g, f⟫_ℝ = 0) :
    (centralReducedHilbertInverse f, f) ∈
      centralClosedGraph (by norm_num : (0 : ℝ) < 2) := by
  rw [centralModelColumnKernel, real_inner_smul_left] at hf
  have horth := (mul_eq_zero.mp hf).resolve_left (inv_ne_zero hg)
  apply centralReducedHilbertInverse_graph f
  rwa [centralModelGroundVector_pairing] at horth

/-- The inverse is built from the previously proved reduced inverse of
the original central Schrodinger operator. -/
def centralModelColumnInverse (g : HermiteL2) :
    (HermiteL2 × ℝ) →L[ℝ] (HermiteL2 × ℝ) :=
  simpleKernelBorderInverse centralReducedHilbertInverse (centralModelColumnKernel g) g

/-- The existing R09 graph is exactly the graph used in the construction. -/
theorem centralModelColumn_borderedGraph_iff (g : HermiteL2) (U F : HermiteL2 × ℝ) :
    BorderedFullGraph (centralPotential 2) g true U F ↔
      SimpleKernelBorderGraph (centralClosedGraph (by norm_num : (0 : ℝ) < 2)) g U F := by
  simp only [BorderedFullGraph, if_pos (rfl : true = true), SimpleKernelBorderGraph,
    centralWeakSchrodingerGraph_iff (by norm_num : (0 : ℝ) < 2)]

theorem centralModelColumnInverse_solves (g : HermiteL2)
    (hg : ⟪centralModelGroundVector, g⟫_ℝ ≠ 0) (F : HermiteL2 × ℝ) :
    BorderedFullGraph (centralPotential 2) g true (centralModelColumnInverse g F) F := by
  apply (centralModelColumn_borderedGraph_iff g _ F).mpr
  exact simpleKernelBorderInverse_solves
    (centralClosedGraph (by norm_num : (0 : ℝ) < 2))
    centralReducedHilbertInverse (centralModelColumnKernel g) g
    (centralModelColumnKernel_graph g) (centralModelColumnKernel_pairing g hg)
    (centralModelColumn_reduced_solves g hg) F

theorem centralModelColumnInverse_unique (g : HermiteL2)
    (hg : ⟪centralModelGroundVector, g⟫_ℝ ≠ 0)
    (U F : HermiteL2 × ℝ)
    (hU : BorderedFullGraph (centralPotential 2) g true U F) :
    centralModelColumnInverse g F = U := by
  exact simpleKernelBorderInverse_unique
    (centralClosedGraph (by norm_num : (0 : ℝ) < 2))
    centralReducedHilbertInverse (centralModelColumnKernel g) g
    (centralModelColumnKernel_graph g) (centralModelColumnKernel_pairing g hg)
    (centralModelColumn_reduced_solves g hg) (centralModelColumnKernel_source_compatible g)
    (centralModelColumnKernel_spans g hg)
    ((centralModelColumn_borderedGraph_iff g U F).mp hU)

/-- A bounded continuous linear two-sided inverse in precisely the
ordinary dx weak graph appearing in BufferHypotheses. -/
theorem exists_centralModelColumnInverse (g : HermiteL2)
    (hg : ⟪centralModelGroundVector, g⟫_ℝ ≠ 0) :
    ∃ C : ℝ, 0 < C ∧
      ∃ G : (RadialL2 × ℝ) →L[ℝ] (RadialL2 × ℝ),
        ‖G‖ ≤ C ∧
        (∀ F, BorderedFullGraph (centralPotential 2) g true (G F) F) ∧
        (∀ U F, BorderedFullGraph (centralPotential 2) g true U F → G F = U) := by
  refine ⟨‖centralModelColumnInverse g‖ + 1, by positivity,
    centralModelColumnInverse g, ?_,
    centralModelColumnInverse_solves g hg, centralModelColumnInverse_unique g hg⟩
  exact le_add_of_nonneg_right (by norm_num)

end ContinuousFlexibility.Radial
