import ContinuousFlexibility.Radial.SimpleKernelBorderInverse
import ContinuousFlexibility.Radial.CentralRadialClosedGraph

/-!
# The central inverse with any nonorthogonal symmetric column

The actual central closed differential graph has a simple kernel and an
already constructed reduced inverse.  We apply the graph-level border
construction to any Hilbert-space column with nonzero kernel pairing.
The column may therefore be the actual compact metric variation, rather
than the earlier auxiliary bump.  Both inverse identities use the same
closed differential graph as the spectral construction.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open scoped InnerProductSpace RealInnerProductSpace

def centralColumnKernel (g : HermiteL2) : HermiteL2 :=
  (⟪centralRadialKernelVector, g⟫_ℝ)⁻¹ • centralRadialKernelVector

theorem centralColumnKernel_graph (g : HermiteL2) :
    (centralColumnKernel g, 0) ∈ centralRadialClosedGraph 2 := by
  have h := (centralRadialClosedGraph 2).smul_mem
    (⟪centralRadialKernelVector, g⟫_ℝ)⁻¹ centralRadialKernelVector_graph
  simpa only [Prod.smul_mk, smul_zero, centralColumnKernel] using h

theorem centralColumnKernel_pairing (g : HermiteL2)
    (hg : ⟪centralRadialKernelVector, g⟫_ℝ ≠ 0) :
    ⟪centralColumnKernel g, g⟫_ℝ = 1 := by
  rw [centralColumnKernel, real_inner_smul_left, inv_mul_cancel₀ hg]

theorem centralColumnKernel_source_compatible (g u f : HermiteL2)
    (hf : (u, f) ∈ centralRadialClosedGraph 2) :
    ⟪centralColumnKernel g, f⟫_ℝ = 0 := by
  rw [centralColumnKernel, real_inner_smul_left,
    real_inner_comm centralRadialKernelVector f,
    centralRadialClosedGraph_two_compat u f hf, mul_zero]

theorem centralColumnKernel_spans (g : HermiteL2)
    (hg : ⟪centralRadialKernelVector, g⟫_ℝ ≠ 0)
    (u : HermiteL2) (hu : (u, 0) ∈ centralRadialClosedGraph 2) :
    ∃ c : ℝ, u = c • centralColumnKernel g := by
  obtain ⟨a, ha⟩ := (centralRadialClosedGraph_two_kernel_iff u).mp hu
  refine ⟨a * ⟪centralRadialKernelVector, g⟫_ℝ, ?_⟩
  rw [centralColumnKernel, smul_smul, mul_assoc, mul_inv_cancel₀ hg, mul_one, ha]

theorem centralColumn_reduced_solves (g : HermiteL2)
    (hg : ⟪centralRadialKernelVector, g⟫_ℝ ≠ 0)
    (f : HermiteL2) (hf : ⟪centralColumnKernel g, f⟫_ℝ = 0) :
    (centralRadialReducedHilbertInverse f, f) ∈ centralRadialClosedGraph 2 := by
  rw [centralColumnKernel, real_inner_smul_left] at hf
  have horth := (mul_eq_zero.mp hf).resolve_left (inv_ne_zero hg)
  exact centralRadialReducedHilbertInverse_graph_compatible f
    ((real_inner_comm f centralRadialKernelVector).trans horth)

def centralColumnInverse (g : HermiteL2) :
    (HermiteL2 × ℝ) →L[ℝ] (HermiteL2 × ℝ) :=
  simpleKernelBorderInverse centralRadialReducedHilbertInverse (centralColumnKernel g) g

theorem centralColumnInverse_solves (g : HermiteL2)
    (hg : ⟪centralRadialKernelVector, g⟫_ℝ ≠ 0) (F : HermiteL2 × ℝ) :
    SimpleKernelBorderGraph (centralRadialClosedGraph 2) g
      (centralColumnInverse g F) F :=
  simpleKernelBorderInverse_solves (centralRadialClosedGraph 2)
    centralRadialReducedHilbertInverse (centralColumnKernel g) g
    (centralColumnKernel_graph g) (centralColumnKernel_pairing g hg)
    (centralColumn_reduced_solves g hg) F

theorem centralColumnInverse_unique (g : HermiteL2)
    (hg : ⟪centralRadialKernelVector, g⟫_ℝ ≠ 0)
    (U F : HermiteL2 × ℝ)
    (hU : SimpleKernelBorderGraph (centralRadialClosedGraph 2) g U F) :
    centralColumnInverse g F = U :=
  simpleKernelBorderInverse_unique (centralRadialClosedGraph 2)
    centralRadialReducedHilbertInverse (centralColumnKernel g) g
    (centralColumnKernel_graph g) (centralColumnKernel_pairing g hg)
    (centralColumn_reduced_solves g hg) (centralColumnKernel_source_compatible g)
    (centralColumnKernel_spans g hg) hU

/-- The norm is a finite constant depending only on the fixed column;
later isometric height transport preserves this same bound. -/
theorem centralColumnInverse_bounded (g : HermiteL2)
    (hg : ⟪centralRadialKernelVector, g⟫_ℝ ≠ 0) :
    ∃ C : ℝ, 0 < C ∧ ∃ G : (HermiteL2 × ℝ) →L[ℝ] (HermiteL2 × ℝ),
      ‖G‖ ≤ C ∧
      (∀ F, SimpleKernelBorderGraph (centralRadialClosedGraph 2) g (G F) F) ∧
      (∀ U F, SimpleKernelBorderGraph (centralRadialClosedGraph 2) g U F → G F = U) := by
  refine ⟨‖centralColumnInverse g‖ + 1, by positivity, centralColumnInverse g, ?_,
    centralColumnInverse_solves g hg, centralColumnInverse_unique g hg⟩
  exact le_add_of_nonneg_right (by norm_num)

end ContinuousFlexibility.Radial
