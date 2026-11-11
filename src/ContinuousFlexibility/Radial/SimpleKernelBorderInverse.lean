import Mathlib.Analysis.InnerProductSpace.LinearMap

/-!
# A symmetric border for a genuine simple-kernel graph

The column used in the central model need not be its original auxiliary
bump.  Any actual Hilbert-space column pairing to one with the kernel gives
a bounded, two-sided bordered inverse.  This permits the final metric
variation column to be inserted before cutting the central model.

The unbounded operator is a submodule of the product of its actual source
and target Hilbert spaces.  Its graph is not defined as the range of the
inverse.  The input reduced inverse solves precisely the sources orthogonal
to the kernel; no bordered inverse is an input.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open scoped RealInnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The symmetric block equation `(L u + c g, ⟪g,u⟫) = (f,t)`. -/
def SimpleKernelBorderGraph (L : Submodule ℝ (E × E)) (g : E)
    (U F : E × ℝ) : Prop :=
  (U.1, F.1 - U.2 • g) ∈ L ∧ ⟪g, U.1⟫_ℝ = F.2

/-- Remove the true kernel obstruction from a source. -/
def simpleKernelCorrectedSource (φ g : E) : E →L[ℝ] E :=
  ContinuousLinearMap.id ℝ E - (innerSL ℝ φ).smulRight g

theorem simpleKernelCorrectedSource_apply (φ g f : E) :
    simpleKernelCorrectedSource φ g f = f - ⟪φ, f⟫_ℝ • g := by
  simp only [simpleKernelCorrectedSource, ContinuousLinearMap.sub_apply,
    ContinuousLinearMap.id_apply, ContinuousLinearMap.smulRight_apply,
    innerSL_apply_apply]

theorem simpleKernelCorrectedSource_orthogonal (φ g : E)
    (hpair : ⟪φ, g⟫_ℝ = 1) (f : E) :
    ⟪φ, simpleKernelCorrectedSource φ g f⟫_ℝ = 0 := by
  rw [simpleKernelCorrectedSource_apply, inner_sub_right, real_inner_smul_right,
    hpair, mul_one, sub_self]

/-- Solve the orthogonal source, then add a kernel vector to prescribe
the row of the new border. -/
def simpleKernelBorderOutput (R : E →L[ℝ] E) (φ g : E) : (E × ℝ) →L[ℝ] E :=
  let A := (R.comp (simpleKernelCorrectedSource φ g)).comp
    (ContinuousLinearMap.fst ℝ E ℝ)
  A + ((ContinuousLinearMap.snd ℝ E ℝ) - (innerSL ℝ g).comp A).smulRight φ

def simpleKernelBorderInverse (R : E →L[ℝ] E) (φ g : E) :
    (E × ℝ) →L[ℝ] (E × ℝ) :=
  (simpleKernelBorderOutput R φ g).prod
    ((innerSL ℝ φ).comp (ContinuousLinearMap.fst ℝ E ℝ))

theorem simpleKernelBorderOutput_apply (R : E →L[ℝ] E) (φ g : E) (F : E × ℝ) :
    simpleKernelBorderOutput R φ g F =
      R (simpleKernelCorrectedSource φ g F.1) +
        (F.2 - ⟪g, R (simpleKernelCorrectedSource φ g F.1)⟫_ℝ) • φ := by
  simp only [simpleKernelBorderOutput, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.sub_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.fst_apply, ContinuousLinearMap.snd_apply,
    ContinuousLinearMap.smulRight_apply, innerSL_apply_apply]

theorem simpleKernelBorderInverse_apply (R : E →L[ℝ] E) (φ g : E) (F : E × ℝ) :
    simpleKernelBorderInverse R φ g F =
      (simpleKernelBorderOutput R φ g F, ⟪φ, F.1⟫_ℝ) := by
  simp only [simpleKernelBorderInverse, ContinuousLinearMap.prod_apply,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.fst_apply, innerSL_apply_apply]

/-- The constructed map solves the full symmetric bordered equation. -/
theorem simpleKernelBorderInverse_solves (L : Submodule ℝ (E × E))
    (R : E →L[ℝ] E) (φ g : E)
    (hφ : (φ, 0) ∈ L) (hpair : ⟪φ, g⟫_ℝ = 1)
    (hR : ∀ f : E, ⟪φ, f⟫_ℝ = 0 → (R f, f) ∈ L) (F : E × ℝ) :
    SimpleKernelBorderGraph L g (simpleKernelBorderInverse R φ g F) F := by
  have hbase := hR (simpleKernelCorrectedSource φ g F.1)
    (simpleKernelCorrectedSource_orthogonal φ g hpair F.1)
  have hsum := L.add_mem hbase (L.smul_mem
    (F.2 - ⟪g, R (simpleKernelCorrectedSource φ g F.1)⟫_ℝ) hφ)
  have hpair' : ⟪g, φ⟫_ℝ = 1 := (real_inner_comm g φ).trans hpair
  rw [simpleKernelBorderInverse_apply]
  constructor
  · rw [simpleKernelBorderOutput_apply, ← simpleKernelCorrectedSource_apply]
    simpa only [Prod.add_def, Prod.smul_mk, smul_zero, add_zero] using hsum
  · rw [simpleKernelBorderOutput_apply, inner_add_right,
      real_inner_smul_right, hpair', mul_one]
    ring

/-- Source compatibility determines the border scalar, including the sign. -/
theorem simpleKernelBorderGraph_scalar (L : Submodule ℝ (E × E)) (φ g : E)
    (hpair : ⟪φ, g⟫_ℝ = 1)
    (hcompat : ∀ u f : E, (u, f) ∈ L → ⟪φ, f⟫_ℝ = 0)
    {U F : E × ℝ} (hU : SimpleKernelBorderGraph L g U F) :
    U.2 = ⟪φ, F.1⟫_ℝ := by
  have h := hcompat U.1 (F.1 - U.2 • g) hU.1
  rw [inner_sub_right, real_inner_smul_right, hpair, mul_one] at h
  exact (sub_eq_zero.mp h).symm

/-- Uniqueness is in the original graph.  It uses its simple kernel,
not a domain imposed after the inverse has been constructed. -/
theorem simpleKernelBorderInverse_unique (L : Submodule ℝ (E × E))
    (R : E →L[ℝ] E) (φ g : E)
    (hφ : (φ, 0) ∈ L) (hpair : ⟪φ, g⟫_ℝ = 1)
    (hR : ∀ f : E, ⟪φ, f⟫_ℝ = 0 → (R f, f) ∈ L)
    (hcompat : ∀ u f : E, (u, f) ∈ L → ⟪φ, f⟫_ℝ = 0)
    (hker : ∀ u : E, (u, 0) ∈ L → ∃ c : ℝ, u = c • φ)
    {U F : E × ℝ} (hU : SimpleKernelBorderGraph L g U F) :
    simpleKernelBorderInverse R φ g F = U := by
  let V := simpleKernelBorderInverse R φ g F
  have hV : SimpleKernelBorderGraph L g V F :=
    simpleKernelBorderInverse_solves L R φ g hφ hpair hR F
  have hc : U.2 = V.2 :=
    (simpleKernelBorderGraph_scalar L φ g hpair hcompat hU).trans
      (simpleKernelBorderGraph_scalar L φ g hpair hcompat hV).symm
  have hd := L.sub_mem hU.1 hV.1
  have hd' : (U.1 - V.1, 0) ∈ L := by
    simpa only [Prod.sub_def, hc, sub_self] using hd
  obtain ⟨c, hdiff⟩ := hker (U.1 - V.1) hd'
  have hpair' : ⟪g, φ⟫_ℝ = 1 := (real_inner_comm g φ).trans hpair
  have hrow : ⟪g, U.1 - V.1⟫_ℝ = 0 := by
    rw [inner_sub_right, hU.2, hV.2, sub_self]
  rw [hdiff, real_inner_smul_right, hpair', mul_one] at hrow
  have hu : U.1 = V.1 := by
    rw [hrow, zero_smul] at hdiff
    exact sub_eq_zero.mp hdiff
  exact Prod.ext hu.symm hc.symm

/-- A graph-level existence theorem with a bounded linear inverse. -/
theorem exists_simpleKernelBorderInverse (L : Submodule ℝ (E × E))
    (R : E →L[ℝ] E) (φ g : E)
    (hφ : (φ, 0) ∈ L) (hpair : ⟪φ, g⟫_ℝ = 1)
    (hR : ∀ f : E, ⟪φ, f⟫_ℝ = 0 → (R f, f) ∈ L)
    (hcompat : ∀ u f : E, (u, f) ∈ L → ⟪φ, f⟫_ℝ = 0)
    (hker : ∀ u : E, (u, 0) ∈ L → ∃ c : ℝ, u = c • φ) :
    ∃ G : (E × ℝ) →L[ℝ] (E × ℝ),
      (∀ F, SimpleKernelBorderGraph L g (G F) F) ∧
      (∀ U F, SimpleKernelBorderGraph L g U F → G F = U) := by
  refine ⟨simpleKernelBorderInverse R φ g, ?_, ?_⟩
  · exact simpleKernelBorderInverse_solves L R φ g hφ hpair hR
  · intro U F hU
    exact simpleKernelBorderInverse_unique L R φ g hφ hpair hR hcompat hker hU

end ContinuousFlexibility.Radial
