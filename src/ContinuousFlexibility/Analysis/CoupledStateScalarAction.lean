module

public import ContinuousFlexibility.Statements.Nonlinear

/-!
# Scalar action through the canonical module structure

The generic definition fixes the usual module action before specializing
to the nested physical state spaces. Its projection and continuity lemmas
avoid repeated low-level scalar-action instance searches on those spaces.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter
open scoped Topology

section Algebra

variable {E F : Type*} [AddCommGroup E] [Module ℝ E]
  [AddCommGroup F] [Module ℝ F]

def coupledScalarAction (t : ℝ) (v : E) : E := t • v

theorem coupledScalarAction_zero (t : ℝ) : coupledScalarAction t (0 : E) = 0 :=
  smul_zero t

theorem coupledScalarAction_zero_scalar (v : E) : coupledScalarAction (0 : ℝ) v = 0 :=
  zero_smul ℝ v

theorem coupledScalarAction_fst (t : ℝ) (v : E × F) :
    (coupledScalarAction t v).1 = coupledScalarAction t v.1 := by
  simp only [coupledScalarAction, Prod.smul_fst]

theorem coupledScalarAction_snd (t : ℝ) (v : E × F) :
    (coupledScalarAction t v).2 = coupledScalarAction t v.2 := by
  simp only [coupledScalarAction, Prod.smul_snd]

theorem coupledScalarAction_prod_mk (t : ℝ) (x : E) (y : F) :
    coupledScalarAction t (x, y) = (coupledScalarAction t x, coupledScalarAction t y) := by
  simp only [coupledScalarAction, Prod.smul_mk]

theorem coupledScalarAction_subtype_val (W : Submodule ℝ E) (t : ℝ) (v : W) :
    (coupledScalarAction t v).val = coupledScalarAction t v.val := by
  simp only [coupledScalarAction, Submodule.coe_smul]

theorem coupledScalarAction_map (L : E →ₗ[ℝ] F) (t : ℝ) (v : E) :
    L (coupledScalarAction t v) = coupledScalarAction t (L v) :=
  L.map_smul t v

theorem coupledScalarAction_linear_eval {ι : Type*}
    (L : E →ₗ[ℝ] (ι → ℝ)) (t : ℝ) (v : E) (i : ι) :
    L (coupledScalarAction t v) i = t * L v i := by
  simp only [coupledScalarAction, map_smul, Pi.smul_apply, smul_eq_mul]

end Algebra

theorem coupledScalarAction_real (t v : ℝ) : coupledScalarAction t v = t * v :=
  smul_eq_mul t v

section Topology

variable {E : Type*} [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
  [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]

theorem coupledScalarAction_continuous_line (x v : E) :
    Continuous (fun t : ℝ => x + coupledScalarAction t v) :=
  continuous_const.add (continuous_id.smul continuous_const)

theorem coupledScalarAction_eventually_line_mem
    {U : Set E} (hU : IsOpen U) {x : E} (hx : x ∈ U) (v : E) :
    ∀ᶠ t : ℝ in 𝓝 0, x + coupledScalarAction t v ∈ U := by
  have hc : ContinuousAt (fun t : ℝ => x + coupledScalarAction t v) (0 : ℝ) :=
    (coupledScalarAction_continuous_line x v).continuousAt
  have hline : Tendsto (fun t : ℝ => x + coupledScalarAction t v) (𝓝 0) (𝓝 x) := by
    simpa only [coupledScalarAction_zero_scalar, add_zero] using hc.tendsto
  exact hline.eventually (hU.mem_nhds hx)

end Topology

end ContinuousFlexibility.Analysis
