import ContinuousFlexibility.Analysis.SmoothCompactL2Density
import ContinuousFlexibility.Scalar.WeightedAngularPrimitiveL2
import Mathlib.Analysis.Normed.Operator.Extend

/-!
# The actual angular primitive as a cylinder L² operator

The previously proved integral estimate defines a bounded linear map on
smooth square-integrable fields. Its extension to the actual cylinder
L² space retains the integral formula for every smooth representative.
This is the fixed operator used on the genuine parameter towers of the
mixed coefficient; no parameter derivative is exchanged with an integral.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set MeasureTheory
open scoped ContDiff
open ContinuousFlexibility.Statements

set_option backward.isDefEq.respectTransparency false

/-- Actual smooth fields before passage to their L² classes. -/
def n07aSmoothCylinderFields : Submodule ℝ (PolarPoint → ℝ) where
  carrier := {f | ContDiff ℝ ∞ f ∧ MemLp f 2 materialCylinderMeasure}
  zero_mem' := ⟨contDiff_const, MemLp.zero⟩
  add_mem' := fun hf hg => ⟨hf.1.add hg.1, hf.2.add hg.2⟩
  smul_mem' := fun c f hf => ⟨contDiff_const.smul hf.1, hf.2.const_smul c⟩

/-- The quotient map is kept separate from the physical integral map. -/
def n07aSmoothCylinderToLp : n07aSmoothCylinderFields →ₗ[ℝ] CylinderL2 where
  toFun f := f.property.2.toLp f.val
  map_add' f g := MemLp.toLp_add f.property.2 g.property.2
  map_smul' c f := MemLp.toLp_const_smul c f.property.2

theorem n07aSmoothCylinderToLp_apply (f : n07aSmoothCylinderFields) :
    n07aSmoothCylinderToLp f = f.property.2.toLp f.val := rfl

/-- The original angular integral, acting on smooth representatives. -/
def n07aSmoothCylinderPrimitive : n07aSmoothCylinderFields →ₗ[ℝ] CylinderL2 where
  toFun f := (scalarAngularPrimitive_memLp_and_norm_le f.property.1 f.property.2).1.toLp
    (scalarAngularPrimitive f.val)
  map_add' f g := by
    apply Lp.ext
    filter_upwards
      [(scalarAngularPrimitive_memLp_and_norm_le (f + g).property.1
        (f + g).property.2).1.coeFn_toLp,
        (scalarAngularPrimitive_memLp_and_norm_le f.property.1 f.property.2).1.coeFn_toLp,
        (scalarAngularPrimitive_memLp_and_norm_le g.property.1 g.property.2).1.coeFn_toLp,
        Lp.coeFn_add
          ((scalarAngularPrimitive_memLp_and_norm_le f.property.1 f.property.2).1.toLp _)
          ((scalarAngularPrimitive_memLp_and_norm_le g.property.1 g.property.2).1.toLp _)]
      with p hfg hf hg hadd
    rw [hfg, hadd]
    simp only [Pi.add_apply, hf, hg]
    exact congrFun (scalarAngularPrimitive_add f.property.1.continuous
      g.property.1.continuous) p
  map_smul' c f := by
    apply Lp.ext
    filter_upwards
      [(scalarAngularPrimitive_memLp_and_norm_le (c • f).property.1
        (c • f).property.2).1.coeFn_toLp,
        (scalarAngularPrimitive_memLp_and_norm_le f.property.1 f.property.2).1.coeFn_toLp,
        Lp.coeFn_smul c
          ((scalarAngularPrimitive_memLp_and_norm_le f.property.1 f.property.2).1.toLp _)]
      with p hcf hf hsmul
    simp only [RingHom.id_apply, hcf, hsmul, Pi.smul_apply, smul_eq_mul, hf]
    simpa only [Submodule.coe_smul, Pi.smul_def, smul_eq_mul] using
      congrFun (scalarAngularPrimitive_const_mul c f.val) p

theorem n07aSmoothCylinderPrimitive_apply (f : n07aSmoothCylinderFields) :
    n07aSmoothCylinderPrimitive f =
      (scalarAngularPrimitive_memLp_and_norm_le f.property.1 f.property.2).1.toLp
        (scalarAngularPrimitive f.val) := rfl

theorem n07aSmoothCylinderPrimitive_norm_le (f : n07aSmoothCylinderFields) :
    ‖n07aSmoothCylinderPrimitive f‖ ≤ Real.pi * ‖n07aSmoothCylinderToLp f‖ := by
  rw [n07aSmoothCylinderPrimitive_apply, n07aSmoothCylinderToLp_apply,
    Lp.norm_toLp, Lp.norm_toLp]
  exact (scalarAngularPrimitive_memLp_and_norm_le f.property.1 f.property.2).2

theorem n07aSmoothCylinderToLp_dense : DenseRange n07aSmoothCylinderToLp := by
  letI : IsFiniteMeasureOnCompacts materialCylinderMeasure := by
    unfold materialCylinderMeasure
    infer_instance
  have hd := smoothCompactL2Submodule_dense (μ := materialCylinderMeasure)
    isOpen_univ (Filter.Eventually.of_forall (fun _ => mem_univ _))
    (fun K hK _ => hK.measure_lt_top)
  apply hd.mono
  rintro u ⟨f, hf, _, _, hu⟩
  have hmem : MemLp f 2 materialCylinderMeasure := (memLp_congr_ae hu).mp (Lp.memLp u)
  refine ⟨⟨f, hf, hmem⟩, ?_⟩
  apply Lp.ext
  exact hmem.coeFn_toLp.trans hu.symm

/-- The genuine bounded angular-integration operator on cylinder L². -/
def n07aAngularPrimitiveLp : CylinderL2 →L[ℝ] CylinderL2 :=
  n07aSmoothCylinderPrimitive.extendOfNorm n07aSmoothCylinderToLp

theorem n07aAngularPrimitiveLp_toLp {f : PolarPoint → ℝ}
    (hf : ContDiff ℝ ∞ f) (hmem : MemLp f 2 materialCylinderMeasure) :
    n07aAngularPrimitiveLp (hmem.toLp f) =
      (scalarAngularPrimitive_memLp_and_norm_le hf hmem).1.toLp
        (scalarAngularPrimitive f) :=
  LinearMap.extendOfNorm_eq n07aSmoothCylinderToLp_dense
    ⟨Real.pi, n07aSmoothCylinderPrimitive_norm_le⟩ ⟨f, hf, hmem⟩

theorem n07aAngularPrimitiveLp_norm_le (u : CylinderL2) :
    ‖n07aAngularPrimitiveLp u‖ ≤ Real.pi * ‖u‖ :=
  LinearMap.norm_extendOfNorm_apply_le n07aSmoothCylinderToLp_dense Real.pi
    n07aSmoothCylinderPrimitive_norm_le u

theorem n07aAngularPrimitiveLp_opNorm_le : ‖n07aAngularPrimitiveLp‖ ≤ Real.pi :=
  LinearMap.opNorm_extendOfNorm_le n07aSmoothCylinderToLp_dense Real.pi_pos.le
    n07aSmoothCylinderPrimitive_norm_le

end ContinuousFlexibility.Analysis
