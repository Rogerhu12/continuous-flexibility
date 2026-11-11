import ContinuousFlexibility.Radial.InnerBorderPieceProjection
import Mathlib.Topology.Algebra.Module.ClosedSubmodule

/-!
# The genuine admissible Hilbert source space

In an unbordered mode the scalar coordinate is the kernel of the actual
continuous scalar projection. It is not an unrestricted extra source
coordinate. The inherited norm is exactly the physical Hilbert norm.
An optional physical support kernel restricts sources to the true inner
region while retaining the same measure.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open Set MeasureTheory
open scoped InnerProductSpace

variable {α : Type*} [MeasurableSpace α] (μ : Measure α)

/-- The actual scalar-zero closed subspace in an unbordered mode. -/
def innerAdmissibleSource (bordered : Bool) : ClosedSubmodule ℝ (InnerBorderL2 μ) :=
  if bordered then ⊤
  else ClosedSubmodule.comap (WithLp.sndL 2 ℝ (Lp ℝ 2 μ) ℝ) (⊥ : ClosedSubmodule ℝ ℝ)

theorem mem_innerAdmissibleSource (bordered : Bool) (F : InnerBorderL2 μ) :
    F ∈ innerAdmissibleSource μ bordered ↔ bordered = true ∨ F.snd = 0 := by
  cases bordered <;>
    simp only [innerAdmissibleSource, Bool.false_eq_true, eq_self_iff_true,
      ite_false, ite_true, ClosedSubmodule.mem_comap, ClosedSubmodule.mem_bot,
      WithLp.sndL_apply, false_or, true_or, ClosedSubmodule.mem_top]

abbrev InnerAdmissibleSource (bordered : Bool) := ↥(innerAdmissibleSource μ bordered)

/-- Isometric inclusion into the same actual physical Hilbert product. -/
def innerAdmissibleSourceInclusion (bordered : Bool) :
    InnerAdmissibleSource μ bordered →L[ℝ] InnerBorderL2 μ :=
  (innerAdmissibleSource μ bordered).toSubmodule.subtypeL

@[simp] theorem innerAdmissibleSourceInclusion_apply (bordered : Bool)
    (F : InnerAdmissibleSource μ bordered) :
    innerAdmissibleSourceInclusion μ bordered F = F.val := rfl

@[simp] theorem innerAdmissibleSourceInclusion_norm (bordered : Bool)
    (F : InnerAdmissibleSource μ bordered) :
    ‖innerAdmissibleSourceInclusion μ bordered F‖ = ‖F‖ := rfl

def innerAdmissibleSourceValue (bordered : Bool) :
    InnerAdmissibleSource μ bordered →L[ℝ] Lp ℝ 2 μ :=
  (WithLp.fstL 2 ℝ (Lp ℝ 2 μ) ℝ).comp (innerAdmissibleSourceInclusion μ bordered)

def innerAdmissibleSourceRow (bordered : Bool) :
    InnerAdmissibleSource μ bordered →L[ℝ] ℝ :=
  (WithLp.sndL 2 ℝ (Lp ℝ 2 μ) ℝ).comp (innerAdmissibleSourceInclusion μ bordered)

@[simp] theorem innerAdmissibleSourceValue_apply (bordered : Bool)
    (F : InnerAdmissibleSource μ bordered) :
    innerAdmissibleSourceValue μ bordered F = F.val.fst := rfl

@[simp] theorem innerAdmissibleSourceRow_apply (bordered : Bool)
    (F : InnerAdmissibleSource μ bordered) :
    innerAdmissibleSourceRow μ bordered F = F.val.snd := rfl

/-- The zero scalar is a proved property of every admissible source. -/
theorem innerAdmissibleSourceRow_unbordered (F : InnerAdmissibleSource μ false) :
    innerAdmissibleSourceRow μ false F = 0 := by
  rw [innerAdmissibleSourceRow_apply]
  simpa only [Bool.false_eq_true, false_or] using
    (mem_innerAdmissibleSource μ false F.val).mp F.property

/-- The physical support constraint is a second closed kernel, so
sources outside the actual inner region are not silently discarded. -/
def innerSupportedAdmissibleSource (s : Set α) (bordered : Bool) :
    ClosedSubmodule ℝ (InnerBorderL2 μ) :=
  innerAdmissibleSource μ bordered ⊓
    ClosedSubmodule.comap
      (((ContinuousLinearMap.id ℝ (Lp ℝ 2 μ)) - innerL2PieceProjection μ s).comp
        (WithLp.fstL 2 ℝ (Lp ℝ 2 μ) ℝ))
      (⊥ : ClosedSubmodule ℝ (Lp ℝ 2 μ))

theorem mem_innerSupportedAdmissibleSource (s : Set α) (bordered : Bool)
    (F : InnerBorderL2 μ) :
    F ∈ innerSupportedAdmissibleSource μ s bordered ↔
      (bordered = true ∨ F.snd = 0) ∧ innerL2PieceProjection μ s F.fst = F.fst := by
  simp only [innerSupportedAdmissibleSource, ClosedSubmodule.mem_inf,
    mem_innerAdmissibleSource, ClosedSubmodule.mem_comap, ClosedSubmodule.mem_bot,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.sub_apply,
    ContinuousLinearMap.id_apply, WithLp.fstL_apply, sub_eq_zero]
  exact and_congr_right (fun _ => eq_comm)

end ContinuousFlexibility.Radial
