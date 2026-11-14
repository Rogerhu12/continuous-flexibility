module

public import ContinuousFlexibility.Radial.InnerGapEnergyCoordinates
public import Mathlib.Topology.Algebra.Module.ClosedSubmodule
public import Mathlib.Analysis.Calculus.Deriv.Support

/-!
# The common physical first-order energy domain

Every piece uses the same actual radial measure and the same normalized
derivative r u′ / √12. The zero-endpoint domain is the closure of smooth
functions compactly supported in the open piece. It does not depend on
the sign of the potential, so positive gaps and retained wells have a
common domain for matching.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Radial

open Set MeasureTheory Filter ContinuousFlexibility.Statements
open scoped ContDiff InnerProductSpace

abbrev InnerRadialH1Pair (D : ReferenceData) :=
  RadialModeL2 D × RadialModeL2 D

/-- The actual physical value and normalized derivative of a compact
smooth field, with both coordinates extended by zero. -/
def InnerRadialH1Core (D : ReferenceData) (a b : ℝ) :
    Set (InnerRadialH1Pair D) :=
  {q | ∃ u : ℝ → ℝ, ContDiff ℝ ∞ u ∧ HasCompactSupport u ∧
    tsupport u ⊆ Ioo a b ∧
    q.1 =ᵐ[radialHilbertMeasure D] (Ioo a b).indicator u ∧
    q.2 =ᵐ[radialHilbertMeasure D]
      (Ioo a b).indicator (innerGapGradientField u)}

theorem innerRadialH1Core_zero (D : ReferenceData) (a b : ℝ) :
    (0 : InnerRadialH1Pair D) ∈ InnerRadialH1Core D a b := by
  refine ⟨0, contDiff_const, HasCompactSupport.zero, ?_, ?_, ?_⟩
  · simp only [tsupport_zero, empty_subset]
  all_goals
    filter_upwards [Lp.coeFn_zero ℝ 2 (radialHilbertMeasure D)] with r hr
    by_cases hmem : r ∈ Ioo a b
    · simpa [indicator_of_mem hmem, innerGapGradientField] using hr
    · simpa [indicator_of_notMem hmem] using hr

theorem innerRadialH1Core_add {D : ReferenceData} {a b : ℝ}
    {q r : InnerRadialH1Pair D}
    (hq : q ∈ InnerRadialH1Core D a b) (hr : r ∈ InnerRadialH1Core D a b) :
    q + r ∈ InnerRadialH1Core D a b := by
  rcases hq with ⟨u, hu, hcu, hsu, hu₀, hu₁⟩
  rcases hr with ⟨v, hv, hcv, hsv, hv₀, hv₁⟩
  refine ⟨u + v, hu.add hv, hcu.add hcv,
    (tsupport_add u v).trans (union_subset hsu hsv), ?_, ?_⟩
  · simp only [Prod.fst_add]
    filter_upwards [hu₀, hv₀, Lp.coeFn_add q.1 r.1] with x hx hy hadd
    rw [hadd, Pi.add_apply, hx, hy]
    by_cases hmem : x ∈ Ioo a b
    · simp only [indicator_of_mem hmem, Pi.add_apply]
    · simp only [indicator_of_notMem hmem, zero_add]
  · simp only [Prod.snd_add]
    filter_upwards [hu₁, hv₁, Lp.coeFn_add q.2 r.2] with x hx hy hadd
    rw [hadd, Pi.add_apply, hx, hy]
    by_cases hmem : x ∈ Ioo a b
    · simp only [indicator_of_mem hmem, innerGapGradientField,
        deriv_add (hu.differentiable (by simp) x) (hv.differentiable (by simp) x)]
      ring
    · simp only [indicator_of_notMem hmem, zero_add]

theorem innerRadialH1Core_smul {D : ReferenceData} {a b : ℝ}
    {q : InnerRadialH1Pair D} (hq : q ∈ InnerRadialH1Core D a b) (c : ℝ) :
    c • q ∈ InnerRadialH1Core D a b := by
  rcases hq with ⟨u, hu, hcu, hsu, hu₀, hu₁⟩
  refine ⟨fun x => c * u x, contDiff_const.mul hu, hcu.mul_left,
    tsupport_mul_subset_right.trans hsu, ?_, ?_⟩
  · simp only [Prod.smul_fst]
    filter_upwards [hu₀, Lp.coeFn_smul c q.1] with x hx hsmul
    rw [hsmul, Pi.smul_apply, smul_eq_mul, hx]
    by_cases hmem : x ∈ Ioo a b
    · simp only [indicator_of_mem hmem]
    · simp only [indicator_of_notMem hmem, mul_zero]
  · simp only [Prod.smul_snd]
    filter_upwards [hu₁, Lp.coeFn_smul c q.2] with x hx hsmul
    rw [hsmul, Pi.smul_apply, smul_eq_mul, hx]
    by_cases hmem : x ∈ Ioo a b
    · simp only [indicator_of_mem hmem, innerGapGradientField, deriv_const_mul_field]
      ring
    · simp only [indicator_of_notMem hmem, mul_zero]

def innerRadialH1CoreSubmodule (D : ReferenceData) (a b : ℝ) :
    Submodule ℝ (InnerRadialH1Pair D) where
  carrier := InnerRadialH1Core D a b
  zero_mem' := innerRadialH1Core_zero D a b
  add_mem' := innerRadialH1Core_add
  smul_mem' := fun c _ hq => innerRadialH1Core_smul hq c

/-- The actual zero-endpoint physical first-order energy domain. -/
def innerRadialH1Zero (D : ReferenceData) (a b : ℝ) :
    ClosedSubmodule ℝ (InnerRadialH1Pair D) :=
  (innerRadialH1CoreSubmodule D a b).closure

theorem coe_innerRadialH1Zero (D : ReferenceData) (a b : ℝ) :
    (innerRadialH1Zero D a b : Set (InnerRadialH1Pair D)) =
      closure (InnerRadialH1Core D a b) := by
  calc
    _ = closure (innerRadialH1CoreSubmodule D a b : Set (InnerRadialH1Pair D)) := by
      rw [innerRadialH1Zero, Submodule.coe_closure]
    _ = _ := rfl

theorem mem_innerRadialH1Zero (D : ReferenceData) (a b : ℝ) (q : InnerRadialH1Pair D) :
    q ∈ innerRadialH1Zero D a b ↔ q ∈ closure (InnerRadialH1Core D a b) :=
  Set.ext_iff.mp (coe_innerRadialH1Zero D a b) q

end ContinuousFlexibility.Radial
