module

public import ContinuousFlexibility.Analysis.EndpointAffinePrimitive
public import ContinuousFlexibility.Analysis.IntervalWeakDivergence

/-!
# Uniqueness of a homogeneous weak divergence solution at a vanishing endpoint

Only one tail condition is needed: the solution itself has finite L² norm with
inverse coefficient weight near the endpoint. The weak equation supplies its
affine reciprocal-primitive representative, and the resistance estimate
forces that representative to vanish on the whole connected interval.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter MeasureTheory
open scoped ContDiff Topology

theorem weak_divergence_eq_zero_of_tail_memLp {a b x₀ : ℝ} (hab : a < b)
    {w u : ℝ → ℝ} (hw : ContDiff ℝ ∞ w)
    (hwpos : ∀ x ∈ Ioo a b, 0 < w x) (hwb : w b = 0)
    (hu : LocallyIntegrableOn u (Ioo a b) volume) (hx₀ : x₀ ∈ Ioo a b)
    (htail : MemLp (fun x => Real.sqrt ((w x)⁻¹) * u x) 2
      (volume.restrict (Ioo x₀ b)))
    (hdiv : ∀ φ : ℝ → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ →
      tsupport φ ⊆ Ioo a b →
        (∫ x, u x * deriv (fun y => w y * deriv φ y) x) = 0) :
    u =ᵐ[volume.restrict (Ioo a b)] 0 := by
  obtain ⟨c, q, hrep⟩ :=
    exists_ae_eq_affine_reciprocalPrimitive_of_divergence_eq_zero_Ioo
      hab hw (fun x hx => (hwpos x hx).ne') hu x₀ hx₀ hdiv
  have hfull : ∀ᵐ x ∂(volume : Measure ℝ), x ∈ Ioo a b →
      u x = c + q * intervalReciprocalPrimitive w x₀ x :=
    (ae_restrict_iff' measurableSet_Ioo).mp hrep
  have htailrep : u =ᵐ[volume.restrict (Ioo x₀ b)]
      (fun x => c + q * intervalReciprocalPrimitive w x₀ x) := by
    apply (ae_restrict_iff' measurableSet_Ioo).mpr
    filter_upwards [hfull] with x hx
    intro hxt
    exact hx ⟨hx₀.1.trans hxt.1, hxt.2⟩
  have hrepLp : MemLp (fun x => Real.sqrt ((w x)⁻¹) *
      (c + q * (∫ y in x₀..x, (w y)⁻¹))) 2 (volume.restrict (Ioo x₀ b)) :=
    MemLp.ae_eq (htailrep.mono fun x hx => congrArg (fun z => Real.sqrt ((w x)⁻¹) * z) hx)
      htail
  obtain ⟨hc, hq⟩ := affine_inverse_primitive_eq_zero_of_memLp hx₀.2
    (hw.of_le (by simp)) (fun x hx => hwpos x ⟨hx₀.1.trans_le hx.1, hx.2⟩)
    hwb c q hrepLp
  filter_upwards [hrep] with x hx
  simpa only [hc, hq, zero_mul, zero_add, Pi.zero_apply] using hx

end ContinuousFlexibility.Analysis
