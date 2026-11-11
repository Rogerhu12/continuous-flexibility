import ContinuousFlexibility.Statements.Radial
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
import Mathlib.MeasureTheory.Function.L2Space

/-!
# A pointwise symmetric representative of an L² sequence limit

An almost everywhere convergent subsequence supplies an actual representative.
Taking the same pointwise limit of the original functions on every angular
orbit preserves their exact evenness and half-turn periodicity, including
outside the physical annulus. No choice of exceptional sets by radius is used.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open Set Filter MeasureTheory
open scoped Topology
open ContinuousFlexibility.Statements

theorem r11b_symmetric_representative_of_L2_tendsto
    {μ : Measure PolarPoint} {f : ℕ → PolarPoint → ℝ}
    (hf : ∀ n, MemLp (f n) 2 μ)
    (hp : ∀ n r, Function.Periodic (fun θ => f n (r, θ)) Real.pi)
    (he : ∀ n r, Function.Even (fun θ => f n (r, θ)))
    {u : Lp ℝ 2 μ}
    (hlim : Tendsto (fun n => (hf n).toLp (f n)) atTop (𝓝 u)) :
    ∃ g : PolarPoint → ℝ, MemLp g 2 μ ∧ g =ᵐ[μ] (u : PolarPoint → ℝ) ∧
      (∀ r, Function.Periodic (fun θ => g (r, θ)) Real.pi) ∧
      (∀ r, Function.Even (fun θ => g (r, θ))) := by
  obtain ⟨ns, _hns, hconv⟩ :=
    (tendstoInMeasure_of_tendsto_Lp hlim).exists_seq_tendsto_ae
  have hrep : ∀ᵐ x ∂μ, ∀ n : ℕ, ((hf n).toLp (f n) : PolarPoint → ℝ) x = f n x :=
    ae_all_iff.mpr fun n => (hf n).coeFn_toLp
  let g : PolarPoint → ℝ := fun x => limUnder atTop (fun n => f (ns n) x)
  have hgu : g =ᵐ[μ] (u : PolarPoint → ℝ) := by
    filter_upwards [hrep, hconv] with x hx hcx
    have hpoint : (fun n => ((hf (ns n)).toLp (f (ns n)) : PolarPoint → ℝ) x) =
        (fun n => f (ns n) x) := funext fun n => hx (ns n)
    rw [hpoint] at hcx
    exact hcx.limUnder_eq
  refine ⟨g, MemLp.ae_eq hgu.symm (Lp.memLp u), hgu, ?_, ?_⟩
  · intro r θ
    change limUnder atTop (fun n => f (ns n) (r, θ + Real.pi)) =
      limUnder atTop (fun n => f (ns n) (r, θ))
    congr 1
    funext n
    exact hp (ns n) r θ
  · intro r θ
    change limUnder atTop (fun n => f (ns n) (r, -θ)) =
      limUnder atTop (fun n => f (ns n) (r, θ))
    congr 1
    funext n
    exact he (ns n) r θ

end ContinuousFlexibility.Radial
