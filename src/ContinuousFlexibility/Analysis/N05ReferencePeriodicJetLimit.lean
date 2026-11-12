import ContinuousFlexibility.Analysis.N05ReferenceAngularJetCells
import ContinuousFlexibility.Analysis.N05ReferenceLowAngularBasis
import ContinuousFlexibility.Analysis.N05ReferenceAngularIntegration
import ContinuousFlexibility.Radial.R11bSymmetricLimit

/-!
# Periodic representatives of the actual angular jet limits

An almost everywhere convergent subsequence has one pointwise limit on
every angular orbit. This preserves the period without imposing evenness,
so the same construction applies to odd angular derivatives. The finite
high and low jets are derivatives of genuine periodic functions.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open Set Filter MeasureTheory
open scoped Topology
open ContinuousFlexibility.Statements

theorem n05_periodic_representative_of_L2_tendsto
    {μ : Measure PolarPoint} {f : ℕ → PolarPoint → ℝ}
    (hf : ∀ n, MemLp (f n) 2 μ)
    (hp : ∀ n, Function.Periodic (f n) (0, Real.pi))
    {u : Lp ℝ 2 μ}
    (hlim : Tendsto (fun n => (hf n).toLp (f n)) atTop (𝓝 u)) :
    ∃ g : PolarPoint → ℝ, MemLp g 2 μ ∧ g =ᵐ[μ] (u : PolarPoint → ℝ) ∧
      Function.Periodic g (0, Real.pi) := by
  obtain ⟨ns, _, hconv⟩ :=
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
  refine ⟨g, MemLp.ae_eq hgu.symm (Lp.memLp u), hgu, ?_⟩
  intro p
  change limUnder atTop (fun n => f (ns n) (p + (0, Real.pi))) =
    limUnder atTop (fun n => f (ns n) p)
  congr 1
  funext n
  exact hp (ns n) p

theorem n05_referenceHighAngularJet_periodic
    (J : Finset ℕ) (b : ℕ) (f : PolarPoint → ℝ) :
    Function.Periodic (n05_referenceHighAngularJet J b f) (0, Real.pi) := by
  intro p
  have hp : Function.Periodic
      (fun θ => referenceBasisProjection (J.image (fun n => n + 2)) f (p.1, θ))
      Real.pi := by
    intro θ
    simpa only [Prod.mk_add_mk, add_zero] using
      referenceBasisProjection_periodic (J.image (fun n => n + 2)) f (p.1, θ)
  simpa only [n05_referenceHighAngularJet, Prod.fst_add, Prod.snd_add, add_zero] using
    n05_periodic_iteratedDeriv hp b p.2

theorem n05_referenceLowAngularJet_periodic
    (b : ℕ) (f : PolarPoint → ℝ) :
    Function.Periodic (n05_referenceLowAngularJet b f) (0, Real.pi) := by
  intro p
  have hp : Function.Periodic (fun θ => referenceBasisProjection {0, 1} f (p.1, θ))
      Real.pi := by
    intro θ
    simpa only [Prod.mk_add_mk, add_zero] using
      referenceBasisProjection_periodic {0, 1} f (p.1, θ)
  simpa only [n05_referenceLowAngularJet, mixedDerivative, iteratedDeriv_zero,
    Prod.fst_add, Prod.snd_add, add_zero] using n05_periodic_iteratedDeriv hp b p.2

end ContinuousFlexibility.Radial
