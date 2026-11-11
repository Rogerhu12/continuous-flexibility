import ContinuousFlexibility.Radial.SelectedOuterTestRecovery
import ContinuousFlexibility.Radial.SelectedOuterKernelSymmetry

/-!
# Full weak test identities from the constructed weighted Green map

The response records the actual representative and flux already obtained
from variation of parameters. Test recovery and Hilbert-space symmetry
then give the weak identity for every ordinary-support smooth test.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open Set Filter MeasureTheory
open scoped Topology ContDiff InnerProductSpace RealInnerProductSpace
open ContinuousFlexibility.Analysis

def OuterWeightedGreenResponse (μ : Measure ℝ) (w ρ : ℝ → ℝ)
    (a b J lam : ℝ) (v : ℝ × ℝ) (R : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ) : Prop :=
  ∀ f : Lp ℝ 2 μ, ∃ u p : ℝ → ℝ,
    (R f : ℝ → ℝ) =ᵐ[μ] u ∧
    ContDiffOn ℝ 1 u (Ico a b) ∧ ContinuousOn p (Ico a b) ∧
    (∀ x ∈ Ioo a b, p x = w x * deriv u x) ∧
    (∀ x ∈ Ico a b, p x = w x * derivWithin u (Ico a b) x) ∧
    HasIntervalWeakDerivative a b p (fun x => J * deriv w x / x * u x - ρ x * f x) ∧
    outerStatePair v (u a, p a / lam) = 0

def OuterWeightedHomogeneousUnique (μ : Measure ℝ) (w : ℝ → ℝ)
    (a b J lam : ℝ) (v : ℝ × ℝ) : Prop :=
  ∀ y z : ℝ → ℝ,
    ContinuousOn y (Ico a b) → ContinuousOn z (Ico a b) →
    OuterFirstOrderSystem (fun x => lam / w x)
      (fun x => J * deriv w x / (lam * x)) y z (Ioo a b) →
    MemLp y 2 μ → outerStatePair v (y a, z a) = 0 →
    ∀ x ∈ Ico a b, y x = 0 ∧ z x = 0

theorem OuterWeightedGreenResponse.recover_test
    {μ : Measure ℝ} {w ρ : ℝ → ℝ} {a b J lam : ℝ} {v : ℝ × ℝ}
    {R : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ}
    (hR : OuterWeightedGreenResponse μ w ρ a b J lam v R)
    (hunique : OuterWeightedHomogeneousUnique μ w a b J lam v)
    (hab : a < b) (hlam : lam ≠ 0) (hw : ContDiff ℝ ∞ w)
    (hwn : ∀ x ∈ Ico a b, w x ≠ 0) (hr : ∀ x ∈ Ico a b, x ≠ 0)
    (hμ : ∀ q : ℝ → Prop, (∀ᵐ x ∂μ, q x) ↔ ∀ᵐ x ∂volume.restrict (Ioo a b), q x)
    (hρ : ∀ x ∈ Ioo a b, ρ x ≠ 0)
    {ψ : ℝ → ℝ} (hψ : ContDiff ℝ ∞ ψ) (hs : Function.support ψ ⊆ Ioo a b)
    (hψLp : MemLp ψ 2 μ)
    (htest : MemLp (fun x => radialJacobi J w ψ x / ρ x) 2 μ) :
    R (-htest.toLp (fun x => radialJacobi J w ψ x / ρ x)) = hψLp.toLp ψ := by
  let q : Lp ℝ 2 μ := htest.toLp (fun x => radialJacobi J w ψ x / ρ x)
  obtain ⟨u, p, hrep, hu, hp, hflux, _, hweak, hRobin⟩ := hR (-q)
  have hsource : (-q : Lp ℝ 2 μ) =ᵐ[volume.restrict (Ioo a b)]
      fun x => -(radialJacobi J w ψ x / ρ x) := by
    apply (hμ _).mp
    filter_upwards [Lp.coeFn_neg q, htest.coeFn_toLp] with x hx hqx
    simpa only [Pi.neg_apply, hqx] using hx
  have hweak' : HasIntervalWeakDerivative a b p
      (fun x => J * deriv w x / x * u x + radialJacobi J w ψ x) := by
    apply outerWeakDerivative_congr_source hweak
    filter_upwards [hsource, ae_restrict_mem measurableSet_Ioo] with x hx hxi
    rw [hx]
    field_simp [hρ x hxi]
    <;> ring
  have huLp : MemLp u 2 μ := (memLp_congr_ae hrep).mp (Lp.memLp (R (-q)))
  have he := outerWeakSolution_recovers_test hab hlam hw hwn hr hu hp hflux hweak'
    hRobin hψ hs huLp hψLp hunique
  apply Lp.ext
  filter_upwards [hrep, hψLp.coeFn_toLp,
    (hμ _).mpr (ae_restrict_mem measurableSet_Ioo)] with x hx hψx hxi
  exact (hx.trans (he (Ioo_subset_Ico_self hxi))).trans hψx.symm

theorem OuterWeightedGreenResponse.test_pairing
    {μ : Measure ℝ} {w ρ : ℝ → ℝ} {a b J lam : ℝ} {v : ℝ × ℝ}
    {R : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ}
    (hR : OuterWeightedGreenResponse μ w ρ a b J lam v R)
    (hunique : OuterWeightedHomogeneousUnique μ w a b J lam v)
    (hsym : R.toLinearMap.IsSymmetric)
    (hab : a < b) (hlam : lam ≠ 0) (hw : ContDiff ℝ ∞ w)
    (hwn : ∀ x ∈ Ico a b, w x ≠ 0) (hr : ∀ x ∈ Ico a b, x ≠ 0)
    (hμ : ∀ q : ℝ → Prop, (∀ᵐ x ∂μ, q x) ↔ ∀ᵐ x ∂volume.restrict (Ioo a b), q x)
    (hρ : ∀ x ∈ Ioo a b, ρ x ≠ 0)
    {ψ : ℝ → ℝ} (hψ : ContDiff ℝ ∞ ψ) (hs : Function.support ψ ⊆ Ioo a b)
    (hψLp : MemLp ψ 2 μ)
    (htest : MemLp (fun x => radialJacobi J w ψ x / ρ x) 2 μ)
    (f : Lp ℝ 2 μ) :
    ⟪R f, htest.toLp (fun x => radialJacobi J w ψ x / ρ x)⟫_ℝ =
      -⟪f, hψLp.toLp ψ⟫_ℝ := by
  have he := hR.recover_test hunique hab hlam hw hwn hr hμ hρ hψ hs hψLp htest
  have hs := hsym.apply_clm f (-htest.toLp (fun x => radialJacobi J w ψ x / ρ x))
  rw [he, inner_neg_right] at hs
  linarith only [hs]

end ContinuousFlexibility.Radial
