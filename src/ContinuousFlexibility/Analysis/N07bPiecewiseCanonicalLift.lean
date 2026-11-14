module

public import ContinuousFlexibility.Analysis.N07bActualCanonicalSourceLift

/-!
# The prescribed source level from piecewise smooth representatives

A physical reference forcing need only have finite global regularity.
Each of its canonical pieces has a genuine smooth extension to its closed
canonical cylinder. These extensions give local L² jets; periodic Green
identities and summability then put the actual jets in the same chosen
volume model. No global smoothness of the forcing is required.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter MeasureTheory ContinuousFlexibility.Statements
open scoped ContDiff Topology BigOperators ENNReal

set_option backward.isDefEq.respectTransparency true

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {K : CanonicalData S} {V : VolumeModelData S K}

/-- The energy of the actual angular jets, before choosing L² classes. -/
def n07bPiecewiseCanonicalJetEnergy (T : MaterialData) (K : CanonicalData S)
    (g : ℕ → PolarPoint → ℝ) (γ t : ℝ) (s m : ℕ) : ℝ :=
  ∑ j : Fin (s + 1), (n07bCanonicalSourceFactor T K γ t m)⁻¹ ^ 2 *
    (eLpNorm (mixedDerivative 0 j.val (g m)) 2 (canonicalMeasure S K m)).toReal ^ 2

theorem n07bPiecewiseCanonicalJetEnergy_nonneg (T : MaterialData) (K : CanonicalData S)
    (g : ℕ → PolarPoint → ℝ) (γ t : ℝ) (s m : ℕ) :
    0 ≤ n07bPiecewiseCanonicalJetEnergy T K g γ t s m :=
  Finset.sum_nonneg (fun _ _ => mul_nonneg (sq_nonneg _) (sq_nonneg _))

/-- A smooth extension on the closed cylinder gives actual interior
smoothness of the specified representative. -/
theorem n07b_contDiffOn_of_closed_canonical_extension (m : ℕ)
    {g e : PolarPoint → ℝ} (hge : EqOn g e (canonicalOpen S K m))
    (he : ∀ p ∈ canonicalClosed S K m, ContDiffAt ℝ ∞ e p) :
    ContDiffOn ℝ ∞ g (canonicalOpen S K m) := by
  intro p hp
  have hpclosed : p ∈ canonicalClosed S K m :=
    ⟨⟨hp.1.1.le, hp.1.2.le⟩, mem_univ _⟩
  have hlocal : g =ᶠ[𝓝 p] e := by
    filter_upwards [(isOpen_Ioo.prod isOpen_univ).mem_nhds hp] with q hq
    exact hge hq
  exact ((he p hpclosed).congr_of_eventuallyEq hlocal).contDiffWithinAt

/-- The actual piecewise jets determine an element of the already chosen
source level, at the stated weight and angular order. -/
theorem n07b_exists_piecewiseCanonicalLift
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T)
    (hV : IsVolumeModel T S K V)
    (g e : ℕ → PolarPoint → ℝ) (γ t : ℝ) (s : ℕ)
    (heq : ∀ m, EqOn (g m) (e m) (canonicalOpen S K m))
    (he : ∀ m p, p ∈ canonicalClosed S K m → ContDiffAt ℝ ∞ (e m) p)
    (hp : ∀ m r, r ∈ Ioo (K.left m) (K.right m) →
      Function.Periodic (fun θ => g m (r, θ)) Real.pi)
    (href : ∀ m, (fun p : PolarPoint => g m (p.1, Real.pi - p.2))
      =ᵐ[canonicalMeasure S K m] g m)
    (hsum : Summable (n07bPiecewiseCanonicalJetEnergy T K g γ t s)) :
    ∃ F : V.level γ t s,
      (∀ m, (V.forget γ t s F m : PolarPoint → ℝ) =ᵐ[canonicalMeasure S K m] g m) ∧
      ‖F‖ ^ 2 = ∑' m, n07bPiecewiseCanonicalJetEnergy T K g γ t s m := by
  let jets : ∀ m : ℕ, Fin (s + 1) → PolarPoint → ℝ :=
    fun m j => mixedDerivative 0 j.val (g m)
  have hjets (m : ℕ) (j : Fin (s + 1)) :
      MemLp (jets m j) 2 (canonicalMeasure S K m) :=
    n07b_canonical_mixedDerivative_memLp_of_extension m (heq m) (he m) 0 j.val
  have hzero (m : ℕ) : jets m 0 = g m := by
    funext p
    simp only [jets, Fin.val_zero, mixedDerivative, iteratedDeriv_zero, Prod.eta]
  have hreflect : ∀ m, (fun p : PolarPoint => jets m 0 (p.1, Real.pi - p.2))
      =ᵐ[canonicalMeasure S K m] jets m 0 := by
    intro m
    rw [hzero m]
    exact href m
  have hweak : ∀ m j φ, CanonicalTest S K m φ →
      (∫ p, jets m j p * φ p ∂canonicalMeasure S K m) =
        (-1 : ℝ) ^ j.val * ∫ p, jets m 0 p * mixedDerivative 0 j.val φ p
          ∂canonicalMeasure S K m := by
    intro m j φ hφ
    have h₀ : MemLp (g m) 2 (canonicalMeasure S K m) := by
      simpa only [hzero m] using hjets m 0
    rw [hzero m]
    exact n07b_integral_canonicalAngularJet_mul
      (n07b_contDiffOn_of_closed_canonical_extension m (heq m) (he m))
      (hp m) j.val h₀ (hjets m j) hφ
  have henergy (m : ℕ) : n07bCanonicalJetEnergy (T := T) hjets γ t m =
      n07bPiecewiseCanonicalJetEnergy T K g γ t s m := by
    simp only [n07bCanonicalJetEnergy, n07bCanonicalWeightedJet,
      n07bPiecewiseCanonicalJetEnergy, norm_smul, Real.norm_eq_abs, mul_pow,
      sq_abs, Lp.norm_toLp, jets]
  have hsummable : Summable (n07bCanonicalJetEnergy (T := T) hjets γ t) :=
    hsum.congr (fun m => (henergy m).symm)
  let F : V.level γ t s := n07bCanonicalSourceLift hjets hV hreflect hweak hsummable
  refine ⟨F, ?_, ?_⟩
  · intro m
    have hforget := n07bCanonicalSourceLift_forget_ae hjets hV hreflect hweak hsummable
      (fun k => (n07bCanonicalSourceFactor_pos_of_material hD hT γ t k).ne') m
    simpa only [hzero m] using hforget
  · exact (n07bCanonicalSourceLift_norm_sq hjets hV hreflect hweak hsummable).trans
      (tsum_congr henergy)

end ContinuousFlexibility.Analysis
