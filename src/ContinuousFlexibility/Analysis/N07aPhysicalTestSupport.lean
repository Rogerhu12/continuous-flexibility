import ContinuousFlexibility.Analysis.N07aCanonicalTestOperator
import ContinuousFlexibility.Analysis.N07aCanonicalRoughPairing

/-!
# Actual support and periodicity for physical weak pairings

The derivative of an equivariant chart is periodic. Thus a periodic
canonical source has a periodic physical representative on its piece.
The genuine compact test and its actual divergence vanish outside that
piece, including at the radial endpoints.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter ContinuousFlexibility.Statements
open scoped ContDiff Topology

theorem n07a_domain_jacobian_periodic {Omega : Set PolarPoint} {F : PolarPoint → PolarPoint}
    (hOmega : IsOpen Omega)
    (hshift : ∀ p ∈ Omega, p + (0, Real.pi) ∈ Omega)
    (hs : ContDiffOn ℝ ∞ F Omega)
    (hp : ∀ p ∈ Omega,
      F (p + (0, Real.pi)) = F p + (0, Real.pi)) :
    ∀ p ∈ Omega,
      planeJacobian F (p + (0, Real.pi)) = planeJacobian F p := by
  intro p hpm
  have hps : p + (0, Real.pi) ∈ Omega := hshift p hpm
  have hf₀ := (hs.contDiffAt (hOmega.mem_nhds hpm)).differentiableAt
    (by simp)
  have hf₁ := (hs.contDiffAt (hOmega.mem_nhds hps)).differentiableAt
    (by simp)
  have hd : HasFDerivAt (fun q => F (q + (0, Real.pi)))
      (fderiv ℝ F (p + (0, Real.pi))) p := by
    have h := hf₁.hasFDerivAt.comp p ((hasFDerivAt_id p).add_const (0, Real.pi))
    have hcomp : (F ∘ fun q : PolarPoint => id q + (0, Real.pi)) =
        fun q => F (q + (0, Real.pi)) := by
      funext q
      rw [Function.comp_apply]
      rfl
    rw [hcomp, ContinuousLinearMap.comp_id] at h
    exact h
  have he : (fun q => F (q + (0, Real.pi))) =ᶠ[𝓝 p]
      fun q => F q + (0, Real.pi) := by
    filter_upwards [hOmega.mem_nhds hpm] with q hq
    exact hp q hq
  have hder := (hd.congr_of_eventuallyEq he.symm).unique
    (hf₀.hasFDerivAt.add_const (0, Real.pi))
  rw [n07a_planeJacobian_eq_det, n07a_planeJacobian_eq_det, hder]

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {L : ReturnCorrectionData S} {K : CanonicalData S}
  {base loss : ℕ} {ε : ℝ} {z : AnnularState S × ℝ} {m : ℕ}

theorem n07a_physical_periodic_of_canonicalSource
    (h04 : N04Properties D T S C L K base loss ε)
    (hz : z ∈ stateNeighborhood S C base ε) (hs : stateSector S z.1)
    {f : PolarPoint → ℝ}
    (hf : ∀ p ∈ canonicalOpen S K m,
      canonicalSource S K z m f (p + (0, Real.pi)) = canonicalSource S K z m f p) :
    ∀ p ∈ physicalPieceOpen S K z m, f (p + (0, Real.pi)) = f p := by
  have hdomain := h04.1.domains z hz hs m
  obtain ⟨hmap, _, hgf, _, hFs, _, _, hpoint⟩ := h04.1.charts z hz hs m
  have hFP := fun p hp => (hpoint p hp).2.2.1
  have hJ := n07a_domain_jacobian_periodic hdomain.1
    (fun p hp => (hdomain.2.2.2.1 p).mpr hp) hFs hFP
  intro p hp
  have hps : p + (0, Real.pi) ∈ physicalPieceOpen S K z m :=
    (hdomain.2.2.2.1 p).mpr hp
  have h := hf (K.chart z m p) (hmap hp)
  rw [← hFP p hp] at h
  simp only [canonicalSource, hgf p hp, hgf _ hps,
    (hpoint p hp).2.2.2, hJ p hp] at h
  exact mul_left_cancel₀ (hpoint p hp).1.ne'
    ((div_left_inj' (abs_ne_zero.mpr (hpoint p hp).2.1)).mp h)

theorem n07aPhysicalTestPullback_zero (z : AnnularState S × ℝ) (m : ℕ)
    (W : PolarPoint → ℝ) {p : PolarPoint}
    (hp : p ∉ physicalPieceOpen S K z m) :
    n07aPhysicalTestPullback S K z m W p = 0 := ite_eq_right hp

theorem n07aPhysicalTestPullback_divergence_zero
    (h04 : N04Properties D T S C L K base loss ε)
    (hz : z ∈ stateNeighborhood S C base ε) (hs : stateSector S z.1)
    {W : PolarPoint → ℝ} (hW : CanonicalTest S K m W)
    (A : SymmetricCoefficients) {p : PolarPoint}
    (hp : p ∉ physicalPieceOpen S K z m) :
    divergenceOperator A (n07aPhysicalTestPullback S K z m W) p = 0 := by
  have hgerm := n07aPhysicalTestPullback_zero_germ h04 hz hs hW hp
  rw [n07a_divergenceOperator_unknown_germ A hgerm]
  simp only [divergenceOperator, radialPartial_const, angularPartial_const,
    mul_zero, add_zero]

end ContinuousFlexibility.Analysis
