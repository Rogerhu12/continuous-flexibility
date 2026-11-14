module

public import ContinuousFlexibility.Radial.InnerGapWeakFlux
public import ContinuousFlexibility.Radial.InnerGapRadialDomain

/-!
# One actual positive-gap Dirichlet/Poisson/flux realization

All identities refer to the same constructed Dirichlet inverse, the
same actual Poisson columns in μ_D, and the full outward flux matrix.
In particular the weak conormal identities use a single closed-domain
solution witness for each arbitrary L² source.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Radial

open Set MeasureTheory ContinuousFlexibility.Statements
open scoped ContDiff InnerProductSpace

/-- Joint properties of the already constructed physical objects.
This is an output package; the theorem below derives every property
from the actual positive-gap coefficients and endpoint solutions. -/
def InnerGapJointRealization (D : ReferenceData) (hw : ContDiff ℝ ∞ D.w)
    {a b j s : ℝ} (hab : a ≤ b) (ha : 0 < a) (hj : 0 < j) (hs : 0 < s)
    (hcore : Ioo a b ⊆ radialCore D) (hpos : ∀ r ∈ Icc a b, 0 < D.w r)
    (hslope : ∀ r ∈ Icc a b, s ≤ r * deriv D.w r / D.w r)
    (p : Fin 2 → ℝ → ℝ) (hp : ∀ k, ContDiff ℝ ∞ (p k)) : Prop :=
  let G := innerGapDirichletInverse D hw hab ha hj hs hcore hpos hslope
  let P := innerGapPoissonL2 D hw.continuous ha hcore
    (fun r hr => (hpos r (Ioo_subset_Icc_self hr)).le) p hp
  (innerGapFluxMatrix D.w a b p).PosSemidef ∧
    G.IsSymmetric ∧ ‖G‖ ≤ 12 / (s * j ^ 2) ∧
    (∀ u f, InnerGapFormGraph D j a b u f ↔ G f = u) ∧
    (∀ ξ : EuclideanSpace ℝ (Fin 2),
      ‖P ξ‖ ≤ (Real.sqrt (12 / s) / j) *
        Real.sqrt ⟪ξ, innerGapFluxOperator D.w a b p ξ⟫_ℝ ∧
      innerRadialGapEnergy D.w (innerGapPoisson p ξ) j a b =
        ⟪ξ, innerGapFluxOperator D.w a b p ξ⟫_ℝ) ∧
    ∀ F : RadialModeL2 D, ∃ q : InnerGapEnergyTriple D,
      q ∈ innerGapFormSpace D j a b ∧ q.fst = G F ∧
      (G F, q.snd.fst) ∈ innerRadialH1Zero D a b ∧
      (∀ r ∈ innerGapFormSpace D j a b, ⟪F, r.fst⟫_ℝ = ⟪q.snd, r.snd⟫_ℝ) ∧
      innerGapWeakFlux D hw ha hcore hpos j p hp q F = -P.adjoint F ∧
      ∀ ξ : EuclideanSpace ℝ (Fin 2),
        innerGapWeakFlux D hw ha hcore hpos j p hp
          (innerGapAffineEnergy D hw ha hcore hpos j p hp q ξ) F =
          innerGapFluxOperator D.w a b p ξ - P.adjoint F

theorem innerGap_joint_realization (D : ReferenceData) (hw : ContDiff ℝ ∞ D.w)
    {a b j s : ℝ} (hab : a ≤ b) (ha : 0 < a) (hj : 0 < j) (hs : 0 < s)
    (hcore : Ioo a b ⊆ radialCore D) (hpos : ∀ r ∈ Icc a b, 0 < D.w r)
    (hslope : ∀ r ∈ Icc a b, s ≤ r * deriv D.w r / D.w r)
    (p : Fin 2 → ℝ → ℝ) (hp : ∀ k, ContDiff ℝ ∞ (p k))
    (hb : ∀ i k, p k (innerGapEndpoint a b i) = if k = i then 1 else 0)
    (heq : ∀ i r, r ∈ Icc a b → radialJacobi (j ^ 2) D.w (p i) r = 0) :
    InnerGapJointRealization D hw hab ha hj hs hcore hpos hslope p hp := by
  have hslope0 : ∀ r ∈ Icc a b, 0 ≤ r * deriv D.w r / D.w r :=
    fun r hr => hs.le.trans (hslope r hr)
  dsimp only [InnerGapJointRealization]
  refine ⟨innerGapFluxMatrix_posSemidef hab ha hw p hp hb heq hpos hslope0,
    innerGapDirichletInverse_isSymmetric D hw hab ha hj hs hcore hpos hslope,
    innerGapDirichletInverse_norm_le D hw hab ha hj hs hcore hpos hslope,
    innerGapDirichletInverse_graph_iff D hw hab ha hj hs hcore hpos hslope, ?_, ?_⟩
  · intro ξ
    exact ⟨innerGapPoissonL2_norm_le D hw hab ha hj hs hcore
      (fun r hr => (hpos r (Ioo_subset_Icc_self hr)).le) p hp hb heq hpos hslope ξ,
      innerGapPoisson_energy_eq hab ha hw p hp hb heq ξ⟩
  · intro F
    obtain ⟨q, hq, hvalue, hH1, hform⟩ := innerGapFormGraph_radialH1 D j a b
      (innerGapDirichletInverse D hw hab ha hj hs hcore hpos hslope F) F
      (innerGapDirichletInverse_graph D hw hab ha hj hs hcore hpos hslope F)
    refine ⟨q, hq, hvalue, hH1, hform,
      innerGapWeakFlux_dirichlet D hw hab ha hcore hpos hslope0 p hp heq q hq F, ?_⟩
    intro ξ
    exact innerGapWeakFlux_affine D hw hab ha hcore hpos hslope0 p hp hb heq q hq F ξ

/-- Actual smooth positive-gap data produces the joint realization.
No Dirichlet inverse, Poisson solvability, matrix positivity, or final
operator estimate is assumed. -/
theorem exists_innerGapJointRealization (D : ReferenceData) (hw : ContDiff ℝ ∞ D.w)
    {A a b B j s : ℝ} (hA : 0 < A) (hAa : A < a) (hab : a < b) (hbB : b < B)
    (hj : 0 < j) (hs : 0 < s) (hcore : Ioo a b ⊆ radialCore D)
    (hwnonneg : ∀ r, 0 ≤ D.w r) (hwpos : ∀ r ∈ Ioo A B, 0 < D.w r)
    (hslope : ∀ r ∈ Icc a b, s ≤ r * deriv D.w r / D.w r) :
    ∃ p : Fin 2 → ℝ → ℝ, ∃ hp : ∀ k, ContDiff ℝ ∞ (p k),
      (∀ i k, p k (innerGapEndpoint a b i) = if k = i then 1 else 0) ∧
      (∀ i r, r ∈ Icc a b → radialJacobi (j ^ 2) D.w (p i) r = 0) ∧
      InnerGapJointRealization D hw hab.le (hA.trans hAa) hj hs hcore
        (fun r hr => hwpos r ⟨hAa.trans_le hr.1, hr.2.trans_lt hbB⟩) hslope p hp := by
  have hslope0 : ∀ r ∈ Icc a b, 0 ≤ r * deriv D.w r / D.w r :=
    fun r hr => hs.le.trans (hslope r hr)
  obtain ⟨p, hp, hboundary, heq⟩ := exists_innerGapPoissonColumns
    hA hAa hab hbB hw hwnonneg hwpos hslope0 j
  refine ⟨p, hp, hboundary, heq, ?_⟩
  exact innerGap_joint_realization D hw hab.le (hA.trans hAa) hj hs hcore
    (fun r hr => hwpos r ⟨hAa.trans_le hr.1, hr.2.trans_lt hbB⟩)
    hslope p hp hboundary heq

end ContinuousFlexibility.Radial
