module

public import ContinuousFlexibility.Analysis.PhysicalTransmissionTrace
public import ContinuousFlexibility.Analysis.PointwiseCylinderJets

/-!
# Boundary jets from a one-sided actual equation

The existing open-set congruence for actual mixed derivatives needs no
smoothness. Smoothness at a boundary point makes each actual mixed jet
continuous there, so the equation extends to that point. No common open
neighborhood of infinite smoothness or equation across the boundary is
assumed.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter
open ContinuousFlexibility.Statements
open scoped Topology ContDiff

set_option backward.isDefEq.respectTransparency false

/-- Smoothness at the boundary point itself is enough to transfer an
actual open-set equation to all actual mixed boundary jets. -/
theorem mixedDerivative_eq_at_closure_of_contDiffAt
    {U : Set PolarPoint} (hU : IsOpen U)
    {F G : PolarPoint → ℝ} {p : PolarPoint}
    (hF : ContDiffAt ℝ ∞ F p) (hG : ContDiffAt ℝ ∞ G p)
    (he : EqOn F G U) (hp : p ∈ closure U) (a b : ℕ) :
    mixedDerivative a b F p = mixedDerivative a b G p := by
  haveI : NeBot (𝓝[U] p) := mem_closure_iff_nhdsWithin_neBot.mp hp
  have hf : ContinuousAt (mixedDerivative a b F) p :=
    (contDiffAt_mixedDerivative hF a b).continuousAt
  have hg : ContinuousAt (mixedDerivative a b G) p :=
    (contDiffAt_mixedDerivative hG a b).continuousAt
  exact tendsto_nhds_unique_of_eventuallyEq
    (hf.mono_left nhdsWithin_le_nhds) (hg.mono_left nhdsWithin_le_nhds)
    ((mixedDerivative_eqOn_of_isOpen hU he a b).eventuallyEq_of_mem self_mem_nhdsWithin)

/-- A neighborhood formulation permits different smooth neighborhoods for
the two fields. It is a consequence of the pointwise version. -/
theorem mixedDerivative_eq_at_closure_of_contDiffOn
    {U V W : Set PolarPoint} (hU : IsOpen U) (hV : IsOpen V) (hW : IsOpen W)
    {F G : PolarPoint → ℝ}
    (hF : ContDiffOn ℝ ∞ F V) (hG : ContDiffOn ℝ ∞ G W)
    (he : EqOn F G U) {p : PolarPoint}
    (hp : p ∈ closure U) (hpV : p ∈ V) (hpW : p ∈ W) (a b : ℕ) :
    mixedDerivative a b F p = mixedDerivative a b G p :=
  mixedDerivative_eq_at_closure_of_contDiffAt hU
    (hF.contDiffAt (hV.mem_nhds hpV)) (hG.contDiffAt (hW.mem_nhds hpW)) he hp a b

/-- One statement covers the interior and both endpoints of a nonempty
physical strip, with pointwise smoothness at the selected point only. -/
theorem mixedDerivative_eq_on_closedStrip_of_contDiffAt
    {F G : PolarPoint → ℝ} {p : PolarPoint}
    (hF : ContDiffAt ℝ ∞ F p) (hG : ContDiffAt ℝ ∞ G p)
    {c d : ℝ} (hcd : c < d)
    (he : EqOn F G (Ioo c d ×ˢ (univ : Set ℝ)))
    (hp : p.1 ∈ Icc c d) (a b : ℕ) :
    mixedDerivative a b F p = mixedDerivative a b G p := by
  apply mixedDerivative_eq_at_closure_of_contDiffAt
    (isOpen_Ioo.prod isOpen_univ) hF hG he ?_ a b
  rw [closure_prod_eq, closure_Ioo hcd.ne, closure_univ]
  exact ⟨hp, mem_univ _⟩

/-- The corresponding open-neighborhood interface. -/
theorem mixedDerivative_eq_on_closedStrip_of_contDiffOn
    {V W : Set PolarPoint} (hV : IsOpen V) (hW : IsOpen W)
    {F G : PolarPoint → ℝ}
    (hF : ContDiffOn ℝ ∞ F V) (hG : ContDiffOn ℝ ∞ G W)
    {c d : ℝ} (hcd : c < d)
    (he : EqOn F G (Ioo c d ×ˢ (univ : Set ℝ)))
    {p : PolarPoint} (hp : p.1 ∈ Icc c d) (hpV : p ∈ V) (hpW : p ∈ W)
    (a b : ℕ) :
    mixedDerivative a b F p = mixedDerivative a b G p :=
  mixedDerivative_eq_on_closedStrip_of_contDiffAt
    (hF.contDiffAt (hV.mem_nhds hpV)) (hG.contDiffAt (hW.mem_nhds hpW)) hcd he hp a b

end ContinuousFlexibility.Analysis
