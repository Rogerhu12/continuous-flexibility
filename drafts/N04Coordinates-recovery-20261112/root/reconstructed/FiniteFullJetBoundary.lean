import ContinuousFlexibility.Analysis.FiniteFullJetMatching
import ContinuousFlexibility.Analysis.OneSidedOrdinaryJets
import ContinuousFlexibility.Analysis.BoundaryTaylorExtension

/-!
# Ordinary finite jets at an actual boundary

An equation on an adjacent open set reaches every finite ordinary jet
at a smooth closure point. Common precomposition then restricts these
jets to the actual radial curve, including its zero order.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter
open ContinuousFlexibility.Statements
open scoped Topology ContDiff BigOperators

variable {E F G : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G]

theorem FiniteFullJetMatch.symm {n : ℕ} {x : E} {f g : E → F}
    (h : FiniteFullJetMatch n x f g) : FiniteFullJetMatch n x g f :=
  ⟨h.right_smooth, h.left_smooth, fun k hk => (h.jets k hk).symm⟩

theorem FiniteFullJetMatch.trans {n : ℕ} {x : E} {f g h : E → F}
    (hfg : FiniteFullJetMatch n x f g) (hgh : FiniteFullJetMatch n x g h) :
    FiniteFullJetMatch n x f h :=
  ⟨hfg.left_smooth, hgh.right_smooth,
    fun k hk => (hfg.jets k hk).trans (hgh.jets k hk)⟩

theorem finiteFullJetMatch_of_germ {n : ℕ} {x : E} {f g : E → F}
    (hf : ContDiffAt ℝ ∞ f x) (hg : ContDiffAt ℝ ∞ g x)
    (he : f =ᶠ[𝓝 x] g) : FiniteFullJetMatch n x f g :=
  ⟨hf, hg, fun k _ => (he.iteratedFDeriv ℝ k).eq_of_nhds⟩

theorem finiteFullJetMatch_of_eqOn_closure
    {n : ℕ} {U : Set E} (hU : IsOpen U) {f g : E → F} {x : E}
    (hf : ContDiffAt ℝ ∞ f x) (hg : ContDiffAt ℝ ∞ g x)
    (he : EqOn f g U) (hx : x ∈ closure U) : FiniteFullJetMatch n x f g := by
  haveI : NeBot (𝓝[U] x) := mem_closure_iff_nhdsWithin_neBot.mp hx
  refine ⟨hf, hg, ?_⟩
  intro k _
  have hfc : ContinuousAt (iteratedFDeriv ℝ k f) x :=
    (hf.differentiableAt_iteratedFDeriv
      (ENat.natCast_lt_of_coe_top_le_withTop le_rfl k)).continuousAt
  have hgc : ContinuousAt (iteratedFDeriv ℝ k g) x :=
    (hg.differentiableAt_iteratedFDeriv
      (ENat.natCast_lt_of_coe_top_le_withTop le_rfl k)).continuousAt
  exact tendsto_nhds_unique_of_eventuallyEq
    (hfc.mono_left nhdsWithin_le_nhds) (hgc.mono_left nhdsWithin_le_nhds)
    ((iteratedFDeriv_eqOn_of_isOpen hU he k).eventuallyEq_of_mem self_mem_nhdsWithin)

theorem FiniteFullJetMatch.precomp {n : ℕ} {y : E} {γ : E → F} {f g : F → G}
    (h : FiniteFullJetMatch n (γ y) f g) (hγ : ContDiffAt ℝ ∞ γ y) :
    FiniteFullJetMatch n y (f ∘ γ) (g ∘ γ) := by
  refine ⟨h.left_smooth.comp y hγ, h.right_smooth.comp y hγ, ?_⟩
  intro k hk
  rw [iteratedFDeriv_comp h.left_smooth hγ (by simp : (k : ℕ∞ω) ≤ ∞),
    iteratedFDeriv_comp h.right_smooth hγ (by simp : (k : ℕ∞ω) ≤ ∞)]
  unfold FormalMultilinearSeries.taylorComp
  apply Finset.sum_congr rfl
  intro c _
  ext v
  simp only [FormalMultilinearSeries.compAlongOrderedFinpartition_apply, ftaylorSeries]
  rw [h.jets c.length (c.length_le.trans hk)]

theorem radialBoundaryJet_eq_of_finiteFullJetMatch
    {f g : PolarPoint → ℝ} {c θ : ℝ} {n k : ℕ}
    (h : FiniteFullJetMatch n (c, θ) f g) (hk : k ≤ n) :
    radialBoundaryJet f c k θ = radialBoundaryJet g c k θ := by
  have hl : ContDiffAt ℝ ∞ (fun r : ℝ => (r, θ)) c :=
    contDiffAt_id.prodMk contDiffAt_const
  have hm := h.precomp hl
  have he := congrArg (fun A : ℝ [×k]→L[ℝ] ℝ => A (fun _ => 1)) (hm.jets k hk)
  simpa only [radialBoundaryJet, iteratedDeriv_eq_iteratedFDeriv, Function.comp_def] using he

end ContinuousFlexibility.Analysis
