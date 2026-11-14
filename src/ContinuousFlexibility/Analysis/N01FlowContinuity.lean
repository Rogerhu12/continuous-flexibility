module

public import ContinuousFlexibility.Analysis.N01ReturnChartRegularity

/-!
# Joint continuity of the actual ordinary flow

The angular maps are strictly increasing by N01.  Separate continuity
therefore gives joint continuity by bracketing the angular coordinate.
This includes the two turning radii and uses no time derivative there.
-/

@[expose] public section

noncomputable section

open Set Filter
open scoped Topology

set_option backward.isDefEq.respectTransparency false

namespace ContinuousFlexibility.Analysis

/-- Separate continuity and monotonicity in the real coordinate give
joint continuity.  The parameter space itself need not be metrizable. -/
theorem continuous_uncurry_of_monotone_sections
    {X : Type*} [TopologicalSpace X] (F : X → ℝ → ℝ)
    (hX : ∀ θ, Continuous (fun x => F x θ))
    (hθ : ∀ x, Continuous (F x)) (hmono : ∀ x, Monotone (F x)) :
    Continuous (fun p : X × ℝ => F p.1 p.2) := by
  apply continuous_iff_continuousAt.mpr
  rintro ⟨x, θ⟩
  apply tendsto_order.mpr
  constructor
  · intro l hl
    have hnear : ∀ᶠ t in 𝓝[<] θ, l < F x t :=
      ((hθ x).continuousAt.eventually (Ioi_mem_nhds hl)).filter_mono nhdsWithin_le_nhds
    have hboth : ∀ᶠ t in 𝓝[<] θ, t < θ ∧ l < F x t := by
      filter_upwards [self_mem_nhdsWithin, hnear] with t ht hlt
      exact ⟨ht, hlt⟩
    obtain ⟨t, ht, hlt⟩ := Filter.Eventually.exists hboth
    have hparam : ∀ᶠ p : X × ℝ in 𝓝 (x, θ), l < F p.1 t :=
      ((hX t).continuousAt.comp continuousAt_fst).eventually (Ioi_mem_nhds hlt)
    have hangle : ∀ᶠ p : X × ℝ in 𝓝 (x, θ), t < p.2 :=
      continuousAt_snd.eventually (Ioi_mem_nhds ht)
    filter_upwards [hparam, hangle] with p hp hpt
    exact hp.trans_le (hmono p.1 hpt.le)
  · intro u hu
    have hnear : ∀ᶠ t in 𝓝[>] θ, F x t < u :=
      ((hθ x).continuousAt.eventually (Iio_mem_nhds hu)).filter_mono nhdsWithin_le_nhds
    have hboth : ∀ᶠ t in 𝓝[>] θ, θ < t ∧ F x t < u := by
      filter_upwards [self_mem_nhdsWithin, hnear] with t ht hlt
      exact ⟨ht, hlt⟩
    obtain ⟨t, ht, hlt⟩ := Filter.Eventually.exists hboth
    have hparam : ∀ᶠ p : X × ℝ in 𝓝 (x, θ), F p.1 t < u :=
      ((hX t).continuousAt.comp continuousAt_fst).eventually (Iio_mem_nhds hlt)
    have hangle : ∀ᶠ p : X × ℝ in 𝓝 (x, θ), p.2 < t :=
      continuousAt_snd.eventually (Iio_mem_nhds ht)
    filter_upwards [hparam, hangle] with p hp hpt
    exact (hmono p.1 hpt.le).trans_lt hp

end ContinuousFlexibility.Analysis

namespace ContinuousFlexibility.Statements

theorem N01Properties.minusFlow_continuousOn
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {base loss : ℕ} {ε : ℝ}
    (hN01 : N01Properties D T S C base loss ε)
    {z : AnnularState S × ℝ} (hz : z ∈ stateNeighborhood S C base ε) (m : ℕ) :
    ContinuousOn (fun p : PolarPoint => C.minusFlow z m p.1 p.2)
      (Icc (C.left m) (C.right m) ×ˢ univ) := by
  have hflow : ordinaryFlowConditions D S C (stateNeighborhood S C base ε) :=
    hN01.2.2.2.2.2.2.1
  have hjoint : Continuous (fun p : Icc (C.left m) (C.right m) × ℝ =>
      C.minusFlow z m p.1 p.2) := by
    apply Analysis.continuous_uncurry_of_monotone_sections
      (fun (r : Icc (C.left m) (C.right m)) θ => C.minusFlow z m r θ)
    · intro θ
      exact (hflow z hz m θ).2.1.domRestrict
    · intro r
      exact (N01Properties.minusFlow_differentiable S C z m hN01 hz r.2).continuous
    · intro r
      exact (strictMono_of_deriv_pos fun θ => ((hflow z hz m θ).2.2.2 r r.2).1).monotone
  apply continuousOn_iff_continuous_domRestrict.mpr
  let lift : (Icc (C.left m) (C.right m) ×ˢ (univ : Set ℝ)) →
      Icc (C.left m) (C.right m) × ℝ := fun p => (⟨p.val.1, p.property.1⟩, p.val.2)
  have hlift : Continuous lift :=
    ((continuous_fst.comp continuous_subtype_val).subtype_mk _).prodMk
      (continuous_snd.comp continuous_subtype_val)
  exact (hjoint.comp hlift).congr fun p => rfl

end ContinuousFlexibility.Statements
