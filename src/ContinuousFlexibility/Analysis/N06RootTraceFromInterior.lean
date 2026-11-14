module

public import ContinuousFlexibility.Analysis.N06ReferenceRootTransmission
public import ContinuousFlexibility.Radial.R07NaturalLineNormalization
public import ContinuousFlexibility.Scalar.Conservation

/-!
# Root traces from the actual one-sided piece interiors

The reference representations need agree with one physical C¹ field only
inside their respective pieces. Their arbitrary extensions past the root
are not required to agree. Continuity and uniqueness of one-sided
derivatives identify the actual endpoint values and radial first jets,
which then give the shared canonical traces and current conormals.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter Real ContinuousFlexibility.Radial
open scoped ContDiff Topology

theorem n06_cauchyData_eq_of_eqOn_Ioo_left {f g : ℝ → ℝ} {a b : ℝ}
    (hab : a < b) (hf : DifferentiableAt ℝ f b) (hg : DifferentiableAt ℝ g b)
    (heq : EqOn f g (Ioo a b)) : f b = g b ∧ deriv f b = deriv g b := by
  have he : f =ᶠ[𝓝[<] b] g := by
    filter_upwards [mem_nhdsWithin_of_mem_nhds (Ioi_mem_nhds hab), self_mem_nhdsWithin]
      with x hxa hxb
    exact heq ⟨hxa, hxb⟩
  have hv : f b = g b := tendsto_nhds_unique_of_eventuallyEq
    (hf.continuousAt.tendsto.mono_left nhdsWithin_le_nhds)
    (hg.continuousAt.tendsto.mono_left nhdsWithin_le_nhds) he
  refine ⟨hv, ?_⟩
  have hdf : HasDerivWithinAt f (deriv f b) (Iio b) b := hf.hasDerivAt.hasDerivWithinAt
  have hdg : HasDerivWithinAt g (deriv g b) (Iio b) b := hg.hasDerivAt.hasDerivWithinAt
  exact (hdf.derivWithin (uniqueDiffWithinAt_Iio b)).symm.trans
    ((he.derivWithin_eq hv).trans (hdg.derivWithin (uniqueDiffWithinAt_Iio b)))

theorem n06_physical_firstJets_from_piece_interiors
    {ul ur η : PolarPoint → ℝ} {l r u : ℝ}
    (hlr : l < r) (hru : r < u)
    (hl : ∀ θ, DifferentiableAt ℝ ul (r, θ))
    (hr : ∀ θ, DifferentiableAt ℝ ur (r, θ))
    (hη : ∀ θ, DifferentiableAt ℝ η (r, θ))
    (hleft : ∀ θ, EqOn (fun x => ul (x, θ)) (fun x => η (x, θ)) (Ioo l r))
    (hright : ∀ θ, EqOn (fun x => ur (x, θ)) (fun x => η (x, θ)) (Ioo r u)) :
    (∀ θ, ul (r, θ) = ur (r, θ)) ∧
      ∀ θ, radialPartial ul (r, θ) = radialPartial ur (r, θ) := by
  have hL (θ : ℝ) := n06_cauchyData_eq_of_eqOn_Ioo_left hlr
    (hasDerivAt_radial_slice (hl θ)).differentiableAt
    (hasDerivAt_radial_slice (hη θ)).differentiableAt (hleft θ)
  have hR (θ : ℝ) := cauchyData_eq_of_eqOn_Ioo_right hru
    (hasDerivAt_radial_slice (hr θ)).differentiableAt
    (hasDerivAt_radial_slice (hη θ)).differentiableAt (hright θ)
  refine ⟨fun θ => (hL θ).1.trans (hR θ).1.symm, ?_⟩
  intro θ
  exact (hasDerivAt_radial_slice (hl θ)).deriv.symm.trans
    (((hL θ).2.trans (hR θ).2.symm).trans (hasDerivAt_radial_slice (hr θ)).deriv)

/-- The actual reference piece identities supply canonical root traces
even when the chosen C¹ representatives have unrelated outside extensions. -/
theorem n06_reference_root_traces_from_interiors
    {Fl Fr : PolarPoint → PolarPoint} {hl hr Wl Wr η : PolarPoint → ℝ}
    {l r u yl yr σl σr : ℝ} {H ρ κ Hr : ℝ → ℝ}
    (Jl : N06RootFirstJets Fl hl r yl σl (fun θ => θ) H ρ κ Hr)
    (Jr : N06RootFirstJets Fr hr r yr σr (fun θ => θ) H ρ κ Hr)
    (hlr : l < r) (hru : r < u)
    (hH : ∀ θ, H θ ≠ 0)
    (hJac : ∀ θ, planeJacobian Fl (r, θ) ≠ 0)
    (hWl : ∀ θ, DifferentiableAt ℝ Wl (yl, θ))
    (hWr : ∀ θ, DifferentiableAt ℝ Wr (yr, θ))
    (hη : ∀ θ, DifferentiableAt ℝ η (r, θ))
    (hleft : ∀ θ, EqOn (fun x => hl (x, θ) * Wl (Fl (x, θ)))
      (fun x => η (x, θ)) (Ioo l r))
    (hright : ∀ θ, EqOn (fun x => hr (x, θ) * Wr (Fr (x, θ)))
      (fun x => η (x, θ)) (Ioo r u)) :
    (∀ θ, Wl (yl, θ) = Wr (yr, θ)) ∧
      ∀ θ, σl * radialPartial Wl (yl, θ) = σr * radialPartial Wr (yr, θ) := by
  have hlSmooth (θ : ℝ) : DifferentiableAt ℝ (fun p => hl p * Wl (Fl p)) (r, θ) := by
    have hw : DifferentiableAt ℝ Wl (Fl (r, θ)) := by
      simpa only [Jl.chart_value θ] using hWl θ
    exact (Jl.height_differentiable θ).mul (hw.comp (r, θ) (Jl.chart_differentiable θ))
  have hrSmooth (θ : ℝ) : DifferentiableAt ℝ (fun p => hr p * Wr (Fr p)) (r, θ) := by
    have hw : DifferentiableAt ℝ Wr (Fr (r, θ)) := by
      simpa only [Jr.chart_value θ] using hWr θ
    exact (Jr.height_differentiable θ).mul (hw.comp (r, θ) (Jr.chart_differentiable θ))
  have hmatch := n06_physical_firstJets_from_piece_interiors hlr hru
    hlSmooth hrSmooth hη hleft hright
  exact n06_reference_root_canonical_traces_of_firstJets Jl Jr hH hJac hWl hWr
    hmatch.1 hmatch.2

end ContinuousFlexibility.Analysis
