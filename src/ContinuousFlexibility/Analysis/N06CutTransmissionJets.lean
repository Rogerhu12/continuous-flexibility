import ContinuousFlexibility.Analysis.N06RootBoundaryCancellation

/-!
# Actual first jets at a negative middle cut

The two radial chart directions are opposite. Their height normal jets
differ by the affine correction dictated by the actual forward charts.
The scalar parameter is `1 / (2 * R)` for the canonical cut of radius R.

The original N05 graph, rather than the totalized inverse-chart values at
an endpoint, supplies the matching physical modal traces. Cancellation of
the actual nonzero reference height and chart scale gives the affine
canonical relation. It then transports every common finite reconstruction
to matching current physical values and conormals.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter MeasureTheory
open ContinuousFlexibility.Statements ContinuousFlexibility.Radial
open scoped ContDiff Topology BigOperators

set_option backward.isDefEq.respectTransparency false

/-- The affine cut law follows from true first jets of two physical
pullbacks. Only the actual boundary height and radial scale are cancelled. -/
theorem n06_cut_scalar_traces_of_physical_jets
    {Fl Fr : PolarPoint → PolarPoint} {hl hr : PolarPoint → ℝ}
    {r y σ τ : ℝ} {β H ρ κ Hr : ℝ → ℝ} {vl vr : ℝ → ℝ}
    (Jl : N06RootFirstJets Fl hl r y σ β H ρ κ Hr)
    (Jr : N06RootFirstJets Fr hr r y (-σ) β H ρ κ
      (fun θ => Hr θ - H θ * (σ * ρ θ) * τ))
    (hH : H 0 ≠ 0) (hscale : σ * ρ 0 ≠ 0)
    (hvl : DifferentiableAt ℝ vl y) (hvr : DifferentiableAt ℝ vr y)
    (hvalue : hl (r, 0) * vl ((Fl (r, 0)).1) =
      hr (r, 0) * vr ((Fr (r, 0)).1))
    (hderiv : deriv (fun x => hl (x, 0) * vl ((Fl (x, 0)).1)) r =
      deriv (fun x => hr (x, 0) * vr ((Fr (x, 0)).1)) r) :
    vl y = vr y ∧ deriv vl y + deriv vr y = -τ * vl y := by
  have hv : vl y = vr y := by
    apply mul_left_cancel₀ hH
    simpa only [Jl.height_value 0, Jr.height_value 0,
      Jl.chart_value 0, Jr.chart_value 0] using hvalue
  refine ⟨hv, ?_⟩
  rw [Jl.radialMode_deriv hvl 0, Jr.radialMode_deriv hvr 0, hv] at hderiv
  apply mul_left_cancel₀ (mul_ne_zero hH hscale)
  rw [hv]
  change (H 0 * (σ * ρ 0)) * (deriv vl y + deriv vr y) =
    (H 0 * (σ * ρ 0)) * (-τ * vr y)
  linear_combination hderiv

/-- A genuine affine canonical cut relation gives equality of the three
physical first jets. The angular drift and the height derivative remain
in the chain rule and cancel with their actual values. -/
theorem n06_cut_reconstruction_firstJets_match
    {Fl Fr : PolarPoint → PolarPoint} {hl hr Wl Wr : PolarPoint → ℝ}
    {r y σ τ : ℝ} {β H ρ κ Hr : ℝ → ℝ}
    (Jl : N06RootFirstJets Fl hl r y σ β H ρ κ Hr)
    (Jr : N06RootFirstJets Fr hr r y (-σ) β H ρ κ
      (fun θ => Hr θ - H θ * (σ * ρ θ) * τ))
    (hWl : ∀ η, DifferentiableAt ℝ Wl (y, η))
    (hWr : ∀ η, DifferentiableAt ℝ Wr (y, η))
    (hvalue : ∀ η, Wl (y, η) = Wr (y, η))
    (hnormal : ∀ η,
      radialPartial Wl (y, η) + radialPartial Wr (y, η) = -τ * Wl (y, η))
    (θ : ℝ) :
    hl (r, θ) * Wl (Fl (r, θ)) = hr (r, θ) * Wr (Fr (r, θ)) ∧
      radialPartial (fun p => hl p * Wl (Fl p)) (r, θ) =
        radialPartial (fun p => hr p * Wr (Fr p)) (r, θ) ∧
      angularPartial (fun p => hl p * Wl (Fl p)) (r, θ) =
        angularPartial (fun p => hr p * Wr (Fr p)) (r, θ) := by
  have ht := n06_angularPartial_eq_of_boundary_values
    (hWl (β θ)) (hWr (β θ)) hvalue
  have hn := hnormal (β θ)
  rw [hvalue (β θ)] at hn
  refine ⟨?_, ?_, ?_⟩
  · rw [Jl.reconstruction_value Wl θ, Jr.reconstruction_value Wr θ, hvalue (β θ)]
  · rw [Jl.reconstruction_radial θ (hWl (β θ)),
      Jr.reconstruction_radial θ (hWr (β θ)), hvalue (β θ), ht]
    linear_combination (H θ * (σ * ρ θ)) * hn
  · rw [Jl.reconstruction_angular θ (hWl (β θ)),
      Jr.reconstruction_angular θ (hWr (β θ)), hvalue (β θ), ht]

/-- The same original N05 graph forces the affine cut traces of each
actual C1 canonical mode. All nonvanishing used here comes from N04's
closed forward chart and positive height, not a separate trace premise. -/
theorem n06N05_canonicalMode_cut_traces
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {R : ReturnEquationData S}
    {L : ReturnCorrectionData S} {K : CanonicalData S} {V : VolumeModelData S K}
    {base loss b : ℕ} {ε : ℝ} {B : CanonicalDomainData S K V b}
    (hS : IsPhysicalSpaces D T S)
    (h : NonlinearPropertiesThrough05 D T S C R L K V b B base loss ε)
    (hcoordinates : N05ControlledReferenceCoordinates D S C K)
    (u : B.Space) (ml mr n : ℕ) (vl vr : ℝ → ℝ)
    (hjoin : K.physicalRight ml = K.physicalLeft mr)
    (hroot : K.physicalRight ml ∈ radialCore D)
    {y σ τ : ℝ} {β H ρ κ Hr : ℝ → ℝ}
    (Jl : N06RootFirstJets (K.chart (C.referenceState, 0) ml)
      (K.height (C.referenceState, 0) ml) (K.physicalRight ml) y σ β H ρ κ Hr)
    (Jr : N06RootFirstJets (K.chart (C.referenceState, 0) mr)
      (K.height (C.referenceState, 0) mr) (K.physicalRight ml) y (-σ) β H ρ κ
        (fun θ => Hr θ - H θ * (σ * ρ θ) * τ))
    (hvl : ContDiff ℝ 1 vl) (hvr : ContDiff ℝ 1 vr)
    (hmodeL : n06HalfCosineCoefficient (u.val.1.1 ml) n
      =ᵐ[volume.restrict (Ioo (K.left ml) (K.right ml))] vl)
    (hmodeR : n06HalfCosineCoefficient (u.val.1.1 mr) n
      =ᵐ[volume.restrict (Ioo (K.left mr) (K.right mr))] vr) :
    vl y = vr y ∧ deriv vl y + deriv vr y = -τ * vl y := by
  have ht := n06N05_canonicalModes_physical_traces_local hS h hcoordinates u ml mr n vl vr
    hjoin hroot hvl hvr hmodeL hmodeR
  have h01 : N01Properties D T S C base loss ε := h.1.1.1.1
  have h04 : N04Properties D T S C L K base loss ε := h.1.2.2.2.2
  have href : (C.referenceState, 0) ∈ stateNeighborhood S C base ε :=
    n05_referenceState_mem (S := S) (C := C) (base := base) h01.2.1
  have hs : stateSector S C.referenceState := n05_referenceState_sector h01.2.2.1
  have hclosed := h04.2.2.2.2.2.2.2.2.1 (C.referenceState, 0) href hs ml
    (K.physicalRight ml, 0) ⟨(h04.2.2.2.1 ml).1.le, le_rfl⟩
  have hH : H 0 ≠ 0 := by
    simpa only [Jl.height_value 0] using hclosed.2.2.2.ne'
  have hscale : σ * ρ 0 ≠ 0 := (mul_ne_zero_iff.mp
    (show (σ * ρ 0) * deriv β 0 ≠ 0 by
      simpa only [Jl.jacobian 0] using hclosed.2.2.1)).1
  exact n06_cut_scalar_traces_of_physical_jets Jl Jr hH hscale
    (hvl.differentiable (by norm_num) y) (hvr.differentiable (by norm_num) y) ht.1 ht.2.1

/-- Finite C1 tensors have their genuine first radial derivative. This
version retains the weak modes' regularity and requires no smooth source. -/
theorem n06_contDiff_one_finiteSynthesis {ι : Type*}
    (s : Finset ι) (v e : ι → ℝ → ℝ)
    (hv : ∀ i ∈ s, ContDiff ℝ 1 (v i)) (he : ∀ i ∈ s, ContDiff ℝ 1 (e i)) :
    ContDiff ℝ 1 (r11bFiniteSynthesis s v e) :=
  ContDiff.sum (fun i hi =>
    ((hv i hi).comp contDiff_fst).mul ((he i hi).comp contDiff_snd))

theorem n06_radialPartial_finiteSynthesis_one {ι : Type*}
    (s : Finset ι) (v e : ι → ℝ → ℝ)
    (hv : ∀ i ∈ s, ContDiff ℝ 1 (v i)) (he : ∀ i ∈ s, ContDiff ℝ 1 (e i)) :
    radialPartial (r11bFiniteSynthesis s v e) =
      r11bFiniteSynthesis s (fun i => deriv (v i)) e := by
  funext p
  rw [← deriv_cylinder_radial_slice
    ((n06_contDiff_one_finiteSynthesis s v e hv he).differentiable (by norm_num)) p.1 p.2]
  exact (HasDerivAt.fun_sum (fun i hi =>
    ((hv i hi).differentiable (by norm_num) p.1).hasDerivAt.mul_const (e i p.2))).deriv

/-- A common finite synthesis preserves both the value and affine normal
relation. The parameter stays independent of the mode and angular point. -/
theorem n06_finiteSynthesis_cut_traces {ι : Type*}
    (s : Finset ι) (vl vr e : ι → ℝ → ℝ) {y τ : ℝ}
    (hvl : ∀ i ∈ s, ContDiff ℝ 1 (vl i))
    (hvr : ∀ i ∈ s, ContDiff ℝ 1 (vr i))
    (he : ∀ i ∈ s, ContDiff ℝ 1 (e i))
    (htrace : ∀ i ∈ s,
      vl i y = vr i y ∧ deriv (vl i) y + deriv (vr i) y = -τ * vl i y)
    (θ : ℝ) :
    r11bFiniteSynthesis s vl e (y, θ) = r11bFiniteSynthesis s vr e (y, θ) ∧
      radialPartial (r11bFiniteSynthesis s vl e) (y, θ) +
          radialPartial (r11bFiniteSynthesis s vr e) (y, θ) =
        -τ * r11bFiniteSynthesis s vl e (y, θ) := by
  constructor
  · apply Finset.sum_congr rfl
    intro i hi
    rw [(htrace i hi).1]
  · rw [n06_radialPartial_finiteSynthesis_one s vl e hvl he,
      n06_radialPartial_finiteSynthesis_one s vr e hvr he]
    change (∑ i ∈ s, deriv (vl i) y * e i θ) +
        (∑ i ∈ s, deriv (vr i) y * e i θ) = -τ * ∑ i ∈ s, vl i y * e i θ
    rw [← Finset.sum_add_distrib, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    calc
      _ = (deriv (vl i) y + deriv (vr i) y) * e i θ := by ring
      _ = _ := by rw [(htrace i hi).2]; ring

/-- Finite modes of the same original graph match the current physical
value and conormal at the affine cut. The only additional inputs describe
the realization of the actual reference and current forward first jets. -/
theorem n06N05_finite_current_cut_conormal
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {R : ReturnEquationData S}
    {L : ReturnCorrectionData S} {K : CanonicalData S} {V : VolumeModelData S K}
    {base loss b : ℕ} {ε : ℝ} {B : CanonicalDomainData S K V b}
    (hS : IsPhysicalSpaces D T S)
    (h : NonlinearPropertiesThrough05 D T S C R L K V b B base loss ε)
    (hcoordinates : N05ControlledReferenceCoordinates D S C K)
    (u : B.Space) (ml mr : ℕ) (s : Finset ℕ) (vl vr : ℕ → ℝ → ℝ)
    (hjoin : K.physicalRight ml = K.physicalLeft mr)
    (hroot : K.physicalRight ml ∈ radialCore D)
    {y σ τ : ℝ} {β₀ H₀ ρ₀ κ₀ Hr₀ β H ρ κ Hr : ℝ → ℝ}
    (Jl₀ : N06RootFirstJets (K.chart (C.referenceState, 0) ml)
      (K.height (C.referenceState, 0) ml) (K.physicalRight ml) y σ β₀ H₀ ρ₀ κ₀ Hr₀)
    (Jr₀ : N06RootFirstJets (K.chart (C.referenceState, 0) mr)
      (K.height (C.referenceState, 0) mr) (K.physicalRight ml) y (-σ) β₀ H₀ ρ₀ κ₀
        (fun θ => Hr₀ θ - H₀ θ * (σ * ρ₀ θ) * τ))
    {Fl Fr : PolarPoint → PolarPoint} {hl hr : PolarPoint → ℝ}
    (Jl : N06RootFirstJets Fl hl (K.physicalRight ml) y σ β H ρ κ Hr)
    (Jr : N06RootFirstJets Fr hr (K.physicalRight ml) y (-σ) β H ρ κ
      (fun θ => Hr θ - H θ * (σ * ρ θ) * τ))
    (hvl : ∀ n ∈ s, ContDiff ℝ 1 (vl n))
    (hvr : ∀ n ∈ s, ContDiff ℝ 1 (vr n))
    (hmodeL : ∀ n ∈ s, n06HalfCosineCoefficient (u.val.1.1 ml) n
      =ᵐ[volume.restrict (Ioo (K.left ml) (K.right ml))] vl n)
    (hmodeR : ∀ n ∈ s, n06HalfCosineCoefficient (u.val.1.1 mr) n
      =ᵐ[volume.restrict (Ioo (K.left mr) (K.right mr))] vr n)
    (A M : PolarPoint → ℝ) (θ : ℝ) :
    hl (K.physicalRight ml, θ) * r11bFiniteSynthesis s vl referenceAngularBasis
        (Fl (K.physicalRight ml, θ)) =
      hr (K.physicalRight ml, θ) * r11bFiniteSynthesis s vr referenceAngularBasis
        (Fr (K.physicalRight ml, θ)) ∧
    symmetricNormalFlux A M
        (fun p => hl p * r11bFiniteSynthesis s vl referenceAngularBasis (Fl p))
        (K.physicalRight ml, θ) =
      symmetricNormalFlux A M
        (fun p => hr p * r11bFiniteSynthesis s vr referenceAngularBasis (Fr p))
        (K.physicalRight ml, θ) := by
  have he : ∀ n ∈ s, ContDiff ℝ 1 (referenceAngularBasis n) :=
    fun n _ => (contDiff_referenceAngularBasis n).of_le (by simp)
  have htrace (n : ℕ) (hn : n ∈ s) :=
    n06N05_canonicalMode_cut_traces hS h hcoordinates u ml mr n (vl n) (vr n)
      hjoin hroot Jl₀ Jr₀ (hvl n hn) (hvr n hn) (hmodeL n hn) (hmodeR n hn)
  have hsum (η : ℝ) := n06_finiteSynthesis_cut_traces s vl vr referenceAngularBasis
    hvl hvr he htrace η
  have hdl := (n06_contDiff_one_finiteSynthesis s vl referenceAngularBasis hvl he).differentiable
    (by norm_num)
  have hdr := (n06_contDiff_one_finiteSynthesis s vr referenceAngularBasis hvr he).differentiable
    (by norm_num)
  have hj := n06_cut_reconstruction_firstJets_match Jl Jr (fun η => hdl (y, η))
    (fun η => hdr (y, η)) (fun η => (hsum η).1) (fun η => (hsum η).2) θ
  exact ⟨hj.1, by simp only [symmetricNormalFlux, hj.2.1, hj.2.2]⟩

end ContinuousFlexibility.Analysis
