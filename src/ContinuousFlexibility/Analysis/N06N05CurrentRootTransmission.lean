module

public import ContinuousFlexibility.Analysis.N06N05LocalModalTraces
public import ContinuousFlexibility.Analysis.N06PositiveRootFirstJets
public import ContinuousFlexibility.Analysis.N06ReferenceRootTransmission
public import ContinuousFlexibility.Radial.R11bFiniteSynthesis

/-!
# Current root transmission of modes from the same original N05 graph

The original physical weak graph supplies the modal value and derivative
matching. The actual reference root jets then identify the canonical
modal traces. Finally the current root jets transport any finite cosine
sum to equal physical values and conormals. No modal or canonical matching
condition is an input.

The geometric root-jet records can be supplied by the actual characteristic
and positive-interpolation constructors. Their realization by the chosen
`K` remains a construction obligation; the frozen N05 statement does not
assert that every possible atlas has these germs. This finite-synthesis
identity also does not assert convergence of the full boundary trace.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter MeasureTheory
open ContinuousFlexibility.Statements ContinuousFlexibility.Radial
open scoped ContDiff Topology BigOperators

set_option backward.isDefEq.respectTransparency false

/-- An actual atlas realization by germs transfers the computed root
jets. This uses ordinary derivatives of equal local functions. -/
theorem N06RootFirstJets.congr_of_germs
    {F F' : PolarPoint → PolarPoint} {h h' : PolarPoint → ℝ}
    {r y σ : ℝ} {β H ρ κ Hr : ℝ → ℝ}
    (J : N06RootFirstJets F h r y σ β H ρ κ Hr)
    (hF : ∀ θ, F' =ᶠ[𝓝 (r, θ)] F)
    (hh : ∀ θ, h' =ᶠ[𝓝 (r, θ)] h) :
    N06RootFirstJets F' h' r y σ β H ρ κ Hr := by
  refine ⟨fun θ => (J.chart_differentiable θ).congr_of_eventuallyEq (hF θ),
    fun θ => (J.height_differentiable θ).congr_of_eventuallyEq (hh θ),
    fun θ => (hF θ).eq_of_nhds.trans (J.chart_value θ),
    fun θ => (hh θ).eq_of_nhds.trans (J.height_value θ), ?_, ?_⟩
  · intro θ
    rw [(hF θ).fderiv_eq (𝕜 := ℝ)]
    exact J.chart_radial θ
  · intro θ
    change fderiv ℝ h' (r, θ) (1, 0) = _
    rw [(hh θ).fderiv_eq (𝕜 := ℝ)]
    exact J.height_radial θ

/-- Restricting the genuine height and chart derivatives to the physical
radius gives the derivative of the actual reconstructed scalar mode. -/
theorem N06RootFirstJets.radialMode_deriv
    {F : PolarPoint → PolarPoint} {h : PolarPoint → ℝ}
    {r y σ : ℝ} {β H ρ κ Hr : ℝ → ℝ}
    (J : N06RootFirstJets F h r y σ β H ρ κ Hr)
    {v : ℝ → ℝ} (hv : DifferentiableAt ℝ v y) (θ : ℝ) :
    deriv (fun x => h (x, θ) * v ((F (x, θ)).1)) r =
      Hr θ * v y + H θ * (σ * ρ θ * deriv v y) := by
  have hline := (hasDerivAt_id r).prodMk (hasDerivAt_const r θ)
  have hh : HasDerivAt (fun x => h (x, θ)) (Hr θ) r := by
    have he := (J.height_differentiable θ).hasFDerivAt.comp_hasDerivAt r hline
    have hHr : fderiv ℝ h (r, θ) (1, 0) = Hr θ := J.height_radial θ
    simpa only [Function.comp_def, id_eq, hHr] using he
  have hF : HasDerivAt (fun x => (F (x, θ)).1) (σ * ρ θ) r := by
    have he := (J.chart_differentiable θ).hasFDerivAt.fst.comp_hasDerivAt r hline
    simpa only [Function.comp_def, id_eq, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.coe_fst', J.chart_radial θ] using he
  have hv' : HasDerivAt v (deriv v y) ((F (r, θ)).1) := by
    simpa only [J.chart_value θ] using hv.hasDerivAt
  have hd := (hh.mul (hv'.comp r hF)).deriv
  simpa only [Function.comp_def, Pi.mul_def, J.chart_value θ, J.height_value θ,
    mul_comm (deriv v y) (σ * ρ θ)] using hd

/-- The literal N05 graph, followed by cancellation of the common actual
reference height and scale, gives the canonical scalar-mode traces. -/
theorem n06N05_canonicalMode_root_traces
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
    {yl yr σl σr : ℝ} {β H ρ κ Hr : ℝ → ℝ}
    (Jl : N06RootFirstJets (K.chart (C.referenceState, 0) ml)
      (K.height (C.referenceState, 0) ml) (K.physicalRight ml) yl σl β H ρ κ Hr)
    (Jr : N06RootFirstJets (K.chart (C.referenceState, 0) mr)
      (K.height (C.referenceState, 0) mr) (K.physicalRight ml) yr σr β H ρ κ Hr)
    (hH : H 0 ≠ 0) (hρ : ρ 0 ≠ 0)
    (hvl : ContDiff ℝ 1 vl) (hvr : ContDiff ℝ 1 vr)
    (hmodeL : n06HalfCosineCoefficient (u.val.1.1 ml) n
      =ᵐ[volume.restrict (Ioo (K.left ml) (K.right ml))] vl)
    (hmodeR : n06HalfCosineCoefficient (u.val.1.1 mr) n
      =ᵐ[volume.restrict (Ioo (K.left mr) (K.right mr))] vr) :
    vl yl = vr yr ∧ σl * deriv vl yl = σr * deriv vr yr := by
  have ht := n06N05_canonicalModes_physical_traces_local hS h hcoordinates u ml mr n vl vr
    hjoin hroot hvl hvr hmodeL hmodeR
  dsimp only at ht
  have hvalue : vl yl = vr yr := by
    apply mul_left_cancel₀ hH
    simpa only [Jl.height_value 0, Jr.height_value 0,
      Jl.chart_value 0, Jr.chart_value 0] using ht.1
  refine ⟨hvalue, ?_⟩
  have hder := ht.2.1
  rw [Jl.radialMode_deriv (hvl.differentiable (by norm_num) yl) 0,
    Jr.radialMode_deriv (hvr.differentiable (by norm_num) yr) 0, hvalue] at hder
  apply mul_left_cancel₀ (mul_ne_zero hH hρ)
  change (H 0 * ρ 0) * (σl * deriv vl yl) =
    (H 0 * ρ 0) * (σr * deriv vr yr)
  linear_combination hder

private theorem n06_finite_modes_differentiable
    (s : Finset ℕ) (v : ℕ → ℝ → ℝ) (y θ : ℝ)
    (hv : ∀ n ∈ s, DifferentiableAt ℝ (v n) y) :
    DifferentiableAt ℝ (r11bFiniteSynthesis s v referenceAngularBasis) (y, θ) := by
  change DifferentiableAt ℝ
    (fun p : PolarPoint => ∑ n ∈ s, v n p.1 * referenceAngularBasis n p.2) (y, θ)
  apply DifferentiableAt.fun_sum
  intro n hn
  simpa only [Pi.mul_def, Function.comp_def] using
    ((hv n hn).comp (y, θ) differentiableAt_fst).mul
      (((contDiff_referenceAngularBasis n).differentiable (by simp) θ).comp
        (y, θ) differentiableAt_snd)

private theorem n06_finite_modes_radial
    (s : Finset ℕ) (v : ℕ → ℝ → ℝ) (y θ : ℝ)
    (hv : ∀ n ∈ s, DifferentiableAt ℝ (v n) y) :
    radialPartial (r11bFiniteSynthesis s v referenceAngularBasis) (y, θ) =
      ∑ n ∈ s, deriv (v n) y * referenceAngularBasis n θ := by
  have hplane := n06_finite_modes_differentiable s v y θ hv
  have hline := hplane.hasFDerivAt.comp_hasDerivAt y
    ((hasDerivAt_id y).prodMk (hasDerivAt_const y θ))
  have hsum : HasDerivAt (fun x => r11bFiniteSynthesis s v referenceAngularBasis (x, θ))
      (∑ n ∈ s, deriv (v n) y * referenceAngularBasis n θ) y :=
    HasDerivAt.fun_sum (fun n hn => (hv n hn).hasDerivAt.mul_const (referenceAngularBasis n θ))
  exact hline.unique hsum

/-- Every finite reconstruction of the same original graph element has
the common current physical value and conormal. The hypotheses on the
modal representatives are regularity and representation, never matching. -/
theorem n06N05_finite_current_root_conormal
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
    {yl yr σl σr : ℝ} {β₀ H₀ ρ₀ κ₀ Hr₀ β H ρ κ Hr : ℝ → ℝ}
    (Jl₀ : N06RootFirstJets (K.chart (C.referenceState, 0) ml)
      (K.height (C.referenceState, 0) ml) (K.physicalRight ml) yl σl β₀ H₀ ρ₀ κ₀ Hr₀)
    (Jr₀ : N06RootFirstJets (K.chart (C.referenceState, 0) mr)
      (K.height (C.referenceState, 0) mr) (K.physicalRight ml) yr σr β₀ H₀ ρ₀ κ₀ Hr₀)
    (hH₀ : H₀ 0 ≠ 0) (hρ₀ : ρ₀ 0 ≠ 0)
    {Fl Fr : PolarPoint → PolarPoint} {hl hr : PolarPoint → ℝ}
    (Jl : N06RootFirstJets Fl hl (K.physicalRight ml) yl σl β H ρ κ Hr)
    (Jr : N06RootFirstJets Fr hr (K.physicalRight ml) yr σr β H ρ κ Hr)
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
  have htrace (n : ℕ) (hn : n ∈ s) :=
    n06N05_canonicalMode_root_traces hS h hcoordinates u ml mr n (vl n) (vr n)
      hjoin hroot Jl₀ Jr₀ hH₀ hρ₀ (hvl n hn) (hvr n hn)
      (hmodeL n hn) (hmodeR n hn)
  have hvlAt : ∀ n ∈ s, DifferentiableAt ℝ (vl n) yl :=
    fun n hn => (hvl n hn).differentiable (by norm_num) yl
  have hvrAt : ∀ n ∈ s, DifferentiableAt ℝ (vr n) yr :=
    fun n hn => (hvr n hn).differentiable (by norm_num) yr
  have hvalue (η : ℝ) : r11bFiniteSynthesis s vl referenceAngularBasis (yl, η) =
      r11bFiniteSynthesis s vr referenceAngularBasis (yr, η) := by
    apply Finset.sum_congr rfl
    intro n hn
    rw [(htrace n hn).1]
  have hnormal (η : ℝ) :
      σl * radialPartial (r11bFiniteSynthesis s vl referenceAngularBasis) (yl, η) =
        σr * radialPartial (r11bFiniteSynthesis s vr referenceAngularBasis) (yr, η) := by
    rw [n06_finite_modes_radial s vl yl η hvlAt,
      n06_finite_modes_radial s vr yr η hvrAt, Finset.mul_sum, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro n hn
    rw [← mul_assoc, (htrace n hn).2, mul_assoc]
  have hmatch := n06_root_reconstruction_firstJets_match Jl Jr
    (fun η => n06_finite_modes_differentiable s vl yl η hvlAt)
    (fun η => n06_finite_modes_differentiable s vr yr η hvrAt) hvalue hnormal θ
  exact ⟨hmatch.1, by simp only [symmetricNormalFlux, hmatch.2.1, hmatch.2.2]⟩

end ContinuousFlexibility.Analysis
