import ContinuousFlexibility.Analysis.N06RootTraceFromInterior
import ContinuousFlexibility.Radial.R11bEvenModeRegularity
import ContinuousFlexibility.Statements.Nonlinear

/-!
# Actual modal interface traces of the same N05 reference graph

The existing radial graph regularity theorem supplies a C1 representative
of each original even Fourier coefficient throughout the open annulus.
Continuity and uniqueness of one-sided derivatives identify the jets of
any two C1 piece representatives at their common interior cut. Applying
this to N05 retains its own physical representatives and all scalar
coordinates, including the actual space model's left cutoff and psi.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter MeasureTheory ContinuousFlexibility.Radial
open ContinuousFlexibility.Statements
open scoped ContDiff Topology

/-- Interface compatibility of the actual Fourier coefficients, with no
condition imposed on arbitrary extensions outside their own pieces. -/
def N06PhysicalModalInterfaceTraces (D : ReferenceData) (η : PolarPoint → ℝ) : Prop :=
  ∀ n : ℕ, ∀ l r s : ℝ, l < r → r < s → Icc l s ⊆ radialCore D →
    ∀ vl vr : ℝ → ℝ, ContDiff ℝ 1 vl → ContDiff ℝ 1 vr →
      evenFourierCoefficient η n =ᵐ[volume.restrict (Ioo l r)] vl →
      evenFourierCoefficient η n =ᵐ[volume.restrict (Ioo r s)] vr →
        vl r = vr r ∧ deriv vl r = deriv vr r ∧
          D.w r * deriv vl r = D.w r * deriv vr r

/-- Matching physical modal values and fluxes are consequences of the
original maximal weak graph, including its genuine mode-two border. -/
theorem n06_referenceGraph_physicalModalInterfaceTraces
    {D : ReferenceData} (hD : IsAccumulatingProfile D) (hb : RadialTrueBorder D)
    {γ M₀ M₁ : ℝ} (hγ : 0 < γ) {U : RadialUnknown} {F : RadialSource}
    (hgraph : ReferenceGraph D γ M₀ M₁ U F) :
    N06PhysicalModalInterfaceTraces D U.1 := by
  intro n l r s hlr hrs hcore vl vr hvl hvr hleft hright
  have hr : r ∈ radialCore D := hcore ⟨hlr.le, hrs.le⟩
  obtain ⟨v, _, hcoeff, hv, _⟩ :=
    r11b_evenCoefficient_contDiffOn_one_representative hD hb hγ hgraph n r hr
  have hsubL : Ioo l r ⊆ radialCore D := fun _ hx =>
    hcore ⟨hx.1.le, (hx.2.trans hrs).le⟩
  have hsubR : Ioo r s ⊆ radialCore D := fun _ hx =>
    hcore ⟨(hlr.trans hx.1).le, hx.2.le⟩
  have hvAt : DifferentiableAt ℝ v r :=
    (hv.contDiffAt (isOpen_Ioo.mem_nhds hr)).differentiableAt (by norm_num)
  have hlv : vl =ᵐ[volume.restrict (Ioo l r)] v :=
    hleft.symm.trans (ae_restrict_of_ae_restrict_of_subset hsubL hcoeff)
  have hrv : vr =ᵐ[volume.restrict (Ioo r s)] v :=
    hright.symm.trans (ae_restrict_of_ae_restrict_of_subset hsubR hcoeff)
  have hleq : EqOn vl v (Ioo l r) := Measure.eqOn_open_of_ae_eq hlv isOpen_Ioo
    hvl.continuous.continuousOn (hv.continuousOn.mono hsubL)
  have hreq : EqOn vr v (Ioo r s) := Measure.eqOn_open_of_ae_eq hrv isOpen_Ioo
    hvr.continuous.continuousOn (hv.continuousOn.mono hsubR)
  have hL := n06_cauchyData_eq_of_eqOn_Ioo_left hlr
    (hvl.differentiable (by norm_num) r) hvAt hleq
  have hR := cauchyData_eq_of_eqOn_Ioo_right hrs
    (hvr.differentiable (by norm_num) r) hvAt hreq
  have hd : deriv vl r = deriv vr r := hL.2.trans hR.2.symm
  exact ⟨hL.1.trans hR.1.symm, hd, congrArg (D.w r * ·) hd⟩

end ContinuousFlexibility.Analysis

namespace ContinuousFlexibility.Statements

open ContinuousFlexibility.Analysis

set_option backward.isDefEq.respectTransparency false

/-- Every element of the chosen N05 graph has its original physical
representatives with actual modal interface traces. No smooth source,
extra domain condition, or change of scalar normalization is used. -/
theorem n06N05_exists_physical_modal_traces
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {R : ReturnEquationData S}
    {L : ReturnCorrectionData S} {K : CanonicalData S} {V : VolumeModelData S K}
    {base loss b : ℕ} {ε : ℝ} {B : CanonicalDomainData S K V b}
    (h : NonlinearPropertiesThrough05 D T S C R L K V b B base loss ε)
    (u : B.Space) :
    ∃ η f : PolarPoint → ℝ,
      HasCanonicalRepresentation D S C K (C.referenceState, 0) u.val.1
        (V.forget (3 / 4 : ℝ) 0 b u.val.2) η f ∧
      ReferenceGraph D B.weakExponent B.sourceMaterial B.outputMaterial
        (η, u.val.1.2.2.1)
        ((fun p => f p - u.val.1.2.2.2 * (S.height (3 / 4 : ℝ)).decode S.psi p), 0) ∧
      N06PhysicalModalInterfaceTraces D η := by
  have h05 : N05Properties D T S C K V b B := h.2
  have h01 : N01Properties D T S C base loss ε := h.1.1.1.1
  have hrel := (h05.2.2.2.2.2.2.1 u.val).mp u.property
  obtain ⟨_, η, f, hrep, hgraph⟩ := hrel
  exact ⟨η, f, hrep, hgraph,
    n06_referenceGraph_physicalModalInterfaceTraces h01.1.1 h01.1.2.2.2.1
      h05.2.2.1 hgraph⟩

end ContinuousFlexibility.Statements
