import ContinuousFlexibility.Analysis.N06ReferenceGraphRootTraces
import ContinuousFlexibility.Analysis.N06ReferenceRemainderFields
import ContinuousFlexibility.Radial.R11bRemainderModes

/-!
# Interface traces after subtracting the actual space cutoff

The reference graph supplies the physical Fourier modes of the complete
height. Canonical heights use the remainder with `S.chiLeft` removed.
Subtracting any smooth radial field changes only the mean channel and
preserves its physical value and derivative matching. This applies on the
original N05 graph, without identifying the space cutoff with `D.chiLeft`.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter MeasureTheory ContinuousFlexibility.Radial
open ContinuousFlexibility.Statements
open scoped ContDiff Topology

/-- Radial subtraction changes precisely the actual mean coefficient.
The identity is almost everywhere, using the genuine L2 angular slices. -/
theorem n06_evenFourierCoefficient_sub_radial_ae
    {D : ReferenceData} {η : PolarPoint → ℝ}
    (hη : MemLp η 2 (radialPhysicalMeasure D)) (a : ℝ → ℝ) (n : ℕ) :
    evenFourierCoefficient (fun p => η p - a p.1) n
      =ᵐ[volume.restrict (radialCore D)]
        (fun r => evenFourierCoefficient η n r - if n = 0 then a r else 0) := by
  by_cases hn : n = 0
  · subst n
    filter_upwards [r11b_radialAngularMean_sub_radial_ae hη a] with r hr
    simpa only [evenFourierCoefficient_zero_physical, ite_true] using hr
  · have hj : 0 < 2 * n := by omega
    simpa only [evenFourierCoefficient_eq_referenceMode _ hn, ite_eq_right hn, sub_zero] using
      r11b_referenceMode_sub_radial_ae hη a (2 * n) hj

/-- The trace statement is preserved under the real radial correction;
its derivative is restored on both sides before applying the original
graph's trace theorem. No boundary condition is imposed on the remainder. -/
theorem n06_physicalModalInterfaceTraces_sub_radial
    {D : ReferenceData} {η : PolarPoint → ℝ}
    (hη : MemLp η 2 (radialPhysicalMeasure D))
    (htrace : N06PhysicalModalInterfaceTraces D η)
    (a : ℝ → ℝ) (ha : ContDiff ℝ 1 a) :
    N06PhysicalModalInterfaceTraces D (fun p => η p - a p.1) := by
  intro n l r s hlr hrs hcore vl vr hvl hvr hleft hright
  let e : ℝ → ℝ := fun x => if n = 0 then a x else 0
  have he : ContDiff ℝ 1 e := by
    by_cases hn : n = 0
    · simpa only [e, ite_eq_left hn] using ha
    · simpa only [e, ite_eq_right hn] using (contDiff_const : ContDiff ℝ 1 (fun _ : ℝ => (0 : ℝ)))
  have hsubL : Ioo l r ⊆ radialCore D := fun _ hx =>
    hcore ⟨hx.1.le, (hx.2.trans hrs).le⟩
  have hsubR : Ioo r s ⊆ radialCore D := fun _ hx =>
    hcore ⟨(hlr.trans hx.1).le, hx.2.le⟩
  have hcoef := n06_evenFourierCoefficient_sub_radial_ae hη a n
  have hL : evenFourierCoefficient η n =ᵐ[volume.restrict (Ioo l r)]
      (fun x => vl x + e x) := by
    filter_upwards [hleft, ae_restrict_of_ae_restrict_of_subset hsubL hcoef] with x hx hcx
    change evenFourierCoefficient η n x = vl x + e x
    change evenFourierCoefficient (fun p => η p - a p.1) n x =
      evenFourierCoefficient η n x - e x at hcx
    linarith only [hx, hcx]
  have hR : evenFourierCoefficient η n =ᵐ[volume.restrict (Ioo r s)]
      (fun x => vr x + e x) := by
    filter_upwards [hright, ae_restrict_of_ae_restrict_of_subset hsubR hcoef] with x hx hcx
    change evenFourierCoefficient η n x = vr x + e x
    change evenFourierCoefficient (fun p => η p - a p.1) n x =
      evenFourierCoefficient η n x - e x at hcx
    linarith only [hx, hcx]
  have hmatch := htrace n l r s hlr hrs hcore
    (fun x => vl x + e x) (fun x => vr x + e x) (hvl.add he) (hvr.add he) hL hR
  have hdl : deriv (fun x => vl x + e x) r = deriv vl r + deriv e r := by
    exact deriv_fun_add (hvl.differentiable (by norm_num) r)
      (he.differentiable (by norm_num) r)
  have hdr : deriv (fun x => vr x + e x) r = deriv vr r + deriv e r := by
    exact deriv_fun_add (hvr.differentiable (by norm_num) r)
      (he.differentiable (by norm_num) r)
  have hd : deriv vl r = deriv vr r := by
    have heq := hmatch.2.1
    rw [hdl, hdr] at heq
    exact add_right_cancel heq
  exact ⟨add_right_cancel hmatch.1, hd, congrArg (D.w r * ·) hd⟩

end ContinuousFlexibility.Analysis

namespace ContinuousFlexibility.Statements

open Set Filter MeasureTheory ContinuousFlexibility.Radial
open ContinuousFlexibility.Analysis
open scoped ContDiff Topology

set_option backward.isDefEq.respectTransparency false

/-- The actual N05 canonical remainder has the same modal interface
compatibility. All three scalar coordinates and the original source are
retained, and the cutoff is exactly the one in the physical space model. -/
theorem n06N05_exists_remainder_modal_traces
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {R : ReturnEquationData S}
    {L : ReturnCorrectionData S} {K : CanonicalData S} {V : VolumeModelData S K}
    {base loss b : ℕ} {ε : ℝ} {B : CanonicalDomainData S K V b}
    (hS : IsPhysicalSpaces D T S)
    (h : NonlinearPropertiesThrough05 D T S C R L K V b B base loss ε)
    (u : B.Space) :
    ∃ η f : PolarPoint → ℝ,
      HasCanonicalRepresentation D S C K (C.referenceState, 0) u.val.1
        (V.forget (3 / 4 : ℝ) 0 b u.val.2) η f ∧
      ReferenceGraph D B.weakExponent B.sourceMaterial B.outputMaterial
        (η, u.val.1.2.2.1)
        ((fun p => f p - u.val.1.2.2.2 * (S.height (3 / 4 : ℝ)).decode S.psi p), 0) ∧
      N06PhysicalModalInterfaceTraces D
        (n06ReferenceRemainder S.chiLeft η u.val.1.2.1) := by
  obtain ⟨η, f, hrep, hgraph, htrace⟩ := n06N05_exists_physical_modal_traces h u
  have h01 : N01Properties D T S C base loss ε := h.1.1.1.1
  have hη : MemLp η 2 (radialPhysicalMeasure D) :=
    r11b_output_memLp h01.1.1 h01.1.2.2.2.1 h.2.2.2.1 hgraph.1
  have ha : ContDiff ℝ 1 (fun r => u.val.1.2.1 * S.chiLeft r) :=
    contDiff_const.mul (hS.2.2.1.1.of_le (by simp))
  exact ⟨η, f, hrep, hgraph,
    n06_physicalModalInterfaceTraces_sub_radial hη htrace _ ha⟩

end ContinuousFlexibility.Statements
