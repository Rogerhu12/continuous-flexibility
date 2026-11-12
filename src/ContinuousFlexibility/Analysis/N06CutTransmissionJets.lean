import ContinuousFlexibility.Analysis.N06N05CurrentRootTransmission
import ContinuousFlexibility.Analysis.N06CurrentClosedTestJets

/-!
# Actual first jets at a negative middle cut

The two radial chart directions are opposite. Their height normal jets
differ by the affine correction dictated by the actual forward charts.
The scalar parameter is `1 / (2 * R)` for the canonical cut of radius R.

The original N05 graph supplies a single physical C1 representative for
each mode. The genuine closed reference inverse identifies its canonical
endpoint jets. The original N04 smooth-test law, extended by a physical
affine probe, then gives the canonical relation without any cut first-jet
record. A separate geometric specialization retains the general genuine
first-jet reconstruction algebra.
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

/-- A scalar physical representative agrees with its canonical modal
representative throughout the open interval. Only the genuine reference
chart identities and its actual radial form are used. -/
private theorem n06_reference_scalarHeight_mode_eqOn
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {L : ReturnCorrectionData S} {K : CanonicalData S}
    {base loss : ℕ} {ε : ℝ}
    (h01 : N01Properties D T S C base loss ε)
    (h04 : N04Properties D T S C L K base loss ε)
    (hcoordinates : N05ControlledReferenceCoordinates D S C K)
    (m : ℕ) (w v : ℝ → ℝ)
    (he : EqOn w (fun r => K.height (C.referenceState, 0) m (r, 0) *
      v ((K.chart (C.referenceState, 0) m (r, 0)).1))
        (Ioo (K.physicalLeft m) (K.physicalRight m))) :
    EqOn (fun y => canonicalHeight S K (C.referenceState, 0) m (fun p => w p.1) (y, 0))
      v (Ioo (K.left m) (K.right m)) := by
  have href := n05_referenceState_mem (S := S) (C := C) (base := base) h01.2.1
  have hs := n05_referenceState_sector h01.2.2.1
  have hc := h04.1.charts (C.referenceState, 0) href hs m
  intro y hy
  let x : PolarPoint := K.inverseChart (C.referenceState, 0) m (y, 0)
  have hp : (y, (0 : ℝ)) ∈ canonicalOpen S K m := ⟨hy, mem_univ _⟩
  have hxActual : x ∈ physicalPieceOpen S K (C.referenceState, 0) m := hc.2.1 hp
  have hx : x ∈ referencePhysicalPieceOpen S K m := by
    simpa only [h04.1.referenceDomain m] using hxActual
  have hshape := hcoordinates.1 m x hx
  have hright : K.chart (C.referenceState, 0) m x = (y, 0) := hc.2.2.2.1 _ hp
  have hyx : (K.chart (C.referenceState, 0) m (x.1, 0)).1 = y := by
    rw [hshape.1] at hright
    exact congrArg Prod.fst hright
  have hH : K.height (C.referenceState, 0) m x ≠ 0 :=
    (hc.2.2.2.2.2.2.2 x hxActual).1.ne'
  change w x.1 / K.height (C.referenceState, 0) m x = v y
  apply (div_eq_iff hH).mpr
  have hmodeValue : w x.1 = K.height (C.referenceState, 0) m (x.1, 0) *
      v ((K.chart (C.referenceState, 0) m (x.1, 0)).1) := he hx.1
  rw [hmodeValue, hshape.2, hyx]
  ring

/-- The genuine closed inverse and one-sided derivative uniqueness
identify the canonical upper endpoint jets of an actual C1 scalar mode. -/
private theorem n06_reference_scalarHeight_upper_jets
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {L : ReturnCorrectionData S} {K : CanonicalData S}
    {base loss : ℕ} {ε : ℝ}
    (h01 : N01Properties D T S C base loss ε)
    (h04 : N04Properties D T S C L K base loss ε)
    (hcoordinates : N05ControlledReferenceCoordinates D S C K)
    (m : ℕ) {w v : ℝ → ℝ}
    (hw : ContDiffOn ℝ 1 w (radialCore D)) (hv : ContDiff ℝ 1 v)
    (he : EqOn w (fun r => K.height (C.referenceState, 0) m (r, 0) *
      v ((K.chart (C.referenceState, 0) m (r, 0)).1))
        (Ioo (K.physicalLeft m) (K.physicalRight m)))
    (hx : (K.inverseChart (C.referenceState, 0) m (K.right m, 0)).1 ∈ radialCore D) :
    canonicalHeight S K (C.referenceState, 0) m (fun p => w p.1) (K.right m, 0) =
        v (K.right m) ∧
      radialPartial (canonicalHeight S K (C.referenceState, 0) m (fun p => w p.1))
        (K.right m, 0) = deriv v (K.right m) := by
  have href := n05_referenceState_mem (S := S) (C := C) (base := base) h01.2.1
  have hs := n05_referenceState_sector h01.2.2.1
  have hp : (K.right m, (0 : ℝ)) ∈ canonicalClosed S K m :=
    ⟨⟨(h04.1.referenceBounds m).2.1.le, le_rfl⟩, mem_univ _⟩
  have hG := (n04b_inverseChart_contDiffAt_closed h04.1 href hs m hp).differentiableAt
    (by simp)
  have hb := h04.1.boundary (C.referenceState, 0) href hs m
  have hH := hb.2.2.2.2.1 _ (hb.2.1 hp)
  have hwx : DifferentiableAt ℝ (fun p : PolarPoint => w p.1)
      (K.inverseChart (C.referenceState, 0) m (K.right m, 0)) :=
    ((hw.contDiffAt (isOpen_Ioo.mem_nhds hx)).differentiableAt
      (by norm_num)).comp _ differentiableAt_fst
  have hd : DifferentiableAt ℝ
      (canonicalHeight S K (C.referenceState, 0) m (fun p => w p.1)) (K.right m, 0) := by
    change DifferentiableAt ℝ (fun p =>
      w (K.inverseChart (C.referenceState, 0) m p).1 /
        K.height (C.referenceState, 0) m (K.inverseChart (C.referenceState, 0) m p)) _
    have hnum : DifferentiableAt ℝ
        (fun p => w (K.inverseChart (C.referenceState, 0) m p).1) (K.right m, 0) :=
      hwx.comp _ hG
    have hden : DifferentiableAt ℝ
        (fun p => K.height (C.referenceState, 0) m
          (K.inverseChart (C.referenceState, 0) m p)) (K.right m, 0) :=
      (hH.2.1.differentiableAt (by simp)).comp _ hG
    simpa only [div_eq_mul_inv] using hnum.fun_mul (hden.fun_inv hH.2.2.2.ne')
  have hslice := hasDerivAt_radial_slice hd
  have htrace := n06_cauchyData_eq_of_eqOn_Ioo_left (h04.1.referenceBounds m).2.1
    hslice.differentiableAt (hv.differentiable (by norm_num) (K.right m))
    (n06_reference_scalarHeight_mode_eqOn h01 h04 hcoordinates m w v he)
  exact ⟨htrace.1, hslice.deriv.symm.trans htrace.2⟩

/-- The same original N05 graph forces each actual canonical mode to
satisfy the affine cut law. Its physical C1 representative is transported
through the genuine closed reference inverse; the law itself comes from
N04 applied to an affine probe with the same physical first jet. No cut
first-jet realization or new matching condition is an input. -/
theorem n06N05_canonicalMode_cut_traces
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {R : ReturnEquationData S}
    {L : ReturnCorrectionData S} {K : CanonicalData S} {V : VolumeModelData S K}
    {base loss b : ℕ} {ε : ℝ} {B : CanonicalDomainData S K V b}
    (hS : IsPhysicalSpaces D T S)
    (h : NonlinearPropertiesThrough05 D T S C R L K V b B base loss ε)
    (hcoordinates : N05ControlledReferenceCoordinates D S C K)
    (u : B.Space) (n k : ℕ) (vl vr : ℝ → ℝ)
    (hvl : ContDiff ℝ 1 vl) (hvr : ContDiff ℝ 1 vr)
    (hmodeL : n06HalfCosineCoefficient (u.val.1.1 (K.cutPair n).1) k
      =ᵐ[volume.restrict (Ioo (K.left (K.cutPair n).1) (K.right (K.cutPair n).1))] vl)
    (hmodeR : n06HalfCosineCoefficient (u.val.1.1 (K.cutPair n).2) k
      =ᵐ[volume.restrict (Ioo (K.left (K.cutPair n).2) (K.right (K.cutPair n).2))] vr) :
    vl (K.cutRadius n) = vr (K.cutRadius n) ∧
      deriv vl (K.cutRadius n) + deriv vr (K.cutRadius n) =
        -(2 * K.cutRadius n)⁻¹ * vl (K.cutRadius n) := by
  obtain ⟨η, f, hrep, hgraph, _⟩ := n06N05_exists_physical_modal_traces h u
  have h01 : N01Properties D T S C base loss ε := h.1.1.1.1
  have h04 : N04Properties D T S C L K base loss ε := h.1.2.2.2.2
  have href := n05_referenceState_mem (S := S) (C := C) (base := base) h01.2.1
  have hs := n05_referenceState_sector h01.2.2.1
  have hcut := h04.2.1.1.2 (C.referenceState, 0) href hs n
  have hxcut := hcut.2.1 ⟨(0 : ℝ), rfl⟩
  have hC := h01.2.2.2.1
  have hxD : (canonicalCutPoint S K (C.referenceState, 0) n 0).1 ∈ radialCore D :=
    ⟨(hC.1 n).1.trans hxcut.1.1, hxcut.1.2.trans (hC.1 n).2.2⟩
  obtain ⟨w, hwAE, hw⟩ := n06_remainder_mode_C1_representative
    h01.1.1 h01.1.2.2.2.1 h.2.2.2.1 hgraph
    (hS.2.2.1.1.of_le (by simp)) u.val.1.2.1 k hxD
  let rem : PolarPoint → ℝ := n06ReferenceRemainder S.chiLeft η u.val.1.2.1
  have hη : MemLp η 2 (radialPhysicalMeasure D) :=
    r11b_output_memLp h01.1.1 h01.1.2.2.2.1 h.2.2.2.1 hgraph.1
  have hχ : MemLp (fun p : PolarPoint => u.val.1.2.1 * S.chiLeft p.1) 2
      (radialPhysicalMeasure D) :=
    r11b_continuous_memLp (continuous_const.mul (hS.2.2.1.1.continuous.comp continuous_fst))
  have hrem : MemLp rem 2 (radialPhysicalMeasure D) := hη.sub hχ
  obtain ⟨a, ha⟩ := hgraph.1
  have hp : Function.Periodic rem (0, Real.pi) :=
    n06_referenceRemainder_periodic ha.2.2.1 _
  have he (m : ℕ) (v : ℝ → ℝ) (hv : ContDiff ℝ 1 v)
      (hmode : n06HalfCosineCoefficient (u.val.1.1 m) k
        =ᵐ[volume.restrict (Ioo (K.left m) (K.right m))] v) :
      EqOn w (fun r => K.height (C.referenceState, 0) m (r, 0) *
        v ((K.chart (C.referenceState, 0) m (r, 0)).1))
          (Ioo (K.physicalLeft m) (K.physicalRight m)) := by
    have hmodal := n06_controlledReference_modal_representation h.1 hcoordinates
      hrem hp m k (hrep.1 m) hmode
    have hsub := (h04.1.referenceBounds m).2.2
    have hwAE' : evenFourierCoefficient rem k
        =ᵐ[volume.restrict (Ioo (K.physicalLeft m) (K.physicalRight m))] w :=
      ae_restrict_of_ae_restrict_of_subset hsub hwAE
    have hAE : w =ᵐ[volume.restrict (Ioo (K.physicalLeft m) (K.physicalRight m))]
        (fun r => K.height (C.referenceState, 0) m (r, 0) *
          v ((K.chart (C.referenceState, 0) m (r, 0)).1)) :=
      hwAE'.symm.trans hmodal
    have hc : ContinuousOn (fun r => K.height (C.referenceState, 0) m (r, 0) *
        v ((K.chart (C.referenceState, 0) m (r, 0)).1))
          (Ioo (K.physicalLeft m) (K.physicalRight m)) := by
      intro r hr
      have hb := n05_reference_boundary_regular h04.1 href hs m (p := (r, 0))
        ⟨hr.1.le, hr.2.le⟩
      exact (n06_radial_mode_pullback_contDiffAt hb.1 hb.2.1 hv).continuousAt.continuousWithinAt
    exact Measure.eqOn_open_of_ae_eq hAE isOpen_Ioo (hw.continuousOn.mono hsub) hc
  obtain ⟨_, _, _, _, _, _, _, _, hRl, hRr⟩ := h04.2.1.1.1 n
  have hxL : (K.inverseChart (C.referenceState, 0) (K.cutPair n).1
      (K.right (K.cutPair n).1, 0)).1 ∈ radialCore D := by
    rw [hRl]
    exact hxD
  have hxR : (K.inverseChart (C.referenceState, 0) (K.cutPair n).2
      (K.right (K.cutPair n).2, 0)).1 ∈ radialCore D := by
    rw [hRr, hcut.1 0]
    exact hxD
  have hleft := n06_reference_scalarHeight_upper_jets h01 h04 hcoordinates
    (K.cutPair n).1 hw hvl (he _ _ hvl hmodeL) hxL
  have hright := n06_reference_scalarHeight_upper_jets h01 h04 hcoordinates
    (K.cutPair n).2 hw hvr (he _ _ hvr hmodeR) hxR
  rw [hRl] at hleft
  rw [hRr] at hright
  have htrans := n06_reference_cut_scalar_of_contDiffOn_one h01 h04 hw n 0
  rw [hleft.1, hright.1, hleft.2, hright.2] at htrans
  refine ⟨htrans.1.symm, ?_⟩
  rw [htrans.2]
  simp only [div_eq_mul_inv]
  ring

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

/-- When a concrete pair of forward first jets realizes an affine cut,
the actual N05 finite modes have matching reconstructed value and flux.
The canonical cut law is proved above from N04 and the original graph;
no reference cut-jet record is needed. This geometric specialization does
not assert that a moving physical cut is a fixed radial circle. -/
theorem n06N05_finite_current_cut_conormal
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {R : ReturnEquationData S}
    {L : ReturnCorrectionData S} {K : CanonicalData S} {V : VolumeModelData S K}
    {base loss b : ℕ} {ε : ℝ} {B : CanonicalDomainData S K V b}
    (hS : IsPhysicalSpaces D T S)
    (h : NonlinearPropertiesThrough05 D T S C R L K V b B base loss ε)
    (hcoordinates : N05ControlledReferenceCoordinates D S C K)
    (u : B.Space) (n : ℕ) (s : Finset ℕ) (vl vr : ℕ → ℝ → ℝ)
    {r σ : ℝ} {β H ρ κ Hr : ℝ → ℝ}
    {Fl Fr : PolarPoint → PolarPoint} {hl hr : PolarPoint → ℝ}
    (Jl : N06RootFirstJets Fl hl r (K.cutRadius n) σ β H ρ κ Hr)
    (Jr : N06RootFirstJets Fr hr r (K.cutRadius n) (-σ) β H ρ κ
      (fun θ => Hr θ - H θ * (σ * ρ θ) * (2 * K.cutRadius n)⁻¹))
    (hvl : ∀ k ∈ s, ContDiff ℝ 1 (vl k))
    (hvr : ∀ k ∈ s, ContDiff ℝ 1 (vr k))
    (hmodeL : ∀ k ∈ s, n06HalfCosineCoefficient (u.val.1.1 (K.cutPair n).1) k
      =ᵐ[volume.restrict (Ioo (K.left (K.cutPair n).1) (K.right (K.cutPair n).1))] vl k)
    (hmodeR : ∀ k ∈ s, n06HalfCosineCoefficient (u.val.1.1 (K.cutPair n).2) k
      =ᵐ[volume.restrict (Ioo (K.left (K.cutPair n).2) (K.right (K.cutPair n).2))] vr k)
    (A M : PolarPoint → ℝ) (θ : ℝ) :
    hl (r, θ) * r11bFiniteSynthesis s vl referenceAngularBasis (Fl (r, θ)) =
      hr (r, θ) * r11bFiniteSynthesis s vr referenceAngularBasis (Fr (r, θ)) ∧
    symmetricNormalFlux A M (fun p => hl p * r11bFiniteSynthesis s vl referenceAngularBasis (Fl p))
        (r, θ) =
      symmetricNormalFlux A M
        (fun p => hr p * r11bFiniteSynthesis s vr referenceAngularBasis (Fr p)) (r, θ) := by
  have he : ∀ k ∈ s, ContDiff ℝ 1 (referenceAngularBasis k) :=
    fun k _ => (contDiff_referenceAngularBasis k).of_le (by simp)
  have htrace (k : ℕ) (hk : k ∈ s) :=
    n06N05_canonicalMode_cut_traces hS h hcoordinates u n k (vl k) (vr k)
      (hvl k hk) (hvr k hk) (hmodeL k hk) (hmodeR k hk)
  have hsum (η : ℝ) := n06_finiteSynthesis_cut_traces s vl vr referenceAngularBasis
    hvl hvr he htrace η
  have hdl := (n06_contDiff_one_finiteSynthesis s vl referenceAngularBasis hvl he).differentiable
    (by norm_num)
  have hdr := (n06_contDiff_one_finiteSynthesis s vr referenceAngularBasis hvr he).differentiable
    (by norm_num)
  have hj := n06_cut_reconstruction_firstJets_match Jl Jr
    (fun η => hdl (K.cutRadius n, η)) (fun η => hdr (K.cutRadius n, η))
    (fun η => (hsum η).1) (fun η => (hsum η).2) θ
  exact ⟨hj.1, by simp only [symmetricNormalFlux, hj.2.1, hj.2.2]⟩

end ContinuousFlexibility.Analysis
