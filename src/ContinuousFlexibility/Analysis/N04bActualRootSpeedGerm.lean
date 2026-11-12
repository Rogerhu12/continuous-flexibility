import ContinuousFlexibility.Analysis.N01FlowAngularVariation
import ContinuousFlexibility.Scalar.S05CalculusProof
import Mathlib.Analysis.Calculus.Deriv.Slope

/-!
# Actual corrected characteristic speeds at a component endpoint

The inward second-jet sign follows from the reference component's strict
interior negativity and its simple endpoint zero. N01 identifies the actual
profile germ with that reference germ; N03 identifies the corrected
coefficient germs with the original coefficients there.

Smooth division of the reference radial zero, together with the actual
separated angular factor, gives smooth drift and a positive smooth root
factor on a genuine two-sided rectangle. Both actual characteristic speeds
agree there with drift plus or minus `sqrt x` times that factor, including
`x = 0`. No flow regularity, chart, or normal-form conclusion is a premise.
The physical radius is `r₀ + σ x`; to use x as the ODE time one multiplies
the displayed physical speeds by the same inward sign σ.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open Set Filter
open scoped Topology ContDiff

set_option backward.isDefEq.respectTransparency false

/-- `false` selects the left root and `true` the right root. -/
def n04bEndpointRadius {S : PhysicalSpacesData} (C : NonlinearGeometryData S)
    (m : ℕ) (side : Bool) : ℝ :=
  if side then C.right m else C.left m

def n04bInwardRootSign (side : Bool) : ℝ := if side then -1 else 1

/-- One inward radial coordinate is used at both physical roots. -/
def n04bRootPhysicalShift {S : PhysicalSpacesData} (C : NonlinearGeometryData S)
    (m : ℕ) (side : Bool) (p : PolarPoint) : PolarPoint :=
  (n04bEndpointRadius C m side + n04bInwardRootSign side * p.1, p.2)

theorem n04bInwardRootSign_ne_zero (side : Bool) : n04bInwardRootSign side ≠ 0 := by
  cases side <;> norm_num [n04bInwardRootSign]

theorem n04b_contDiff_rootPhysicalShift {S : PhysicalSpacesData}
    (C : NonlinearGeometryData S) (m : ℕ) (side : Bool) :
    ContDiff ℝ ∞ (n04bRootPhysicalShift C m side) :=
  (contDiff_const.add (contDiff_const.mul contDiff_fst)).prodMk contDiff_snd

@[simp] theorem n04bRootPhysicalShift_zero {S : PhysicalSpacesData}
    (C : NonlinearGeometryData S) (m : ℕ) (side : Bool) (θ : ℝ) :
    n04bRootPhysicalShift C m side (0, θ) = (n04bEndpointRadius C m side, θ) := by
  simp only [n04bRootPhysicalShift, mul_zero, add_zero]

/-- A nonzero derivative of a function negative immediately to the right
of its zero must be negative. Only an actual scalar derivative is used. -/
private theorem n04b_deriv_neg_of_negative_right
    {f : ℝ → ℝ} {v δ : ℝ} (hδ : 0 < δ) (hf : HasDerivAt f v 0)
    (hf0 : f 0 = 0) (hv : v ≠ 0)
    (hneg : ∀ t ∈ Ioo (0 : ℝ) δ, f t < 0) : v < 0 := by
  have hle : v ≤ 0 := le_of_tendsto hf.tendsto_slope_zero_right (by
    filter_upwards [self_mem_nhdsWithin,
      nhdsWithin_le_nhds (Iio_mem_nhds hδ)] with t ht htδ
    have ht0 : 0 < t := ht
    simpa only [zero_add, hf0, sub_zero, smul_eq_mul] using
      mul_nonpos_of_nonneg_of_nonpos (inv_nonneg.mpr ht0.le)
        (hneg t ⟨ht0, htδ⟩).le)
  exact lt_of_le_of_ne hle hv

/-- In particular the inward second-jet sign is derived from N01, not
included as an extra root-factor hypothesis. -/
theorem n04b_endpoint_reference_geometry
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {base loss : ℕ} {ε : ℝ}
    (hN : N01Properties D T S C base loss ε) (m : ℕ) (side : Bool) :
    n04bEndpointRadius C m side ∈ Ioo D.a D.b ∧
      deriv D.w (n04bEndpointRadius C m side) = 0 ∧
      deriv (deriv D.w) (n04bEndpointRadius C m side) ≠ 0 ∧
      n04bInwardRootSign side *
        deriv (deriv D.w) (n04bEndpointRadius C m side) < 0 := by
  have hC : controlGeometryConditions D S C := hN.2.2.2.1
  obtain ⟨_, hbounds⟩ := hN.1.1
  let r₀ := n04bEndpointRadius C m side
  let σ := n04bInwardRootSign side
  have hr₀ : r₀ ∈ Ioo D.a D.b := by
    cases side with
    | false => exact ⟨(hC.1 m).1, (hC.1 m).2.1.trans (hC.1 m).2.2⟩
    | true => exact ⟨(hC.1 m).1.trans (hC.1 m).2.1, (hC.1 m).2.2⟩
  have hroot : deriv D.w r₀ = 0 ∧ deriv (deriv D.w) r₀ ≠ 0 := by
    cases side with
    | false => exact ⟨(hC.2.1 m).1, (hC.2.1 m).2.2.1⟩
    | true => exact ⟨(hC.2.1 m).2.1, (hC.2.1 m).2.2.2⟩
  have hinside (t : ℝ) (ht : t ∈ Ioo (0 : ℝ) (C.right m - C.left m)) :
      r₀ + σ * t ∈ Ioo (C.left m) (C.right m) := by
    cases side <;> dsimp [r₀, σ, n04bEndpointRadius, n04bInwardRootSign] <;>
      constructor <;> linarith [ht.1, ht.2]
  have hwd : ContDiff ℝ ∞ (deriv D.w) :=
    (contDiff_infty_iff_deriv.mp hbounds.1.2.2.1.1).2
  have houter : HasDerivAt (deriv D.w) (deriv (deriv D.w) r₀) (r₀ + σ * 0) := by
    simpa only [mul_zero, add_zero] using (hwd.differentiable (by simp) r₀).hasDerivAt
  have hd : HasDerivAt (fun t : ℝ => deriv D.w (r₀ + σ * t))
      (deriv (deriv D.w) r₀ * σ) 0 := by
    simpa only [Function.comp_def, id_eq, mul_one] using
      houter.comp 0 (((hasDerivAt_id 0).const_mul σ).const_add r₀)
  have hsign := n04b_deriv_neg_of_negative_right
    (sub_pos.mpr (hC.1 m).2.1) hd
    (by simpa only [mul_zero, add_zero] using hroot.1)
    (mul_ne_zero hroot.2 (n04bInwardRootSign_ne_zero side))
    (fun t ht => hC.2.2.2.1 m _ (hinside t ht))
  refine ⟨hr₀, hroot.1, hroot.2, ?_⟩
  change σ * deriv (deriv D.w) r₀ < 0
  simpa only [mul_comm] using hsign

theorem n04b_stateProfile_endpoint_germ
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {base loss : ℕ} {ε : ℝ}
    (hN : N01Properties D T S C base loss ε)
    {z : AnnularState S × ℝ} (hz : z ∈ stateNeighborhood S C base ε)
    (m : ℕ) (side : Bool) :
    stateProfile D S C z.1 =ᶠ[𝓝 (n04bEndpointRadius C m side)] D.w := by
  have hg := n04b_endpoint_reference_geometry hN m side
  rcases hN with ⟨_, _, _, _, _, _, _, _, _, _, hroot, _, _⟩
  exact hroot z hz _ hg.1 hg.2.1

/-- Both actual profile root jets are fixed by the genuine N01 germ. -/
theorem n04b_stateProfile_endpoint_jets
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {base loss : ℕ} {ε : ℝ}
    (hN : N01Properties D T S C base loss ε)
    {z : AnnularState S × ℝ} (hz : z ∈ stateNeighborhood S C base ε)
    (m : ℕ) (side : Bool) :
    deriv (stateProfile D S C z.1) (n04bEndpointRadius C m side) = 0 ∧
      n04bInwardRootSign side *
        deriv (deriv (stateProfile D S C z.1)) (n04bEndpointRadius C m side) < 0 := by
  have he := n04b_stateProfile_endpoint_germ hN hz m side
  have hg := n04b_endpoint_reference_geometry hN m side
  rw [he.deriv_eq, he.deriv.deriv_eq]
  exact ⟨hg.2.1, hg.2.2.2⟩

/-- The actual corrected speeds have the square-root form on a two-sided
open rectangle. Hence the equality includes the root and may be
differentiated in angle there without differentiating `sqrt` in radius. -/
theorem n04b_actualRootSpeed_germ
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {R : ReturnEquationData S}
    {L : ReturnCorrectionData S} {base loss : ℕ} {ε : ℝ}
    (hN : NonlinearPropertiesThrough03 D T S C R L base loss ε)
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    {z : AnnularState S × ℝ} (hz : z ∈ stateNeighborhood S C base ε)
    (hsector : stateSector S z.1) (m : ℕ) (side : Bool) (θ : ℝ) :
    ∃ (δ : ℝ) (d c₀ : PolarPoint → ℝ), 0 < δ ∧
      ContDiffOn ℝ ∞ d (Ioo (-δ) δ ×ˢ Ioo (θ - δ) (θ + δ)) ∧
      ContDiffOn ℝ ∞ c₀ (Ioo (-δ) δ ×ˢ Ioo (θ - δ) (θ + δ)) ∧
      ∀ p ∈ Ioo (-δ) δ ×ˢ Ioo (θ - δ) (θ + δ),
        0 < c₀ p ∧
        minusCharacteristicSpeed (L.coefficients z) (n04bRootPhysicalShift C m side p) =
          d p - Real.sqrt p.1 * c₀ p ∧
        plusCharacteristicSpeed (L.coefficients z) (n04bRootPhysicalShift C m side p) =
          d p + Real.sqrt p.1 * c₀ p := by
  have hN01 : N01Properties D T S C base loss ε := hN.1.1
  obtain ⟨_, hbounds⟩ := hN01.1.1
  have hgeom : RadialProfileGeometry D := hbounds.1
  let r₀ := n04bEndpointRadius C m side
  let σ := n04bInwardRootSign side
  let shift := n04bRootPhysicalShift C m side
  have hroot := n04b_endpoint_reference_geometry hN01 m side
  have hshift : ContDiff ℝ ∞ shift := n04b_contDiff_rootPhysicalShift C m side
  have hshift0 : shift (0, θ) = (r₀, θ) := n04bRootPhysicalShift_zero C m side θ
  have hwd : ContDiff ℝ ∞ (deriv D.w) :=
    (contDiff_infty_iff_deriv.mp hgeom.2.2.1.1).2
  let f : ℝ → ℝ := fun x => -deriv D.w (r₀ + σ * x)
  have hf : ContDiff ℝ ∞ f :=
    (hwd.comp (contDiff_const.add (contDiff_const.mul contDiff_id))).neg
  have hroot0 : deriv D.w r₀ = 0 := hroot.2.1
  have hf0 : f 0 = 0 := by
    simp only [f, mul_zero, add_zero, hroot0, neg_zero]
  obtain ⟨g, hg, hgzero, hdivide⟩ := exists_smooth_division_at_zero hf hf0
  have houter : HasDerivAt (deriv D.w) (deriv (deriv D.w) r₀) (r₀ + σ * 0) := by
    simpa only [mul_zero, add_zero] using (hwd.differentiable (by simp) r₀).hasDerivAt
  have hfd : HasDerivAt f (-(deriv (deriv D.w) r₀ * σ)) 0 := by
    simpa only [f, Function.comp_def, id_eq, mul_one] using
      (houter.comp 0 (((hasDerivAt_id 0).const_mul σ).const_add r₀)).fun_neg
  have hg0 : 0 < g 0 := by
    rw [hgzero, hfd.deriv]
    have hs : σ * deriv (deriv D.w) r₀ < 0 := hroot.2.2.2
    nlinarith only [hs]
  let A : PolarPoint → ℝ := fun p => D.w (shift p).1 * g p.1 / (shift p).1
  let d : PolarPoint → ℝ := fun p => stateCharacteristicDrift D S C z (shift p)
  let c₀ : PolarPoint → ℝ := fun p =>
    Real.sqrt (A p) * characteristicAngularFactor D S C z (shift p)
  have hp₀ : (r₀, θ) ∈ annularOpen D := ⟨hroot.1, mem_univ _⟩
  have hlim : Tendsto shift (𝓝 (0, θ)) (𝓝 (r₀, θ)) := by
    simpa only [hshift0] using (hshift.continuous.continuousAt (x := (0, θ))).tendsto
  have hradlim : Tendsto (fun p : PolarPoint => (shift p).1)
      (𝓝 (0, θ)) (𝓝 r₀) := continuousAt_fst.tendsto.comp hlim
  have hprofile := n04b_stateProfile_endpoint_germ hN01 hz m side
  have hmatch := hN.2.2.2.1 z hz hsector (r₀, θ) hp₀ hroot.2.1
  have hevent : ∀ᶠ p in 𝓝 (0, θ),
      shift p ∈ annularOpen D ∧ 0 < g p.1 ∧
      stateProfile D S C z.1 (shift p).1 = D.w (shift p).1 ∧
      deriv (stateProfile D S C z.1) (shift p).1 = deriv D.w (shift p).1 ∧
      (L.coefficients z).b (shift p) = (originalCoefficients D S C z).b (shift p) ∧
      (L.coefficients z).c (shift p) = (originalCoefficients D S C z).c (shift p) := by
    have hAnn : ∀ᶠ p in 𝓝 (0, θ), shift p ∈ annularOpen D :=
      hlim.eventually ((isOpen_Ioo.prod isOpen_univ).mem_nhds hp₀)
    have hgp : ∀ᶠ p : PolarPoint in 𝓝 (0, θ), 0 < g p.1 :=
      (hg.continuous.continuousAt.comp continuousAt_fst).eventually (Ioi_mem_nhds hg0)
    filter_upwards [hAnn, hgp, hprofile.comp_tendsto hradlim,
      hprofile.deriv.comp_tendsto hradlim, hmatch.1.comp_tendsto hlim,
      hmatch.2.comp_tendsto hlim] with p hp hgpos hw hdw hb hc
    exact ⟨hp, hgpos, hw, hdw, hb, hc⟩
  obtain ⟨η, hη, hball⟩ := Metric.mem_nhds_iff.mp hevent
  let δ := η / 2
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hinfo (p : PolarPoint) (hp : p ∈ Ioo (-δ) δ ×ˢ Ioo (θ - δ) (θ + δ)) :
      shift p ∈ annularOpen D ∧ 0 < g p.1 ∧
      stateProfile D S C z.1 (shift p).1 = D.w (shift p).1 ∧
      deriv (stateProfile D S C z.1) (shift p).1 = deriv D.w (shift p).1 ∧
      (L.coefficients z).b (shift p) = (originalCoefficients D S C z).b (shift p) ∧
      (L.coefficients z).c (shift p) = (originalCoefficients D S C z).c (shift p) := by
    apply hball
    rw [Metric.mem_ball, Prod.dist_eq, Real.dist_eq, Real.dist_eq, sub_zero, max_lt_iff]
    constructor <;> rw [abs_lt] <;> constructor <;> dsimp [δ] at hp <;>
      linarith [hp.1.1, hp.1.2, hp.2.1, hp.2.2]
  have hApos (p : PolarPoint) (hp : p ∈ Ioo (-δ) δ ×ˢ Ioo (θ - δ) (θ + δ)) :
      0 < A p := by
    have hi := hinfo p hp
    exact div_pos (mul_pos (hgeom.2.2.2.2.1 _ hi.1.1) hi.2.1)
      (hgeom.1.trans hi.1.1.1)
  have hreg (p : PolarPoint) (hp : p ∈ Ioo (-δ) δ ×ˢ Ioo (θ - δ) (θ + δ)) :
      ContDiffAt ℝ ∞ d p ∧ ContDiffAt ℝ ∞ c₀ p ∧ 0 < c₀ p := by
    have hi := hinfo p hp
    have hA : ContDiffAt ℝ ∞ A p :=
      (((hgeom.2.2.1.1.comp hshift.fst).contDiffAt).mul
        (hg.comp contDiff_fst).contDiffAt).div hshift.fst.contDiffAt
          (hgeom.1.trans hi.1.1.1).ne'
    have hfac := N01Properties.characteristic_factors_contDiffAt hN01 hS hT hz hsector hi.1
    obtain ⟨ha, hD, _⟩ :=
      N01Properties.characteristic_coefficient_regular hN01 hS hT hz hsector hi.1
    have hb : 0 < characteristicAngularFactor D S C z (shift p) :=
      one_div_pos.mpr (mul_pos hD ha)
    exact ⟨hfac.1.comp p hshift.contDiffAt,
      (hA.sqrt (hApos p hp).ne').mul (hfac.2.comp p hshift.contDiffAt),
      mul_pos (Real.sqrt_pos.mpr (hApos p hp)) hb⟩
  refine ⟨δ, d, c₀, hδ, ?_, ?_, ?_⟩
  · intro p hp
    exact (hreg p hp).1.contDiffWithinAt
  · intro p hp
    exact (hreg p hp).2.1.contDiffWithinAt
  · intro p hp
    obtain ⟨hpD, _, hw, hdw, hb, hc⟩ := hinfo p hp
    have ha := hN.2.1 z hz hsector (shift p)
    have hrad : characteristicRadialRoot D S C z (shift p).1 =
        Real.sqrt p.1 * Real.sqrt (A p) := by
      unfold characteristicRadialRoot
      rw [hw, hdw]
      have hdivide' : -deriv D.w (shift p).1 = p.1 * g p.1 := hdivide p.1
      have he : -(D.w (shift p).1 * deriv D.w (shift p).1 / (shift p).1) =
          p.1 * A p := by
        calc
          _ = D.w (shift p).1 * (-deriv D.w (shift p).1) / (shift p).1 := by ring
          _ = _ := by rw [hdivide']; dsimp only [A]; ring
      rw [he, Real.sqrt_mul' _ (hApos p hp).le]
    have hsame : minusCharacteristicSpeed (L.coefficients z) (shift p) =
        minusCharacteristicSpeed (originalCoefficients D S C z) (shift p) := by
      simp only [minusCharacteristicSpeed, ha, hb, hc]
    have hminus : minusCharacteristicSpeed (L.coefficients z) (shift p) =
        d p - Real.sqrt p.1 * c₀ p := by
      rw [hsame, N01Properties.minusCharacteristicSpeed_eq_separated hN01 hS hT hz hsector hpD,
        hrad]
      dsimp only [d, c₀]
      ring
    have hdrift : (L.coefficients z).b (shift p) / (L.coefficients z).a (shift p) = d p := by
      dsimp only [d, stateCharacteristicDrift]
      rw [ha, hb]
    refine ⟨(hreg p hp).2.2, hminus, ?_⟩
    have hsum : plusCharacteristicSpeed (L.coefficients z) (shift p) =
        2 * ((L.coefficients z).b (shift p) / (L.coefficients z).a (shift p)) -
          minusCharacteristicSpeed (L.coefficients z) (shift p) := by
      unfold plusCharacteristicSpeed minusCharacteristicSpeed
      ring
    rw [hsum, hdrift, hminus]
    ring

end ContinuousFlexibility.Statements
