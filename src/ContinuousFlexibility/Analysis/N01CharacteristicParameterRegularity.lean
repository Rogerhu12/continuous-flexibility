module

public import ContinuousFlexibility.Analysis.N01FlowAngularVariation
public import ContinuousFlexibility.Analysis.PolarHeightCharacteristicVariation
public import ContinuousFlexibility.Scalar.S04CalculusProof
public import ContinuousFlexibility.Scalar.GreenIdentity
public import ContinuousFlexibility.Analysis.N01RadialFlow
public import Mathlib.Analysis.Normed.Group.Bounded

/-!
# Parameter and angle regularity of the actual characteristic speed

The parameter varies only the physical height. The radial square root
is independent of that parameter, so it remains a continuous multiplier
at turning radii. The drift and angular factor are jointly smooth in
the parameter and physical point. Their genuine parameter derivatives
therefore give continuous, uniformly bounded speed derivatives on every
compact parameter and radial and angular box.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Statements

open Set Filter
open scoped ContDiff Topology

set_option backward.isDefEq.respectTransparency false

local instance n01CharacteristicParameterRegularityRealNormedSpace : NormedSpace ℝ ℝ := NormedField.toNormedSpace

theorem characteristicRadialRoot_q_eq (D : ReferenceData) (S : PhysicalSpacesData)
    (C : NonlinearGeometryData S) (x : AnnularState S) (q r : ℝ) :
    characteristicRadialRoot D S C (x, q) r =
      characteristicRadialRoot D S C (x, 0) r := rfl

/-- The genuine parameter derivative of the separated smooth factors. -/
def characteristicQDerivative (D : ReferenceData) (S : PhysicalSpacesData)
    (C : NonlinearGeometryData S) (x : AnnularState S) (s : ℝ × PolarPoint) : ℝ :=
  fderiv ℝ (fun t : ℝ × PolarPoint => stateCharacteristicDrift D S C (x, t.1) t.2)
    s (1, (0, 0)) -
  characteristicRadialRoot D S C (x, 0) s.2.1 *
    fderiv ℝ (fun t : ℝ × PolarPoint => characteristicAngularFactor D S C (x, t.1) t.2)
      s (1, (0, 0))

/-- A genuine joint derivative is determined by its two actual scalar
slice derivatives. -/
theorem hasFDerivAt_coprod_of_hasDerivAt_slices
    {f : PolarPoint → ℝ} {L : PolarPoint →L[ℝ] ℝ} {q θ a b : ℝ}
    (hf : HasFDerivAt f L (q, θ))
    (hq : HasDerivAt (fun t => f (t, θ)) a q)
    (hθ : HasDerivAt (fun t => f (q, t)) b θ) :
    HasFDerivAt f ((ContinuousLinearMap.toSpanSingleton ℝ a).coprod
      (ContinuousLinearMap.toSpanSingleton ℝ b)) (q, θ) := by
  have hq' : HasDerivAt (fun t => f (t, θ)) (L (1, 0)) q := by
    simpa only [Function.comp_def, id_eq] using
      hf.comp_hasDerivAt q ((hasDerivAt_id q).prodMk (hasDerivAt_const q θ))
  have hθ' : HasDerivAt (fun t => f (q, t)) (L (0, 1)) θ := by
    simpa only [Function.comp_def, id_eq] using
      hf.comp_hasDerivAt θ ((hasDerivAt_const θ q).prodMk (hasDerivAt_id θ))
  have hLq : L (1, 0) = a := hq'.unique hq
  have hLθ : L (0, 1) = b := hθ'.unique hθ
  apply hf.congr_fderiv
  apply ContinuousLinearMap.ext
  intro v
  have hv : v = v.1 • (1, 0) + v.2 • (0, 1) := by
    rcases v with ⟨v₁, v₂⟩
    simp only [Prod.smul_mk, smul_eq_mul, mul_one, mul_zero, Prod.mk_add_mk,
      add_zero, zero_add]
  calc
    L v = L (v.1 • (1, 0) + v.2 • (0, 1)) := congrArg L hv
    _ = v.1 * a + v.2 * b := by
      simp only [map_add, map_smul, hLq, hLθ, smul_eq_mul]
    _ = ((ContinuousLinearMap.toSpanSingleton ℝ a).coprod
        (ContinuousLinearMap.toSpanSingleton ℝ b)) v := by
      simp only [ContinuousLinearMap.coprod_apply,
        ContinuousLinearMap.toSpanSingleton_apply, smul_eq_mul]

theorem minusCharacteristicSpeed_angular_periodic_of_physical
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    (hS : IsPhysicalSpaces D T S) (C : NonlinearGeometryData S)
    (z : AnnularState S × ℝ) (r : ℝ) :
    Function.Periodic (fun θ =>
      minusCharacteristicSpeed (originalCoefficients D S C z) (r, θ)) Real.pi := by
  have hu := ((hS.1 (3 / 4 : ℝ)).2.2.2.1 z.1.1.1).2.2.1
  have hh : Function.Periodic (stateHeight D S C z) (0, Real.pi) := by
    intro p
    simp only [stateHeight, stateU, heightPairField, Prod.fst_add, add_zero]
    rw [hu p]
  obtain ⟨ha, hb, hc⟩ := periodic_heightCorrectedCoefficients (stateProfile D S C z.1) hh
  intro θ
  have ha' := ha (r, θ)
  have hb' := hb (r, θ)
  have hc' := hc (r, θ)
  simp only [Prod.mk_add_mk, add_zero] at ha' hb' hc'
  simp only [minusCharacteristicSpeed, originalCoefficients, ha', hb', hc']

section ActualFactors

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {base loss : ℕ} {ε : ℝ}
  (hN01 : N01Properties D T S C base loss ε)
  (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
  {x : AnnularState S} {q : ℝ}
  (hxq : (x, q) ∈ stateNeighborhood S C base ε)
  (hsector : stateSector S x)

include hN01 hS hT hxq hsector

theorem N01Properties.characteristic_factors_parameter_contDiffAt
    {p : PolarPoint} (hp : p ∈ annularOpen D) :
    ContDiffAt ℝ ∞
      (fun s : ℝ × PolarPoint => stateCharacteristicDrift D S C (x, s.1) s.2) (q, p) ∧
    ContDiffAt ℝ ∞
      (fun s : ℝ × PolarPoint => characteristicAngularFactor D S C (x, s.1) s.2) (q, p) := by
  have hw := contDiff_stateProfile_of_n01 hS hT hN01 x
  have hh := hN01.stateRadialHeight_contDiff hS hT x
  have hu : ContDiff ℝ ∞ (stateU S x) :=
    physical_height_with_cutoff_contDiff hT hS (by norm_num : (0 : ℝ) < 3 / 4)
      x.1.1 x.1.2
  have hW : ContDiff ℝ ∞ (fun s : ℝ × ℝ => stateProfile D S C x s.2) :=
    hw.comp contDiff_snd
  have hZ : ContDiff ℝ ∞
      (fun s : ℝ × PolarPoint => stateHeight D S C (x, s.1) s.2) :=
    (hh.comp contDiff_snd.fst).add (contDiff_fst.mul (hu.comp contDiff_snd))
  obtain ⟨_, hgeom⟩ := hN01.1.1
  have hr : p.1 ≠ 0 := (hgeom.1.1.trans hp.1.1).ne'
  obtain ⟨ha, hd, _, _⟩ :=
    hN01.characteristic_coefficient_regular hS hT hxq hsector hp
  have hE := contDiffAt_parameter_profileEnergy (p := q) (x := p) hW.contDiffAt
  have hk := contDiffAt_parameter_heightRadial (p := q) (x := p) hZ.contDiffAt
  have ht := contDiffAt_parameter_heightAngular (p := q) (x := p) hZ.contDiffAt hr
  have htr := contDiffAt_parameter_radialPartial ht
  have htt := contDiffAt_parameter_angularPartial ht
  have hD := contDiffAt_parameter_polarDiscriminant
    (p := q) (x := p) hW.contDiffAt hZ.contDiffAt hr
  have hscale : ContDiffAt ℝ ∞ (fun s : ℝ × PolarPoint =>
      inverseDThreeHalves
        (polarDiscriminant (stateProfile D S C x) (stateHeight D S C (x, s.1)) s.2))
      (q, p) :=
    contDiffAt_const.div (hD.mul (hD.sqrt hd.ne'))
      (mul_ne_zero hd.ne' (Real.sqrt_pos.mpr hd).ne')
  have hA : ContDiffAt ℝ ∞ (fun s : ℝ × PolarPoint =>
      (originalCoefficients D S C (x, s.1)).a s.2) (q, p) :=
    (hk.add (hE.mul htt)).mul hscale
  have hB : ContDiffAt ℝ ∞ (fun s : ℝ × PolarPoint =>
      (originalCoefficients D S C (x, s.1)).b s.2) (q, p) :=
    (hE.neg.mul htr).mul hscale
  exact ⟨hB.div hA ha.ne', contDiffAt_const.div (hD.mul hA) (mul_ne_zero hd.ne' ha.ne')⟩

theorem N01Properties.minusCharacteristicSpeed_parameter_continuousAt
    {p : PolarPoint} (hp : p ∈ annularOpen D) :
    ContinuousAt (fun s : ℝ × PolarPoint =>
      minusCharacteristicSpeed (originalCoefficients D S C (x, s.1)) s.2) (q, p) := by
  obtain ⟨hA, hB⟩ :=
    hN01.characteristic_factors_parameter_contDiffAt hS hT hxq hsector hp
  have hK : ContinuousAt (fun s : ℝ × PolarPoint =>
      characteristicRadialRoot D S C (x, 0) s.2.1) (q, p) := by
    have hmap : ContinuousAt (fun s : ℝ × PolarPoint => s.2.1) (q, p) :=
      continuousAt_snd.fst
    have hk := hN01.characteristicRadialRoot_continuousAt hS hT
      (z := (x, 0)) (r := p.1) hp.1
    simpa only [Function.comp_def] using hk.comp_of_eq hmap rfl
  have hqnear : ∀ᶠ s : ℝ × PolarPoint in 𝓝 (q, p), |s.1| < ε :=
    continuousAt_fst.abs.eventually_lt continuousAt_const hxq.2
  have hpnear : ∀ᶠ s : ℝ × PolarPoint in 𝓝 (q, p), s.2 ∈ annularOpen D :=
    continuousAt_snd.eventually ((isOpen_Ioo.prod isOpen_univ).mem_nhds hp)
  apply (hA.continuousAt.sub (hK.mul hB.continuousAt)).congr_of_eventuallyEq
  filter_upwards [hqnear, hpnear] with s hs hp'
  simpa only [Pi.sub_apply, Pi.mul_apply, characteristicRadialRoot_q_eq] using
    hN01.minusCharacteristicSpeed_eq_separated hS hT
      (z := (x, s.1)) ⟨hxq.1, hs⟩ hsector hp'

theorem N01Properties.characteristicQDerivative_continuousAt
    {p : PolarPoint} (hp : p ∈ annularOpen D) :
    ContinuousAt (characteristicQDerivative D S C x) (q, p) := by
  obtain ⟨hA, hB⟩ :=
    hN01.characteristic_factors_parameter_contDiffAt hS hT hxq hsector hp
  have hAq : ContinuousAt (fun s : ℝ × PolarPoint =>
      fderiv ℝ (fun t : ℝ × PolarPoint => stateCharacteristicDrift D S C (x, t.1) t.2)
        s (1, (0, 0))) (q, p) :=
    (hA.fderiv_right (m := 0) (by simp)).continuousAt.clm_apply continuousAt_const
  have hBq : ContinuousAt (fun s : ℝ × PolarPoint =>
      fderiv ℝ (fun t : ℝ × PolarPoint => characteristicAngularFactor D S C (x, t.1) t.2)
        s (1, (0, 0))) (q, p) :=
    (hB.fderiv_right (m := 0) (by simp)).continuousAt.clm_apply continuousAt_const
  have hK : ContinuousAt (fun s : ℝ × PolarPoint =>
      characteristicRadialRoot D S C (x, 0) s.2.1) (q, p) := by
    have hmap : ContinuousAt (fun s : ℝ × PolarPoint => s.2.1) (q, p) :=
      continuousAt_snd.fst
    have hk := hN01.characteristicRadialRoot_continuousAt hS hT
      (z := (x, 0)) (r := p.1) hp.1
    simpa only [Function.comp_def] using hk.comp_of_eq hmap rfl
  exact hAq.sub (hK.mul hBq)

theorem N01Properties.characteristicAngularDerivative_parameter_continuousAt
    {p : PolarPoint} (hp : p ∈ annularOpen D) :
    ContinuousAt (fun s : ℝ × PolarPoint =>
      characteristicAngularDerivative D S C (x, s.1) s.2) (q, p) := by
  obtain ⟨hA, hB⟩ :=
    hN01.characteristic_factors_parameter_contDiffAt hS hT hxq hsector hp
  have hAθ := (contDiffAt_parameter_angularPartial hA).continuousAt
  have hBθ := (contDiffAt_parameter_angularPartial hB).continuousAt
  have hK : ContinuousAt (fun s : ℝ × PolarPoint =>
      characteristicRadialRoot D S C (x, 0) s.2.1) (q, p) := by
    have hmap : ContinuousAt (fun s : ℝ × PolarPoint => s.2.1) (q, p) :=
      continuousAt_snd.fst
    have hk := hN01.characteristicRadialRoot_continuousAt hS hT
      (z := (x, 0)) (r := p.1) hp.1
    simpa only [Function.comp_def] using hk.comp_of_eq hmap rfl
  exact hAθ.sub (hK.mul hBθ)

/-- A true parameter derivative, including at radial turning points. -/
theorem N01Properties.minusCharacteristicSpeed_hasDerivAt_q
    {p : PolarPoint} (hp : p ∈ annularOpen D) :
    HasDerivAt (fun t : ℝ =>
      minusCharacteristicSpeed (originalCoefficients D S C (x, t)) p)
      (characteristicQDerivative D S C x (q, p)) q := by
  obtain ⟨hA, hB⟩ :=
    hN01.characteristic_factors_parameter_contDiffAt hS hT hxq hsector hp
  have hmap : HasDerivAt (fun t : ℝ => (t, p)) (1, (0, 0)) q :=
    (hasDerivAt_id q).prodMk (hasDerivAt_const q p)
  have hAq : HasDerivAt (fun t : ℝ => stateCharacteristicDrift D S C (x, t) p)
      (fderiv ℝ (fun s : ℝ × PolarPoint =>
        stateCharacteristicDrift D S C (x, s.1) s.2) (q, p) (1, (0, 0))) q := by
    simpa only [Function.comp_def] using
      (hA.differentiableAt (by simp)).hasFDerivAt.comp_hasDerivAt q hmap
  have hBq : HasDerivAt (fun t : ℝ => characteristicAngularFactor D S C (x, t) p)
      (fderiv ℝ (fun s : ℝ × PolarPoint =>
        characteristicAngularFactor D S C (x, s.1) s.2) (q, p) (1, (0, 0))) q := by
    simpa only [Function.comp_def] using
      (hB.differentiableAt (by simp)).hasFDerivAt.comp_hasDerivAt q hmap
  have hqnear : ∀ᶠ t : ℝ in 𝓝 q, |t| < ε :=
    continuousAt_id.abs.eventually_lt continuousAt_const hxq.2
  apply (hAq.sub (hBq.const_mul (characteristicRadialRoot D S C (x, 0) p.1))).congr_of_eventuallyEq
  filter_upwards [hqnear] with t ht
  simpa only [Pi.sub_apply, Pi.mul_apply, characteristicRadialRoot_q_eq] using
    hN01.minusCharacteristicSpeed_eq_separated hS hT
      (z := (x, t)) ⟨hxq.1, ht⟩ hsector hp

theorem N01Properties.characteristic_factors_q_angle_contDiffAt
    {r θ : ℝ} (hr : r ∈ Ioo D.a D.b) :
    ContDiffAt ℝ ∞ (fun v : PolarPoint =>
      stateCharacteristicDrift D S C (x, v.1) (r, v.2)) (q, θ) ∧
    ContDiffAt ℝ ∞ (fun v : PolarPoint =>
      characteristicAngularFactor D S C (x, v.1) (r, v.2)) (q, θ) := by
  obtain ⟨hA, hB⟩ := hN01.characteristic_factors_parameter_contDiffAt hS hT hxq hsector
    (p := (r, θ)) ⟨hr, mem_univ _⟩
  have hmap : ContDiffAt ℝ ∞ (fun v : PolarPoint => (v.1, (r, v.2))) (q, θ) :=
    contDiffAt_fst.prodMk (contDiffAt_const.prodMk contDiffAt_snd)
  constructor
  · simpa only [Function.comp_def] using ContDiffAt.comp
      (f := fun v : PolarPoint => (v.1, (r, v.2)))
      (g := fun s : ℝ × PolarPoint => stateCharacteristicDrift D S C (x, s.1) s.2)
      (q, θ) hA hmap
  · simpa only [Function.comp_def] using ContDiffAt.comp
      (f := fun v : PolarPoint => (v.1, (r, v.2)))
      (g := fun s : ℝ × PolarPoint => characteristicAngularFactor D S C (x, s.1) s.2)
      (q, θ) hB hmap

/-- The actual speed is smooth jointly in the height parameter and angle
at every annular radius, including the turning radii. -/
theorem N01Properties.minusCharacteristicSpeed_q_angle_contDiffAt
    {r θ : ℝ} (hr : r ∈ Ioo D.a D.b) :
    ContDiffAt ℝ ∞ (fun v : PolarPoint =>
      minusCharacteristicSpeed (originalCoefficients D S C (x, v.1)) (r, v.2)) (q, θ) := by
  obtain ⟨hAs, hBs⟩ :=
    hN01.characteristic_factors_q_angle_contDiffAt hS hT hxq hsector (θ := θ) hr
  have hnear : ∀ᶠ v : PolarPoint in 𝓝 (q, θ), |v.1| < ε :=
    continuousAt_fst.abs.eventually_lt continuousAt_const hxq.2
  have hmul : ContDiffAt ℝ ∞ (fun v : PolarPoint =>
      characteristicRadialRoot D S C (x, 0) r *
        characteristicAngularFactor D S C (x, v.1) (r, v.2)) (q, θ) :=
    contDiffAt_const.mul hBs
  apply (hAs.sub hmul).congr_of_eventuallyEq
  filter_upwards [hnear] with v hv
  simpa only [Pi.sub_apply, Pi.mul_apply, characteristicRadialRoot_q_eq] using
    hN01.minusCharacteristicSpeed_eq_separated hS hT
      (z := (x, v.1)) ⟨hxq.1, hv⟩ hsector (p := (r, v.2)) ⟨hr, mem_univ _⟩

/-- Joint differentiation in the construction parameter and the angle
uses only smooth factors; the radial square root is constant on this slice. -/
theorem N01Properties.minusCharacteristicSpeed_hasFDerivAt_q_angle
    {r θ : ℝ} (hr : r ∈ Ioo D.a D.b) :
    HasFDerivAt (fun v : PolarPoint =>
      minusCharacteristicSpeed (originalCoefficients D S C (x, v.1)) (r, v.2))
      ((ContinuousLinearMap.toSpanSingleton ℝ
        (characteristicQDerivative D S C x (q, (r, θ)))).coprod
        (ContinuousLinearMap.toSpanSingleton ℝ
          (characteristicAngularDerivative D S C (x, q) (r, θ)))) (q, θ) := by
  have hv := (hN01.minusCharacteristicSpeed_q_angle_contDiffAt hS hT hxq hsector
    (θ := θ) hr).differentiableAt (by simp)
  exact hasFDerivAt_coprod_of_hasDerivAt_slices hv.hasFDerivAt
    (hN01.minusCharacteristicSpeed_hasDerivAt_q hS hT hxq hsector
      (p := (r, θ)) ⟨hr, mem_univ _⟩)
    (hN01.minusCharacteristicSpeed_hasDerivAt_angular hS hT hxq hsector hr θ)

theorem N01Properties.characteristicQDerivative_angular_periodic
    {r : ℝ} (hr : r ∈ Ioo D.a D.b) :
    Function.Periodic (fun θ =>
      characteristicQDerivative D S C x (q, (r, θ))) Real.pi := by
  intro θ
  have heq : (fun t : ℝ =>
      minusCharacteristicSpeed (originalCoefficients D S C (x, t)) (r, θ + Real.pi)) =
    (fun t : ℝ => minusCharacteristicSpeed (originalCoefficients D S C (x, t)) (r, θ)) :=
    funext (fun t => minusCharacteristicSpeed_angular_periodic_of_physical hS C (x, t) r θ)
  have hs := hN01.minusCharacteristicSpeed_hasDerivAt_q hS hT hxq hsector
    (p := (r, θ + Real.pi)) ⟨hr, mem_univ _⟩
  rw [heq] at hs
  exact hs.unique (hN01.minusCharacteristicSpeed_hasDerivAt_q hS hT hxq hsector
    (p := (r, θ)) ⟨hr, mem_univ _⟩)

theorem N01Properties.characteristicAngularDerivative_periodic
    {r : ℝ} (hr : r ∈ Ioo D.a D.b) :
    Function.Periodic (fun θ =>
      characteristicAngularDerivative D S C (x, q) (r, θ)) Real.pi := by
  intro θ
  let V : ℝ → ℝ := fun t =>
    minusCharacteristicSpeed (originalCoefficients D S C (x, q)) (r, t)
  have heq : (fun t => V (t + Real.pi)) = V :=
    funext (minusCharacteristicSpeed_angular_periodic_of_physical hS C (x, q) r)
  have hd : deriv V (θ + Real.pi) = deriv V θ := by
    rw [← deriv_comp_add_const V Real.pi θ, heq]
  exact (hN01.minusCharacteristicSpeed_hasDerivAt_angular hS hT hxq hsector hr
    (θ + Real.pi)).deriv.symm.trans (hd.trans
      (hN01.minusCharacteristicSpeed_hasDerivAt_angular hS hT hxq hsector hr θ).deriv)

omit hxq in
theorem N01Properties.characteristicQDerivative_zero
    (hx : (x, 0) ∈ stateNeighborhood S C base ε)
    {p : PolarPoint} (hp : p ∈ annularOpen D) :
    characteristicQDerivative D S C x (0, p) =
      heightSpeedVariation (stateProfile D S C x) (stateU S x) p :=
  (hN01.minusCharacteristicSpeed_hasDerivAt_q hS hT hx hsector hp).unique
    (hN01.hasDerivAt_minusCharacteristicSpeed_q_zero hS hT x hp)

end ActualFactors

/-- Both genuine partial derivatives have a common bound on a closed
parameter box and the complete closed radial component. -/
theorem N01Properties.characteristicParameterDerivatives_bounded
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {base loss : ℕ} {ε : ℝ}
    (hN01 : N01Properties D T S C base loss ε)
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    {x : AnnularState S} (hx : (x, 0) ∈ stateNeighborhood S C base ε)
    (hsector : stateSector S x) (m : ℕ) (R : ℝ) :
    ∃ δ B : ℝ, 0 < δ ∧ δ < ε ∧ 0 ≤ B ∧
      ∀ q r θ, |q| ≤ δ → r ∈ Icc (C.left m) (C.right m) → |θ| ≤ R →
        |characteristicQDerivative D S C x (q, (r, θ))| ≤ B ∧
        |characteristicAngularDerivative D S C (x, q) (r, θ)| ≤ B := by
  have hε : 0 < ε := by simpa only [abs_zero] using hx.2
  let δ : ℝ := ε / 2
  have hδpos : 0 < δ := div_pos hε (by norm_num)
  have hδε : δ < ε := by dsimp only [δ]; linarith
  let K : Set (ℝ × PolarPoint) :=
    Icc (-δ) δ ×ˢ (Icc (C.left m) (C.right m) ×ˢ Icc (-R) R)
  have hK : IsCompact K := isCompact_Icc.prod (isCompact_Icc.prod isCompact_Icc)
  have hcontrol : controlGeometryConditions D S C := hN01.2.2.2.1
  have hvalid {s : ℝ × PolarPoint} (hs : s ∈ K) :
      (x, s.1) ∈ stateNeighborhood S C base ε :=
    ⟨hx.1, (abs_le.mpr hs.1).trans_lt hδε⟩
  have hcore {s : ℝ × PolarPoint} (hs : s ∈ K) : s.2 ∈ annularOpen D :=
    ⟨⟨(hcontrol.1 m).1.trans_le hs.2.1.1,
      hs.2.1.2.trans_lt (hcontrol.1 m).2.2⟩, mem_univ _⟩
  have hQc : ContinuousOn (characteristicQDerivative D S C x) K := fun s hs =>
    (hN01.characteristicQDerivative_continuousAt hS hT (hvalid hs) hsector
      (hcore hs)).continuousWithinAt
  have hθc : ContinuousOn (fun s : ℝ × PolarPoint =>
      characteristicAngularDerivative D S C (x, s.1) s.2) K := fun s hs =>
    (hN01.characteristicAngularDerivative_parameter_continuousAt hS hT
      (hvalid hs) hsector (hcore hs)).continuousWithinAt
  obtain ⟨A, hA⟩ := hK.exists_bound_of_continuousOn hQc
  obtain ⟨B, hB⟩ := hK.exists_bound_of_continuousOn hθc
  refine ⟨δ, max (max A B) 0, hδpos, hδε, le_max_right _ _, ?_⟩
  intro q r θ hq hr hθ
  have hs : (q, (r, θ)) ∈ K := ⟨abs_le.mp hq, hr, abs_le.mp hθ⟩
  constructor
  · have hb : |characteristicQDerivative D S C x (q, (r, θ))| ≤ A := by
      simpa only [Real.norm_eq_abs] using hA (q, (r, θ)) hs
    exact hb.trans ((le_max_left A B).trans (le_max_left _ _))
  · have hb : |characteristicAngularDerivative D S C (x, q) (r, θ)| ≤ B := by
      simpa only [Real.norm_eq_abs] using hB (q, (r, θ)) hs
    exact hb.trans ((le_max_right A B).trans (le_max_left _ _))

/-- Periodicity turns the compact angle bound into a bound on all real
angles, with the same parameter and radial box. -/
theorem N01Properties.characteristicParameterDerivatives_uniform_bound
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {base loss : ℕ} {ε : ℝ}
    (hN01 : N01Properties D T S C base loss ε)
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    {x : AnnularState S} (hx : (x, 0) ∈ stateNeighborhood S C base ε)
    (hsector : stateSector S x) (m : ℕ) :
    ∃ δ B : ℝ, 0 < δ ∧ δ < ε ∧ 0 ≤ B ∧
      ∀ q r θ, |q| ≤ δ → r ∈ Icc (C.left m) (C.right m) →
        |characteristicQDerivative D S C x (q, (r, θ))| ≤ B ∧
        |characteristicAngularDerivative D S C (x, q) (r, θ)| ≤ B := by
  obtain ⟨δ, B, hδ, hδε, hB, hbound⟩ :=
    hN01.characteristicParameterDerivatives_bounded hS hT hx hsector m Real.pi
  refine ⟨δ, B, hδ, hδε, hB, ?_⟩
  intro q r θ hq hr
  have hxq : (x, q) ∈ stateNeighborhood S C base ε := ⟨hx.1, hq.trans_lt hδε⟩
  have hcontrol : controlGeometryConditions D S C := hN01.2.2.2.1
  have hr' : r ∈ Ioo D.a D.b :=
    ⟨(hcontrol.1 m).1.trans_le hr.1, hr.2.trans_lt (hcontrol.1 m).2.2⟩
  have hperiod : Function.Periodic (fun t : ℝ =>
      (characteristicQDerivative D S C x (q, (r, t)),
        characteristicAngularDerivative D S C (x, q) (r, t))) Real.pi := by
    intro t
    exact Prod.ext
      (hN01.characteristicQDerivative_angular_periodic hS hT hxq hsector hr' t)
      (hN01.characteristicAngularDerivative_periodic hS hT hxq hsector hr' t)
  obtain ⟨t, ht, heq⟩ := hperiod.exists_mem_Ico₀ Real.pi_pos θ
  have hQt : characteristicQDerivative D S C x (q, (r, θ)) =
      characteristicQDerivative D S C x (q, (r, t)) := congrArg Prod.fst heq
  have hθt : characteristicAngularDerivative D S C (x, q) (r, θ) =
      characteristicAngularDerivative D S C (x, q) (r, t) := congrArg Prod.snd heq
  rw [hQt, hθt]
  exact hbound q r t hq hr (by simpa only [abs_of_nonneg ht.1] using ht.2.le)

theorem N01Properties.characteristicAngularDerivative_q_zero
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {base loss : ℕ} {ε : ℝ}
    (hN01 : N01Properties D T S C base loss ε)
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    {x : AnnularState S} (hx : (x, 0) ∈ stateNeighborhood S C base ε)
    (hsector : stateSector S x) {r : ℝ} (hr : r ∈ Ioo D.a D.b) (θ : ℝ) :
    characteristicAngularDerivative D S C (x, 0) (r, θ) = 0 := by
  have hw := contDiff_stateProfile_of_n01 hS hT hN01 x
  obtain ⟨_, hgeom⟩ := hN01.1.1
  have hr0 : r ≠ 0 := (hgeom.1.1.trans hr.1).ne'
  have hwp : 0 < stateProfile D S C x r :=
    mul_pos (hgeom.1.2.2.2.2.1 r hr) (Real.exp_pos _)
  have heq : (fun t : ℝ =>
      minusCharacteristicSpeed (originalCoefficients D S C (x, 0)) (r, t)) =
      fun _ : ℝ => -opticalSpeed (stateProfile D S C x) r := by
    funext t
    obtain ⟨ha, hb, hc⟩ := originalCoefficients_radial_zero x hw (r, t)
    exact minusCharacteristicSpeed_of_radial_coefficients ha hb hc hr0 hwp
  have hd := hN01.minusCharacteristicSpeed_hasDerivAt_angular hS hT hx hsector hr θ
  rw [heq] at hd
  exact hd.unique (hasDerivAt_const θ _)

end ContinuousFlexibility.Statements
