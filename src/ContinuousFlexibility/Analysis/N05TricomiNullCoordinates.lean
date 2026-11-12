import ContinuousFlexibility.Analysis.N05ReferenceCutImage
import ContinuousFlexibility.Analysis.N05CanonicalBoundarySymmetry
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
# Actual null coordinates of the reference Tricomi chart

The function `(2/3) * ξ * sqrt ξ` has derivative `sqrt ξ` for positive
canonical radius.  The principal identities obtained from N04 therefore
force both actual functions `φ ± (2/3) ξ sqrt ξ` to have null differential.
Their angular derivatives cannot vanish, by the nonzero mixed pairing
with the radial chart coordinate.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open Set Filter
open scoped Topology ContDiff

set_option backward.isDefEq.respectTransparency false

def n05TricomiTime (t : ℝ) : ℝ := (2 / 3 : ℝ) * t * Real.sqrt t

theorem n05TricomiTime_continuous : Continuous n05TricomiTime :=
  (continuous_const.mul continuous_id).mul Real.continuous_sqrt

theorem n05TricomiTime_zero : n05TricomiTime 0 = 0 := by
  simp only [n05TricomiTime, mul_zero, zero_mul]

theorem n05TricomiTime_hasDerivAt {t : ℝ} (ht : 0 < t) :
    HasDerivAt n05TricomiTime (Real.sqrt t) t := by
  have hs := Real.hasDerivAt_sqrt ht.ne'
  have hs0 : Real.sqrt t ≠ 0 := (Real.sqrt_pos.mpr ht).ne'
  have hvalue : (2 / 3 : ℝ) * Real.sqrt t +
      ((2 / 3 : ℝ) * t) * (1 / (2 * Real.sqrt t)) = Real.sqrt t := by
    field_simp [hs0]
    nlinarith only [Real.sq_sqrt ht.le]
  convert (((hasDerivAt_id t).const_mul (2 / 3 : ℝ)).mul hs) using 1 <;>
    simp only [Pi.mul_def, id_eq, mul_one, hvalue]
  rfl

def n05NullCoordinate (Ψ : PolarPoint → PolarPoint) (σ : ℝ) : PolarPoint → ℝ :=
  fun p => (Ψ p).2 + σ * n05TricomiTime (Ψ p).1

theorem n05NullCoordinate_contDiffAt
    {Ψ : PolarPoint → PolarPoint} {x : PolarPoint}
    (hΨ : ContDiffAt ℝ ∞ Ψ x) (hx : 0 < (Ψ x).1) (σ : ℝ) :
    ContDiffAt ℝ ∞ (n05NullCoordinate Ψ σ) x := by
  exact hΨ.snd.add (contDiffAt_const.mul
    ((contDiffAt_const.mul hΨ.fst).mul (hΨ.fst.sqrt hx.ne')))

theorem n05NullCoordinate_partials
    {Ψ : PolarPoint → PolarPoint} {x : PolarPoint}
    (hΨ : DifferentiableAt ℝ Ψ x) (hx : 0 < (Ψ x).1) (σ : ℝ) :
    radialPartial (n05NullCoordinate Ψ σ) x =
        radialPartial (fun p => (Ψ p).2) x +
          σ * (Real.sqrt (Ψ x).1 * radialPartial (fun p => (Ψ p).1) x) ∧
      angularPartial (n05NullCoordinate Ψ σ) x =
        angularPartial (fun p => (Ψ p).2) x +
          σ * (Real.sqrt (Ψ x).1 * angularPartial (fun p => (Ψ p).1) x) := by
  have ht : HasFDerivAt (fun p => n05TricomiTime (Ψ p).1)
      (Real.sqrt (Ψ x).1 • fderiv ℝ (fun p => (Ψ p).1) x) x := by
    simpa only [Function.comp_def] using
      (n05TricomiTime_hasDerivAt hx).comp_hasFDerivAt
        (f := fun p : PolarPoint => (Ψ p).1) x hΨ.fst.hasFDerivAt
  have hn : HasFDerivAt (n05NullCoordinate Ψ σ)
      (fderiv ℝ (fun p => (Ψ p).2) x +
        σ • (Real.sqrt (Ψ x).1 • fderiv ℝ (fun p => (Ψ p).1) x)) x :=
    hΨ.snd.hasFDerivAt.add (ht.const_mul σ)
  constructor <;>
    simp only [radialPartial, angularPartial, hn.fderiv,
      ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul]

/-- Algebraic nullness and the nonzero cross pairing, using the three
principal identities rather than assuming a characteristic formula. -/
theorem n05_null_symbol_algebra
    {a c H j v xr xt pr pt σ s : ℝ}
    (hH : H ≠ 0) (hs : s ^ 2 = v) (hσ : σ ^ 2 = 1)
    (hrr : H * (a * xr * xr + c * xt * xt) = j)
    (hrt : H * (a * xr * pr + c * xt * pt) = 0)
    (htt : H * (a * pr * pr + c * pt * pt) = j * (-v)) :
    a * (pr + σ * (s * xr)) ^ 2 + c * (pt + σ * (s * xt)) ^ 2 = 0 ∧
      H * (a * xr * (pr + σ * (s * xr)) + c * xt * (pt + σ * (s * xt))) =
        σ * s * j := by
  have hnull : H * (a * (pr + σ * (s * xr)) ^ 2 +
      c * (pt + σ * (s * xt)) ^ 2) = 0 := by
    calc
      _ = H * (a * pr * pr + c * pt * pt) +
          2 * σ * s * (H * (a * xr * pr + c * xt * pt)) +
          σ ^ 2 * s ^ 2 * (H * (a * xr * xr + c * xt * xt)) := by ring
      _ = 0 := by rw [hrr, hrt, htt, hσ, hs]; ring
  refine ⟨(mul_eq_zero.mp hnull).resolve_left hH, ?_⟩
  calc
    _ = H * (a * xr * pr + c * xt * pt) +
        σ * s * (H * (a * xr * xr + c * xt * xt)) := by ring
    _ = σ * s * j := by rw [hrt, hrr]; ring

theorem n05_null_angular_ne_zero_algebra
    {a c H xr xt nr nt σ s j : ℝ}
    (ha : 0 < a) (hσ : σ ≠ 0) (hs : s ≠ 0) (hj : j ≠ 0)
    (hnull : a * nr ^ 2 + c * nt ^ 2 = 0)
    (hcross : H * (a * xr * nr + c * xt * nt) = σ * s * j) : nt ≠ 0 := by
  intro hnt
  have hsq : a * nr ^ 2 = 0 := by
    simpa only [hnt, pow_two, mul_zero, add_zero] using hnull
  have hnr : nr = 0 := sq_eq_zero_iff.mp ((mul_eq_zero.mp hsq).resolve_left ha.ne')
  have hzero : σ * s * j = 0 := by
    simpa only [hnr, hnt, mul_zero, add_zero] using hcross.symm
  exact (mul_ne_zero (mul_ne_zero hσ hs) hj) hzero

/-- Both signed null coordinates satisfy the actual reference null equation
and retain a nonzero pairing with the canonical radius. -/
theorem n05_negative_reference_null_identities
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {R : ReturnEquationData S}
    {L : ReturnCorrectionData S} {K : CanonicalData S} {base loss : ℕ} {ε : ℝ}
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (h : NonlinearPropertiesThrough04 D T S C R L K base loss ε)
    {m : ℕ} (hm : K.positive m = false) {x : PolarPoint}
    (hx : x ∈ referencePhysicalPieceOpen S K m) {σ : ℝ} (hσ : σ ^ 2 = 1) :
    let Ψ := K.chart (C.referenceState, 0) m
    let N := n05NullCoordinate Ψ σ
    let ξ := fun p => (Ψ p).1
    D.w x.1 * radialPartial N x ^ 2 +
        (deriv D.w x.1 / x.1) * angularPartial N x ^ 2 = 0 ∧
      K.height (C.referenceState, 0) m x ^ 2 *
          (D.w x.1 * radialPartial ξ x * radialPartial N x +
            (deriv D.w x.1 / x.1) * angularPartial ξ x * angularPartial N x) =
        σ * Real.sqrt (Ψ x).1 * |planeJacobian Ψ x| := by
  dsimp only
  have h01 := h.1.1.1
  have h04 := h.2.2.2.2
  have hpieces := h04.1.referenceBounds
  have hnegative := h04.1.referenceNegative
  have hxClosed : x.1 ∈ Icc (K.physicalLeft m) (K.physicalRight m) :=
    ⟨hx.1.1.le, hx.1.2.le⟩
  have hxD : x ∈ annularOpen D := ⟨(hpieces m).2.2 hx.1, mem_univ _⟩
  have hpos := n05_negative_reference_radius_pos hT hS h hm hxClosed hxD
    (hnegative m hm x.1 hx.1)
  obtain ⟨hΨ, _, _, hh⟩ := n05_reference_boundary_regular h04.1
    (n05_referenceState_mem h01.2.1) (n05_referenceState_sector h01.2.2.1) m (p := x) hxClosed
  have hsym := n05_negative_reference_symbol_closed hT hS h hm hxClosed
  dsimp only at hsym
  simp only [n05PrincipalPair, n05RadialReferenceCoefficients, zero_mul, add_zero] at hsym
  have hd := n05NullCoordinate_partials (hΨ.differentiableAt (by simp)) hpos σ
  rw [hd.1, hd.2]
  exact n05_null_symbol_algebra (pow_ne_zero 2 hh.ne') (Real.sq_sqrt hpos.le) hσ
    hsym.1 hsym.2.1 hsym.2.2

/-- The angular differential of either actual null coordinate is nonzero
throughout a negative physical piece. -/
theorem n05_negative_reference_null_angular_ne_zero
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {R : ReturnEquationData S}
    {L : ReturnCorrectionData S} {K : CanonicalData S} {base loss : ℕ} {ε : ℝ}
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (h : NonlinearPropertiesThrough04 D T S C R L K base loss ε)
    {m : ℕ} (hm : K.positive m = false) {x : PolarPoint}
    (hx : x ∈ referencePhysicalPieceOpen S K m) {σ : ℝ} (hσ : σ ^ 2 = 1) :
    angularPartial (n05NullCoordinate (K.chart (C.referenceState, 0) m) σ) x ≠ 0 := by
  have h01 := h.1.1.1
  have h04 := h.2.2.2.2
  have hpieces := h04.1.referenceBounds
  have hnegative := h04.1.referenceNegative
  have hxClosed : x.1 ∈ Icc (K.physicalLeft m) (K.physicalRight m) :=
    ⟨hx.1.1.le, hx.1.2.le⟩
  have hxD : x ∈ annularOpen D := ⟨(hpieces m).2.2 hx.1, mem_univ _⟩
  obtain ⟨B, hB⟩ := h01.1.1
  have hw : 0 < D.w x.1 := hB.1.2.2.2.2.1 x.1 hxD.1
  have hpos := n05_negative_reference_radius_pos hT hS h hm hxClosed hxD
    (hnegative m hm x.1 hx.1)
  have hJ := (n05_reference_boundary_regular h04.1 (n05_referenceState_mem h01.2.1)
    (n05_referenceState_sector h01.2.2.1) m (p := x) hxClosed).2.2.1
  have hσ0 : σ ≠ 0 := by
    intro hz
    rw [hz] at hσ
    norm_num at hσ
  have hid := n05_negative_reference_null_identities hT hS h hm hx hσ
  exact n05_null_angular_ne_zero_algebra hw hσ0
    (Real.sqrt_pos.mpr hpos).ne' (abs_ne_zero.mpr hJ) hid.1 hid.2

end ContinuousFlexibility.Statements

