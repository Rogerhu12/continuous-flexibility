import ContinuousFlexibility.Analysis.N06ReferenceCutTravel
import ContinuousFlexibility.Radial.ScaleSlowVariation

/-!
# Quantitative travel and half-widths on the original physical cells

The first return margin gives a lower bound for the actual optical
travel.  The reciprocal profile estimate on the same original physical
cell bounds the optical speed.  Consequently the actual N04 cut, which
bisects that travel, has two quantitatively nonzero physical half-widths
and a quantitatively nonzero canonical radius.

Every coefficient exponent below uses the cell supplied by
`RadialReturnMargins`.  No identification with `K.cell` is asserted.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open Set MeasureTheory
open scoped ContDiff

set_option backward.isDefEq.respectTransparency false

/-- A true optical speed bound on every original physical cell.  Only
the retained reciprocal-profile bound and the global smooth profile
are used; no root model is needed. -/
theorem n06_profile_opticalSpeed_bound {D : ReferenceData}
    (hD : IsAccumulatingProfile D) :
    ∃ M A : ℝ, 1 ≤ M ∧ 0 < A ∧ ∀ j r, r ∈ D.cells j →
      opticalSpeed D.w r ≤ M * radialE (D.cellIndex j) ^ A := by
  obtain ⟨C, hC⟩ := hD
  rcases hC with ⟨hgeom, hpart, hCpos, _, _, _, _, _, _, hinv, _, _, _⟩
  have hw : ContDiff ℝ ∞ D.w := hgeom.2.2.1.1
  obtain ⟨M₀, hM₀⟩ := isCompact_Icc.exists_bound_of_continuousOn
    ((hw.continuous_deriv (by simp)).continuousOn :
      ContinuousOn (deriv D.w) (Icc D.a D.b))
  let Mder : ℝ := max 1 M₀
  let B : ℝ := Mder * D.a⁻¹ * C 0
  have hMder : 0 < Mder := zero_lt_one.trans_le (le_max_left _ _)
  have hB : 0 < B := mul_pos (mul_pos hMder (inv_pos.mpr hgeom.1)) (hCpos 0)
  refine ⟨B + 1, C 0, by linarith only [hB], hCpos 0, ?_⟩
  intro j r hr
  have hcore : r ∈ radialCore D := hpart.2.2.2.1 j hr
  have hrpos : 0 < r := hgeom.1.trans hcore.1
  have hwpos : 0 < D.w r := hgeom.2.2.2.2.1 r hcore
  have hder : -deriv D.w r ≤ Mder := by
    have habs : |deriv D.w r| ≤ M₀ := by
      simpa only [Real.norm_eq_abs] using hM₀ r ⟨hcore.1.le, hcore.2.le⟩
    exact (neg_le_abs _).trans (habs.trans (le_max_right _ _))
  have hrinv : r⁻¹ ≤ D.a⁻¹ := inv_anti₀ hgeom.1 hcore.1.le
  have hwinv : (D.w r)⁻¹ ≤ C 0 * radialE (D.cellIndex j) ^ C 0 := by
    have hb := hinv j r hr 0
    change |(D.w r)⁻¹| ≤ C 0 * radialE (D.cellIndex j) ^ C 0 at hb
    simpa only [abs_of_pos (inv_pos.mpr hwpos)] using hb
  have hE : 1 ≤ radialE (D.cellIndex j) :=
    Real.one_le_exp_iff.mpr (Radial.radialQ_nonneg _)
  have hP : 1 ≤ radialE (D.cellIndex j) ^ C 0 :=
    Real.one_le_rpow hE (hCpos 0).le
  have hrad : -deriv D.w r / (r * D.w r) ≤
      B * radialE (D.cellIndex j) ^ C 0 := by
    calc
      -deriv D.w r / (r * D.w r) =
          (-deriv D.w r * r⁻¹) * (D.w r)⁻¹ := by
        simp only [div_eq_mul_inv, mul_inv_rev]
        ring
      _ ≤ (Mder * r⁻¹) * (D.w r)⁻¹ :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right hder (inv_nonneg.mpr hrpos.le))
          (inv_nonneg.mpr hwpos.le)
      _ ≤ (Mder * D.a⁻¹) * (D.w r)⁻¹ :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hrinv hMder.le)
          (inv_nonneg.mpr hwpos.le)
      _ ≤ (Mder * D.a⁻¹) * (C 0 * radialE (D.cellIndex j) ^ C 0) :=
        mul_le_mul_of_nonneg_left hwinv
          (mul_nonneg hMder.le (inv_nonneg.mpr hgeom.1.le))
      _ = B * radialE (D.cellIndex j) ^ C 0 := by dsimp only [B]; ring
  have hbound : 1 ≤ (B + 1) * radialE (D.cellIndex j) ^ C 0 := by
    calc
      1 ≤ B + 1 := by linarith only [hB]
      _ = (B + 1) * 1 := (mul_one _).symm
      _ ≤ (B + 1) * radialE (D.cellIndex j) ^ C 0 :=
        mul_le_mul_of_nonneg_left hP (by positivity)
  apply Real.sqrt_le_iff.mpr
  refine ⟨zero_le_one.trans hbound, hrad.trans ?_⟩
  have hsmall : B * radialE (D.cellIndex j) ^ C 0 ≤
      (B + 1) * radialE (D.cellIndex j) ^ C 0 :=
    mul_le_mul_of_nonneg_right (by linarith) (zero_le_one.trans hP)
  exact hsmall.trans (by nlinarith only [hbound])

/-- The original return margin controls the actual component travel and
its optical speed on the closed component, with one original cell index.
The speed bound at the roots follows by continuity from the open cell. -/
theorem n06_return_component_travel_bounds {D : ReferenceData}
    (hD : IsAccumulatingProfile D) (hreturn : RadialReturnMargins D) :
    ∃ M A : ℝ, 1 ≤ M ∧ 0 < A ∧ ∀ l r,
      NegativeRadialComponent D l r → ∃ j : ℕ,
        Ioo l r ⊆ D.cells j ∧
        radialE (D.cellIndex j) ^ (-A) ≤ radialTravel D l r ∧
        ∀ x ∈ Icc l r,
          opticalSpeed D.w x ≤ M * radialE (D.cellIndex j) ^ A := by
  obtain ⟨M, A₀, hM, hA₀, hspeed⟩ := n06_profile_opticalSpeed_bound hD
  obtain ⟨A₁, hA₁, hret⟩ := hreturn.2
  let A : ℝ := max A₀ A₁
  have hA : 0 < A := hA₀.trans_le (le_max_left _ _)
  refine ⟨M, A, hM, hA, ?_⟩
  intro l r hneg
  obtain ⟨_, j, hcell, c, hc, hcinv, hmargin⟩ := hret l r hneg
  have hE : 1 ≤ radialE (D.cellIndex j) :=
    Real.one_le_exp_iff.mpr (Radial.radialQ_nonneg _)
  have hEpos : 0 < radialE (D.cellIndex j) := zero_lt_one.trans_le hE
  have hlower : radialE (D.cellIndex j) ^ (-A₁) ≤ c := by
    simpa only [Real.rpow_neg hEpos.le] using inv_le_of_inv_le₀ hc hcinv
  have hsin : c ≤ |Real.sin (radialTravel D l r)| := by
    simpa only [Nat.cast_one, div_one, one_mul] using hmargin 1 (by omega)
  have htravel0 : 0 ≤ radialTravel D l r :=
    intervalIntegral.integral_nonneg_of_forall hneg.2.1.le
      (fun _ => Real.sqrt_nonneg _)
  have htravel : radialE (D.cellIndex j) ^ (-A) ≤ radialTravel D l r := by
    calc
      radialE (D.cellIndex j) ^ (-A) ≤ radialE (D.cellIndex j) ^ (-A₁) :=
        Real.rpow_le_rpow_of_exponent_le hE (neg_le_neg (le_max_right _ _))
      _ ≤ c := hlower
      _ ≤ |Real.sin (radialTravel D l r)| := hsin
      _ ≤ |radialTravel D l r| := Real.abs_sin_le_abs
      _ = radialTravel D l r := abs_of_nonneg htravel0
  have hopen (x : ℝ) (hx : x ∈ Ioo l r) :
      opticalSpeed D.w x ≤ M * radialE (D.cellIndex j) ^ A :=
    (hspeed j x (hcell hx)).trans
      (mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_exponent_le hE (le_max_left _ _))
        (zero_le_one.trans hM))
  obtain ⟨C, hC⟩ := hD
  have hv : ContinuousOn (opticalSpeed D.w) (Icc l r) :=
    continuousOn_opticalSpeed_of_profile hC.1.2.2.1.1
      (hC.1.1.trans hneg.1) (fun x hx =>
        hC.1.2.2.2.2.1 x ⟨hneg.1.trans_le hx.1, hx.2.trans_lt hneg.2.2.1⟩)
  refine ⟨j, hcell, htravel, ?_⟩
  intro x hx
  have hxclosure : x ∈ closure (Ioo l r) := by
    simpa only [closure_Ioo hneg.2.1.ne] using hx
  have hclosed := ((hv x hx).mono Ioo_subset_Icc_self).mem_closure hxclosure
    (show MapsTo (opticalSpeed D.w) (Ioo l r)
      (Iic (M * radialE (D.cellIndex j) ^ A)) from hopen)
  simpa only [isClosed_Iic.closure_eq, mem_Iic] using hclosed

private theorem n06_halfWidth_of_travel_bound
    {M A E l r t : ℝ} {v : ℝ → ℝ}
    (hM : 0 < M) (hE : 0 < E) (hlr : l ≤ r)
    (hv : ContinuousOn v (Icc l r))
    (hbound : ∀ x ∈ Icc l r, v x ≤ M * E ^ A)
    (htravel : (∫ x in l..r, v x) = t)
    (hlower : E ^ (-A) ≤ 2 * t) :
    (2 * M)⁻¹ * E ^ (-(2 * A)) ≤ r - l := by
  have hi : IntervalIntegrable v volume l r := hv.intervalIntegrable_of_Icc hlr
  have hc : IntervalIntegrable (fun _ : ℝ => M * E ^ A) volume l r :=
    intervalIntegrable_const
  have hint := intervalIntegral.integral_mono_on hlr hi hc hbound
  rw [htravel, intervalIntegral.integral_const, smul_eq_mul] at hint
  have hprod : 0 < M * E ^ A := mul_pos hM (Real.rpow_pos_of_pos hE _)
  have hquot : (E ^ (-A) / 2) / (M * E ^ A) ≤ r - l := by
    apply (div_le_iff₀ hprod).mpr
    nlinarith only [hlower, hint]
  have halgebra : (E ^ (-A) / 2) / (M * E ^ A) =
      (2 * M)⁻¹ * E ^ (-(2 * A)) := by
    have hexp : -A - A = -(2 * A) := by ring
    calc
      (E ^ (-A) / 2) / (M * E ^ A) =
          (2 * M)⁻¹ * (E ^ (-A) / E ^ A) := by
        simp only [div_eq_mul_inv, mul_inv_rev]
        ring
      _ = (2 * M)⁻¹ * E ^ (-(2 * A)) := by rw [← Real.rpow_sub hE, hexp]
  exact halgebra ▸ hquot

private theorem n06_cutRadius_of_travel_bound
    {A E R : ℝ} (hA : 0 < A) (hE : 1 ≤ E) (hR : 0 < R)
    (hlower : E ^ (-A) ≤ 2 * n05TricomiTime R) :
    (1 / 2 : ℝ) * E ^ (-A) ≤ R := by
  by_cases hRone : R ≤ 1
  · have hsqrt : Real.sqrt R ≤ 1 := Real.sqrt_le_one.mpr hRone
    have htime : n05TricomiTime R ≤ R := by
      unfold n05TricomiTime
      have hm := mul_le_mul_of_nonneg_left hsqrt
        (show 0 ≤ (2 / 3 : ℝ) * R by positivity)
      nlinarith only [hm, hR]
    linarith only [hlower, htime]
  · have hpow : E ^ (-A) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos hE (neg_nonpos.mpr hA.le)
    linarith only [hpow, hRone]

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {R : ReturnEquationData S}
  {L : ReturnCorrectionData S} {K : CanonicalData S} {base loss : ℕ} {ε : ℝ}

/-- Polynomial lower bounds for the actual N04 cut and its two physical
half-widths, derived from the original retained profile and return margin.
The common index `j` is the actual cell from `RadialReturnMargins`. -/
theorem n06_reference_cut_physical_bounds
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (h : NonlinearPropertiesThrough04 D T S C R L K base loss ε) :
    ∃ M A : ℝ, 1 ≤ M ∧ 0 < A ∧ ∀ m, ∃ j : ℕ,
      Ioo (C.left m) (C.right m) ⊆ D.cells j ∧
      radialE (D.cellIndex j) ^ (-A) ≤ radialTravel D (C.left m) (C.right m) ∧
      (2 * M)⁻¹ * radialE (D.cellIndex j) ^ (-(2 * A)) ≤
        K.physicalRight (K.cutPair m).1 - C.left m ∧
      (2 * M)⁻¹ * radialE (D.cellIndex j) ^ (-(2 * A)) ≤
        C.right m - K.physicalRight (K.cutPair m).1 ∧
      (1 / 2 : ℝ) * radialE (D.cellIndex j) ^ (-A) ≤ K.cutRadius m := by
  have h01 := h.1.1.1
  have hg : controlGeometryConditions D S C := h01.2.2.2.1
  obtain ⟨M, A, hM, hA, hb⟩ :=
    n06_return_component_travel_bounds h01.1.1 h01.1.2.2.1
  refine ⟨M, A, hM, hA, ?_⟩
  intro m
  have hneg : NegativeRadialComponent D (C.left m) (C.right m) :=
    ⟨(hg.1 m).1, (hg.1 m).2.1, (hg.1 m).2.2,
      (hg.2.1 m).1, (hg.2.1 m).2.1, hg.2.2.2.1 m⟩
  obtain ⟨j, hj, htravel, hspeed⟩ := hb (C.left m) (C.right m) hneg
  have ht := n06_reference_cut_travel hT hS h m
  have hlower : radialE (D.cellIndex j) ^ (-A) ≤
      2 * n05TricomiTime (K.cutRadius m) := ht.2.2 ▸ htravel
  have hpieces := h.2.2.2.2.1.referenceBounds
  have hcuts := h.2.2.2.2.2.1.1.1
  obtain ⟨_, _, hl, hr, hmeet, hy, _, _, _, _⟩ := hcuts m
  let cut : ℝ := K.physicalRight (K.cutPair m).1
  have hlc : C.left m < cut := by
    rw [← hl]
    exact (hpieces (K.cutPair m).1).1
  have hcr : cut < C.right m := by
    dsimp only [cut]
    rw [hmeet, ← hr]
    exact (hpieces (K.cutPair m).2).1
  obtain ⟨Q, hQ⟩ := h01.1.1
  have hv : ContinuousOn (opticalSpeed D.w) (Icc (C.left m) (C.right m)) :=
    continuousOn_opticalSpeed_of_profile hQ.1.2.2.1.1
      (hQ.1.1.trans hneg.1) (fun x hx =>
        hQ.1.2.2.2.2.1 x ⟨hneg.1.trans_le hx.1, hx.2.trans_lt hneg.2.2.1⟩)
  have hE : 1 ≤ radialE (D.cellIndex j) :=
    Real.one_le_exp_iff.mpr (Radial.radialQ_nonneg _)
  have hEpos : 0 < radialE (D.cellIndex j) := zero_lt_one.trans_le hE
  have hMpos : 0 < M := zero_lt_one.trans_le hM
  refine ⟨j, hj, htravel, ?_, ?_, n06_cutRadius_of_travel_bound hA hE hy hlower⟩
  · exact n06_halfWidth_of_travel_bound hMpos hEpos hlc.le
      (hv.mono (Icc_subset_Icc le_rfl hcr.le))
      (fun x hx => hspeed x ⟨hx.1, hx.2.trans hcr.le⟩) ht.1 hlower
  · exact n06_halfWidth_of_travel_bound hMpos hEpos hcr.le
      (hv.mono (Icc_subset_Icc hlc.le le_rfl))
      (fun x hx => hspeed x ⟨hlc.le.trans hx.1, hx.2⟩) ht.2.1 hlower

end ContinuousFlexibility.Statements
