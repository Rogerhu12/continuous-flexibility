module

public import ContinuousFlexibility.Analysis.N06ReferenceRootLower
public import ContinuousFlexibility.Analysis.N06RootCollarFromProfile

/-!
# Genuine positive-side root collars for the selected reference

The root curvature lower bound and the original reciprocal-profile bound
pay for one explicit two-sided collar.  Its divided profile has controlled
ordinary jets and a positive lower bound.  The positive side is identified
by the actual sign of `w'`, and profile positivity keeps the whole collar
inside the physical annulus.

The cost still records both original cell labels.  The frozen cover and
weight contracts do not identify the physical return-margin cell with
`K.cell`; this theorem does not replace that missing comparison by an input.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Statements

open Set ContinuousFlexibility.Analysis
open scoped ContDiff

set_option backward.isDefEq.respectTransparency false

/-- The two original weights that pay for the genuine root collar. -/
def n06ReferenceRootCollarCost (D : ReferenceData) (T : MaterialData)
    {S : PhysicalSpacesData} (K : CanonicalData S) (A M : ℝ) (i j : ℕ) : ℝ :=
  (1 + M * T.E0 (T.sample (K.cell i)) ^ M) ^ 12 *
    (radialE (D.cellIndex j) ^ A) ^ 19

/-- Cell bounds extend to the actual closed interval by continuity;
membership of its endpoints in the open cell is unnecessary. -/
theorem n06_profileCell_closed_interval_lower
    {D : ReferenceData} {caps : ℕ → ℝ} (hD : AccumulatingProfileBounds D caps)
    {j : ℕ} {l r : ℝ} (hlr : l < r) (hcell : Ioo l r ⊆ D.cells j)
    {x : ℝ} (hx : x ∈ Icc l r) :
    (caps 0 * radialE (D.cellIndex j) ^ caps 0)⁻¹ ≤ D.w x := by
  rcases hD with ⟨hgeom, hpart, _, _, _, _, _, _, _, hinv, _⟩
  have hopen (t : ℝ) (ht : t ∈ Ioo l r) :
      (caps 0 * radialE (D.cellIndex j) ^ caps 0)⁻¹ ≤ D.w t := by
    have hb := hinv j t (hcell ht) 0
    change |(D.w t)⁻¹| ≤ caps 0 * radialE (D.cellIndex j) ^ caps 0 at hb
    exact inv_le_of_inv_le₀
      (hgeom.2.2.2.2.1 t (hpart.2.2.2.1 j (hcell ht)))
      ((le_abs_self _).trans hb)
  have hxclosure : x ∈ closure (Ioo l r) := by
    simpa only [closure_Ioo hlr.ne] using hx
  have hcont : ContinuousOn D.w (Icc l r) := hgeom.2.2.1.1.continuous.continuousOn
  have hclosed := ((hcont x hx).mono Ioo_subset_Icc_self).mem_closure hxclosure
    (show MapsTo D.w (Ioo l r)
      (Ici (caps 0 * radialE (D.cellIndex j) ^ caps 0)⁻¹) from hopen)
  simpa only [isClosed_Ici.closure_eq, mem_Ici] using hclosed

private theorem n06_reference_profile_four_bound
    {D : ReferenceData} (hw : ContDiff ℝ ∞ D.w) :
    ∃ B : ℝ, 1 ≤ B ∧ ∀ k : ℕ, k ≤ 4 → ∀ r ∈ Icc (D.a - 1) (D.b + 1),
      |iteratedDeriv k D.w r| ≤ B := by
  let f : ℝ → Fin 5 → ℝ := fun r i => iteratedDeriv i.val D.w r
  have hf : Continuous f := continuous_pi fun i => hw.continuous_iteratedDeriv i.val (by simp)
  obtain ⟨B0, hB0⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (hf.continuousOn : ContinuousOn f (Icc (D.a - 1) (D.b + 1)))
  refine ⟨max 1 B0, le_max_left _ _, fun k hk r hr => ?_⟩
  have hb : |iteratedDeriv k D.w r| ≤ ‖f r‖ := by
    simpa only [f, Real.norm_eq_abs] using norm_le_pi_norm (f r) (⟨k, by omega⟩ : Fin 5)
  exact hb.trans ((hB0 r hr).trans (le_max_right _ _))

private theorem n06_rootCollar_cutHalf_closed_subset
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {R : ReturnEquationData S}
    {L : ReturnCorrectionData S} {K : CanonicalData S}
    {base loss : ℕ} {ε : ℝ}
    (h : NonlinearPropertiesThrough04 D T S C R L K base loss ε)
    (m : ℕ) {i : ℕ} (hi : i = (K.cutPair m).1 ∨ i = (K.cutPair m).2) :
    Icc (K.physicalLeft i) (K.physicalRight i) ⊆ Icc (C.left m) (C.right m) := by
  have hpieces := h.2.2.2.2.1.1.referenceBounds
  have hcut := h.2.2.2.2.1.2.1.1.1
  obtain ⟨_, _, hleft, hright, hmeet, _⟩ := hcut m
  have hlcut : C.left m ≤ K.physicalRight (K.cutPair m).1 := by
    rw [← hleft]
    exact (hpieces (K.cutPair m).1).1.le
  have hcutr : K.physicalLeft (K.cutPair m).2 ≤ C.right m := by
    rw [← hright]
    exact (hpieces (K.cutPair m).2).1.le
  have hlcut' : C.left m ≤ K.physicalLeft (K.cutPair m).2 := by
    simpa only [hmeet] using hlcut
  have hcutr' : K.physicalRight (K.cutPair m).1 ≤ C.right m := by
    simpa only [hmeet] using hcutr
  rcases hi with rfl | rfl
  · intro x hx
    exact ⟨by simpa only [hleft] using hx.1, hx.2.trans hcutr'⟩
  · intro x hx
    exact ⟨hlcut'.trans hx.1, by simpa only [hright] using hx.2⟩

/-- Exact Through04 data give true ordinary root collars for the same
physical profile.  The positive side and its linear slope floor are proved,
and all costs keep their physical and canonical indices explicit. -/
theorem n06_reference_root_division_collar
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {R : ReturnEquationData S}
    {L : ReturnCorrectionData S} {K : CanonicalData S}
    {base loss : ℕ} {ε : ℝ}
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (h : NonlinearPropertiesThrough04 D T S C R L K base loss ε) :
    ∃ B c A M : ℝ, 1 ≤ B ∧ 0 < c ∧ 0 < A ∧ 0 < M ∧
      ∀ m, ∃ j : ℕ, Ioo (C.left m) (C.right m) ⊆ D.cells j ∧
        ∀ i, i = (K.cutPair m).1 ∨ i = (K.cutPair m).2 →
          ∀ r ∈ Icc (K.physicalLeft i) (K.physicalRight i), deriv D.w r = 0 →
          let δ := c / n06ReferenceRootCollarCost D T K A M i j
          0 < δ ∧ δ ≤ 1 ∧ δ ≤ D.a / 2 ∧
            ∃ ι : ℝ, ∃ g : ℝ → ℝ,
              (ι = 1 ∨ ι = -1) ∧ ContDiff ℝ ∞ g ∧
              g 0 = |deriv (deriv D.w) r| ∧
              (∀ t : ℝ, -deriv D.w (r + ι * t) = t * g t) ∧
              (∀ t ∈ Icc (-δ) δ,
                δ ≤ g t ∧ δ ≤ D.w (r + ι * t) ∧ r + ι * t ∈ radialCore D ∧
                  N06ScalarJetTwoBound g t B ∧
                  ∀ k : ℕ, k ≤ 4 → |iteratedDeriv k D.w (r + ι * t)| ≤ B) ∧
              ∀ t ∈ Ico (-δ) 0,
                0 < deriv D.w (r + ι * t) ∧ δ * (-t) ≤ deriv D.w (r + ι * t) := by
  obtain ⟨c0, A0, M, hc0, hA0, hM, hcurvature⟩ :=
    n06_referenceNegative_root_curvature_lower hT hS h
  obtain ⟨caps, hcaps⟩ := h.1.1.1.1.1
  have hgeom : RadialProfileGeometry D := hcaps.1
  have hcaps0 : 0 < caps 0 := hcaps.2.2.1 0
  obtain ⟨B, hB, hfour⟩ := n06_reference_profile_four_bound hgeom.2.2.1.1
  have hBp : 0 < B := zero_lt_one.trans_le hB
  let A : ℝ := max A0 (caps 0)
  have hA : 0 < A := hA0.trans_le (le_max_left _ _)
  let c : ℝ := min 1 (min (D.a / 2)
    (min (c0 / (2 * B)) ((caps 0)⁻¹ / (2 * B))))
  have hc : 0 < c := lt_min zero_lt_one (lt_min (half_pos hgeom.1)
    (lt_min (div_pos hc0 (mul_pos (by norm_num) hBp))
      (div_pos (inv_pos.mpr hcaps0) (mul_pos (by norm_num) hBp))))
  have hc1 : c ≤ 1 := min_le_left _ _
  have hca : c ≤ D.a / 2 := (min_le_right _ _).trans (min_le_left _ _)
  have hcr : c ≤ c0 / (2 * B) :=
    ((min_le_right _ _).trans (min_le_right _ _)).trans (min_le_left _ _)
  have hcw : c ≤ (caps 0)⁻¹ / (2 * B) :=
    ((min_le_right _ _).trans (min_le_right _ _)).trans (min_le_right _ _)
  have hcBr : 2 * B * c ≤ c0 := by
    have he := (le_div_iff₀ (mul_pos (by norm_num : (0 : ℝ) < 2) hBp)).mp hcr
    nlinarith only [he]
  have hcBw : 2 * B * c ≤ (caps 0)⁻¹ := by
    have he := (le_div_iff₀ (mul_pos (by norm_num : (0 : ℝ) < 2) hBp)).mp hcw
    nlinarith only [he]
  refine ⟨B, c, A, M, hB, hc, hA, hM, fun m => ?_⟩
  obtain ⟨j, hcell, hrootbound⟩ := hcurvature m
  refine ⟨j, hcell, fun i hi r hr hroot => ?_⟩
  let k : ℝ := 1 + M * T.E0 (T.sample (K.cell i)) ^ M
  let E : ℝ := radialE (D.cellIndex j)
  let d : ℝ := n06ReferenceRootCollarCost D T K A M i j
  let δ : ℝ := c / d
  have hE : 1 ≤ E := Real.one_le_exp_iff.mpr (Radial.radialQ_nonneg _)
  have hEp : 0 < E := zero_lt_one.trans_le hE
  have hE0 : 0 < T.E0 (T.sample (K.cell i)) :=
    (hT.2.1 _ (spaces_trace_sample_mem ⟨caps, hcaps⟩ hT (K.cell i))).2.2.1
  have hk : 1 ≤ k := by
    have he := (mul_pos hM (Real.rpow_pos_of_pos hE0 M)).le
    dsimp only [k]
    linarith only [he]
  have hEA : 1 ≤ E ^ A := Real.one_le_rpow hE hA.le
  have hd1 : 1 ≤ d := one_le_mul_of_one_le_of_one_le
    (show 1 ≤ k ^ 12 from one_le_pow₀ hk) (show 1 ≤ (E ^ A) ^ 19 from one_le_pow₀ hEA)
  have hdp : 0 < d := zero_lt_one.trans_le hd1
  have hδ : 0 < δ := div_pos hc hdp
  have hδc : δ ≤ c := by
    apply (div_le_iff₀ hdp).mpr
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hd1 hc.le
  have hδ1 : δ ≤ 1 := hδc.trans hc1
  have hδa : δ ≤ D.a / 2 := hδc.trans hca
  have hdroot : k ^ 12 * (E ^ A0) ^ 18 ≤ d := by
    change k ^ 12 * (E ^ A0) ^ 18 ≤ k ^ 12 * (E ^ A) ^ 19
    apply mul_le_mul_of_nonneg_left ?_ (pow_nonneg (zero_le_one.trans hk) _)
    exact (pow_le_pow_left₀ (Real.rpow_nonneg hEp.le _)
      (Real.rpow_le_rpow_of_exponent_le hE (le_max_left _ _)) 18).trans
        (pow_le_pow_right₀ hEA (by norm_num : 18 ≤ 19))
  have hdcaps : E ^ caps 0 ≤ d := by
    calc
      E ^ caps 0 ≤ E ^ A :=
        Real.rpow_le_rpow_of_exponent_le hE (le_max_right _ _)
      _ ≤ (E ^ A) ^ 19 := le_self_pow₀ hEA (by norm_num : (19 : ℕ) ≠ 0)
      _ ≤ k ^ 12 * (E ^ A) ^ 19 := by
        simpa only [one_mul] using mul_le_mul_of_nonneg_right
          (show 1 ≤ k ^ 12 from one_le_pow₀ hk) (pow_nonneg (zero_le_one.trans hEA) _)
  have hδcurv : 2 * B * δ ≤ |deriv (deriv D.w) r| := by
    calc
      2 * B * δ = (2 * B * c) / d := by dsimp only [δ]; ring
      _ ≤ c0 / d := div_le_div_of_nonneg_right hcBr hdp.le
      _ ≤ c0 / (k ^ 12 * (E ^ A0) ^ 18) :=
        div_le_div_of_nonneg_left hc0.le
          (mul_pos (pow_pos (zero_lt_one.trans_le hk) _)
            (pow_pos (Real.rpow_pos_of_pos hEp _) _)) hdroot
      _ ≤ |deriv (deriv D.w) r| := hrootbound i hi r hr hroot
  have hδheight : 2 * B * δ ≤ D.w r := by
    calc
      2 * B * δ = (2 * B * c) / d := by dsimp only [δ]; ring
      _ ≤ (caps 0)⁻¹ / d := div_le_div_of_nonneg_right hcBw hdp.le
      _ ≤ (caps 0)⁻¹ / E ^ caps 0 :=
        div_le_div_of_nonneg_left (inv_nonneg.mpr hcaps0.le)
          (Real.rpow_pos_of_pos hEp _) hdcaps
      _ = (caps 0 * E ^ caps 0)⁻¹ := by
        rw [div_eq_mul_inv, mul_inv_rev, mul_comm]
      _ ≤ D.w r := n06_profileCell_closed_interval_lower hcaps
        (h.1.1.1.2.2.2.1.1 m).2.1 hcell (n06_rootCollar_cutHalf_closed_subset h m hi hr)
  have hcore : r ∈ radialCore D := n06_cutPiece_closed_subset h m hi hr
  have hlocal (n : ℕ) (hn : n ≤ 4) (y : ℝ) (hy : y ∈ Icc (r - 1) (r + 1)) :
      |iteratedDeriv n D.w y| ≤ B :=
    hfour n hn y ⟨by linarith only [hcore.1, hy.1], by linarith only [hcore.2, hy.2]⟩
  obtain ⟨ι, g, hι, hg, hg0, hfactor, hgbound, hpositive⟩ :=
    n06_root_division_collar_of_profile_bounds hgeom.2.2.1.1
      hroot hB hδ hδ1 hδcurv hδheight hlocal
  refine ⟨hδ, hδ1, hδa, ι, g, hι, hg, hg0, hfactor, ?_, hpositive⟩
  intro t ht
  obtain ⟨hgt, hwt, hgjet, hwjet⟩ := hgbound t ht
  refine ⟨hgt, hwt, ?_, hgjet, hwjet⟩
  have hwpos : 0 < D.w (r + ι * t) := hδ.trans_le hwt
  by_contra hout
  have houtside : r + ι * t ≤ D.a ∨ D.b ≤ r + ι * t := by
    simpa only [radialCore, mem_Ioo, not_and_or, not_lt] using hout
  exact hwpos.ne' (hgeom.2.2.1.2 _ houtside)

end ContinuousFlexibility.Statements
