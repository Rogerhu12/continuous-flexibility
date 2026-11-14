module

public import ContinuousFlexibility.Analysis.N01OpticalRootDivision
public import ContinuousFlexibility.Analysis.N01ReturnMargins
public import ContinuousFlexibility.Analysis.ActualNegativeLengthRadialBounds
public import ContinuousFlexibility.Analysis.ActualNegativeHostMaterialSamples

/-!
# The actual optical root factor on an entire half component

The smooth division is selected once for the whole component. The raw
optical lower bound and the distance from the cut to the opposite root
then keep that same factor positive on the entire closed optical half.
Both its ordinary jets and its reciprocal value are measured at the
original sample stored by that half. No chosen root-model radius occurs.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set
open ContinuousFlexibility.Statements
open scoped ContDiff

private theorem dividedFactor_lower_on_prefix {F g : ℝ → ℝ} {L d κ : ℝ}
    (hd : 0 < d) (hdL : d < L) (hκ : 0 < κ) (hg : Continuous g)
    (hfactor : ∀ t ∈ Icc (0 : ℝ) L, F t = t * g t)
    (hlower : ∀ t ∈ Ioo (0 : ℝ) L, κ * min t (L - t) ≤ F t) :
    ∀ t ∈ Icc (0 : ℝ) d, κ * ((L - d) / L) ≤ g t := by
  have hL : 0 < L := hd.trans hdL
  have hgap : 0 < L - d := sub_pos.mpr hdL
  have hfrac0 : 0 ≤ (L - d) / L := (div_pos hgap hL).le
  have hfrac1 : (L - d) / L ≤ 1 := (div_le_one hL).mpr (by linarith only [hd])
  have hinner (t : ℝ) (ht : t ∈ Ioo (0 : ℝ) d) :
      κ * ((L - d) / L) ≤ g t := by
    have htL : t < L := ht.2.trans hdL
    have hmin : ((L - d) / L) * t ≤ min t (L - t) := by
      apply le_min
      · simpa only [one_mul] using mul_le_mul_of_nonneg_right hfrac1 ht.1.le
      · calc
          ((L - d) / L) * t ≤ ((L - d) / L) * L :=
            mul_le_mul_of_nonneg_left htL.le hfrac0
          _ = L - d := div_mul_cancel₀ _ hL.ne'
          _ ≤ L - t := by linarith only [ht.2]
    apply le_of_mul_le_mul_left (a := t) _ ht.1
    calc
      t * (κ * ((L - d) / L)) = κ * (((L - d) / L) * t) := by ring
      _ ≤ κ * min t (L - t) := mul_le_mul_of_nonneg_left hmin hκ.le
      _ ≤ F t := hlower t ⟨ht.1, htL⟩
      _ = t * g t := hfactor t ⟨ht.1.le, htL.le⟩
  intro t ht
  exact le_on_closure hinner continuousOn_const hg.continuousOn
    (by simpa only [closure_Ioo hd.ne] using ht)

/-- The opposite half width, rather than a local model radius, controls
the reciprocal of the actual normalized optical factor. -/
theorem normalizedOpticalRootDivision_inverse_on_half
    {w g : ℝ → ℝ} {l h c κ : ℝ}
    (hlc : l < c) (hch : c < h) (hκ : 0 < κ) (rightEnd : Bool)
    (hg : Continuous g)
    (hfactor : ∀ t ∈ Icc (0 : ℝ) (h - l),
      n01aOpticalRadicand w (inwardComponentPoint l h rightEnd t) = t * g t)
    (hoptical : ∀ x ∈ Ioo l h,
      κ * min (x - l) (h - x) ≤ n01aOpticalRadicand w x) :
    ∀ t ∈ Icc (0 : ℝ) (if rightEnd then h - c else c - l),
      0 < g t ∧ (g t)⁻¹ ≤
        (h - l) * κ⁻¹ * (if rightEnd then c - l else h - c)⁻¹ := by
  let d : ℝ := if rightEnd then h - c else c - l
  have hd : 0 < d := by
    cases rightEnd <;> simp only [d, Bool.false_eq_true, ↓reduceIte]
    · exact sub_pos.mpr hlc
    · exact sub_pos.mpr hch
  have hdL : d < h - l := by
    cases rightEnd <;> simp only [d, Bool.false_eq_true, ↓reduceIte]
      <;> linarith only [hlc, hch]
  have hL : 0 < h - l := hd.trans hdL
  have hraw (t : ℝ) (ht : t ∈ Ioo (0 : ℝ) (h - l)) :
      κ * min t (h - l - t) ≤
        n01aOpticalRadicand w (inwardComponentPoint l h rightEnd t) := by
    have hx : inwardComponentPoint l h rightEnd t ∈ Ioo l h := by
      cases rightEnd <;> simp only [inwardComponentPoint, Bool.false_eq_true, ↓reduceIte]
        <;> constructor <;> linarith only [ht.1, ht.2]
    have he : min (inwardComponentPoint l h rightEnd t - l)
        (h - inwardComponentPoint l h rightEnd t) = min t (h - l - t) := by
      cases rightEnd
      · simp only [inwardComponentPoint, Bool.false_eq_true, ↓reduceIte]
        congr 1 <;> ring
      · simp only [inwardComponentPoint, ↓reduceIte]
        rw [min_comm]
        congr 1 <;> ring
    simpa only [he] using hoptical (inwardComponentPoint l h rightEnd t) hx
  have hbound := dividedFactor_lower_on_prefix hd hdL hκ hg hfactor hraw
  have hlo : 0 < κ * ((h - l - d) / (h - l)) :=
    mul_pos hκ (div_pos (sub_pos.mpr hdL) hL)
  have hopposite : h - l - d = (if rightEnd then c - l else h - c) := by
    cases rightEnd <;> simp only [d, Bool.false_eq_true, ↓reduceIte] <;> ring
  intro t ht
  have ht' : t ∈ Icc (0 : ℝ) d := ht
  refine ⟨hlo.trans_le (hbound t ht'), ?_⟩
  calc
    (g t)⁻¹ ≤ (κ * ((h - l - d) / (h - l)))⁻¹ := inv_anti₀ hlo (hbound t ht')
    _ = (h - l) * κ⁻¹ * (if rightEnd then c - l else h - c)⁻¹ := by
      rw [mul_inv_rev, inv_div, div_eq_mul_inv, hopposite]
      ring

/-- Either physical half-width can be paid at either stored half sample
of the same component. The genuine return-margin host is only an input
to the already proved radial bound and is never identified with K.cell. -/
theorem n04bActualTypedAtlas_negative_allHalf_inverse_material
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {R : ReturnEquationData S}
    {L : ReturnCorrectionData S} {base loss : ℕ} {ε : ℝ}
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (hN : NonlinearPropertiesThrough03 D T S C R L base loss ε)
    (hfield : N04bFieldRegularity D S C L base ε) (e : ℕ ≃ N04PieceIndex D) :
    let K := n04bActualTypedAtlas hT hS hN hfield e
    let cut := n04bActualReferenceCut hN
    ∃ B A : ℝ, 0 < B ∧ 0 ≤ A ∧ ∀ k m side, e k = .inl (m, side) →
      ∀ other : Bool,
        (n04bNegativeRight C cut (m, other) - n04bNegativeLeft C cut (m, other))⁻¹ ≤
          B * T.E0 (T.sample (K.cell k)) ^ A := by
  dsimp only
  obtain ⟨B, A, hB, hA, hradial⟩ := n04b_actual_negative_radial_length_bounds hN
  obtain ⟨K₀, P₀, hK₀, hP₀, hpower⟩ :=
    materialSample_radialE_power_bound hT hN.1.1.1.1 (R := A) hA
  obtain ⟨K₁, P₁, hK₁, hP₁, hsample⟩ :=
    n04bActualTypedAtlas_negative_host_sample_E0_power hT hS hN hfield e P₀ hP₀
  refine ⟨B * K₀ * K₁, P₁, mul_pos (mul_pos hB hK₀) hK₁, hP₁, ?_⟩
  intro k m side hk other
  obtain ⟨j, hhost, hwidth⟩ := hradial m
  calc
    _ ≤ B * radialE (D.cellIndex j) ^ A := (hwidth other).1
    _ ≤ B * (K₀ * T.E0 (T.sample j) ^ P₀) :=
      mul_le_mul_of_nonneg_left (hpower j) hB.le
    _ ≤ B * (K₀ * (K₁ * T.E0 (T.sample ((n04bActualTypedAtlas hT hS hN hfield e).cell k)) ^ P₁)) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left (hsample k m side hk j hhost) hK₀.le) hB.le
    _ = _ := by ring

/-- The same selected smooth factor has all-order jets on the full
component and a reciprocal bound on its true optical half. The raw
optical inequality is explicit and belongs to the same actual witness. -/
theorem n04bActualTypedAtlas_opticalRootDivision_half_material
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {R : ReturnEquationData S}
    {L : ReturnCorrectionData S} {base loss : ℕ} {ε K₀ : ℝ}
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (hN : NonlinearPropertiesThrough03 D T S C R L base loss ε)
    (hfield : N04bFieldRegularity D S C L base ε) (e : ℕ ≃ N04PieceIndex D)
    (hK₀ : 0 < K₀) :
    let K := n04bActualTypedAtlas hT hS hN hfield e
    let cut := n04bActualReferenceCut hN
    ∃ A P : ℕ → ℝ, (∀ n, 0 < A n) ∧ (∀ n, 0 ≤ P n) ∧
      ∃ B Q : ℝ, 0 < B ∧ 0 ≤ Q ∧
      ∀ k m side, e k = .inl (m, side) →
      ∀ j, Ioo (C.left m) (C.right m) ⊆ D.cells j →
      (∀ x ∈ Ioo (C.left m) (C.right m),
        K₀⁻¹ * T.E0 (T.sample j) ^ (-K₀) *
          min (x - C.left m) (C.right m - x) ≤ -deriv D.w x / (x * D.w x)) →
      ∃ g : ℝ → ℝ, ContDiff ℝ ∞ g ∧
        (∀ t ∈ Icc (0 : ℝ) (C.right m - C.left m),
          n01aOpticalRadicand D.w
            (inwardComponentPoint (C.left m) (C.right m) side t) = t * g t) ∧
        (∀ n t, t ∈ Icc (0 : ℝ) (C.right m - C.left m) →
          |iteratedDeriv n g t| ≤ A n * T.E0 (T.sample (K.cell k)) ^ P n) ∧
        ∀ t ∈ Icc (0 : ℝ)
            (n04bNegativeRight C cut (m, side) - n04bNegativeLeft C cut (m, side)),
          0 < g t ∧ (g t)⁻¹ ≤ B * T.E0 (T.sample (K.cell k)) ^ Q := by
  classical
  dsimp only
  let K := n04bActualTypedAtlas hT hS hN hfield e
  let cut := n04bActualReferenceCut hN
  obtain ⟨Ag, Pg, hAg, hPg, hdivision⟩ :=
    exists_normalizedOpticalRootDivision_material_family hN.1.1.1.1 hT
  choose Cs Ps hCs hPs hsample using fun n =>
    n04bActualTypedAtlas_negative_host_sample_E0_power hT hS hN hfield e (Pg n) (hPg n)
  obtain ⟨Bo, Po, hBo, hPo, hopticalCost⟩ :=
    n04bActualTypedAtlas_negative_host_sample_E0_power hT hS hN hfield e K₀ hK₀.le
  obtain ⟨Bw, Pw, hBw, hPw, hwidth⟩ :=
    n04bActualTypedAtlas_negative_allHalf_inverse_material hT hS hN hfield e
  let W := D.b - D.a
  have hW : 0 < W := sub_pos.mpr (n04b_profileGeometry_of_through03 hN).2.1
  refine ⟨(fun n => Ag n * Cs n), Ps, (fun n => mul_pos (hAg n) (hCs n)), hPs,
    W * (K₀ * Bo) * Bw, Po + Pw,
    mul_pos (mul_pos hW (mul_pos hK₀ hBo)) hBw, add_nonneg hPo hPw, ?_⟩
  intro k m side hk j hhost hoptical
  have hcomp := n01Properties_negativeRadialComponent hN.1.1 m
  obtain ⟨g, hg, hfactor, hjets⟩ :=
    hdivision (C.left m) (C.right m) j hcomp hhost side
  refine ⟨g, hg, hfactor, ?_, ?_⟩
  · intro n t ht
    exact (hjets n t ht).trans
      ((mul_le_mul_of_nonneg_left (hsample n k m side hk j hhost) (hAg n).le).trans_eq
        (by ring))
  let E := T.E0 (T.sample (K.cell k))
  have hE : 0 < E := (hT.2.1 _ (materialSample_mem_interval hN.1.1.1.1 hT (K.cell k))).2.2.1
  have hEj : 0 < T.E0 (T.sample j) :=
    (hT.2.1 _ (materialSample_mem_interval hN.1.1.1.1 hT j)).2.2.1
  let κ := K₀⁻¹ * T.E0 (T.sample j) ^ (-K₀)
  have hκ : 0 < κ := mul_pos (inv_pos.mpr hK₀) (Real.rpow_pos_of_pos hEj _)
  have hκinv : κ⁻¹ ≤ (K₀ * Bo) * E ^ Po := by
    dsimp only [κ]
    rw [Real.rpow_neg hEj.le, mul_inv_rev, inv_inv, inv_inv]
    calc
      _ ≤ K₀ * (Bo * E ^ Po) := by
        simpa only [mul_comm] using
          mul_le_mul_of_nonneg_left (hopticalCost k m side hk j hhost) hK₀.le
      _ = _ := by ring
  have hc := n04bActualReferenceCut_mem hN m
  have hinverse := normalizedOpticalRootDivision_inverse_on_half hc.1 hc.2 hκ side
    hg.continuous hfactor hoptical
  have hwidthOther : (if side then cut m - C.left m else C.right m - cut m)⁻¹ ≤
      Bw * E ^ Pw := by
    have hh := hwidth k m side hk (!side)
    cases side <;> simpa only [n04bNegativeLeft, n04bNegativeRight,
      Bool.false_eq_true, Bool.not_false, Bool.not_true, ↓reduceIte] using hh
  intro t ht
  have ht' : t ∈ Icc (0 : ℝ) (if side then C.right m - cut m else cut m - C.left m) := by
    cases side <;> simpa only [n04bNegativeLeft, n04bNegativeRight,
      Bool.false_eq_true, ↓reduceIte] using ht
  have h := hinverse t ht'
  have hother : 0 < (if side then cut m - C.left m else C.right m - cut m) := by
    cases side <;> simp only [Bool.false_eq_true, ↓reduceIte]
    · exact sub_pos.mpr hc.2
    · exact sub_pos.mpr hc.1
  have hspan : C.right m - C.left m ≤ W := by
    dsimp only [W]
    linarith only [hcomp.1, hcomp.2.2.1]
  refine ⟨h.1, h.2.trans ?_⟩
  calc
    _ ≤ (W * ((K₀ * Bo) * E ^ Po)) * (Bw * E ^ Pw) :=
      mul_le_mul (mul_le_mul hspan hκinv (inv_pos.mpr hκ).le hW.le)
        hwidthOther (inv_pos.mpr hother).le
        (mul_nonneg hW.le (mul_nonneg (mul_pos hK₀ hBo).le (Real.rpow_nonneg hE.le _)))
    _ = (W * (K₀ * Bo) * Bw) * E ^ (Po + Pw) := by
      rw [Real.rpow_add hE]
      ring

end ContinuousFlexibility.Analysis
