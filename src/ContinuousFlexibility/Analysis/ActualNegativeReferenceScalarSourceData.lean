import ContinuousFlexibility.Analysis.ActualNegativeReferenceHeightProfileJets
import ContinuousFlexibility.Analysis.ActualNegativeLengthMaterialBounds
import ContinuousFlexibility.Analysis.N07aCanonicalUnitCoefficient

/-!
# The original negative reference inverse and scalar source

The two scalar families are literal unit-coordinate slices of the same
stored atlas. Canonical affine rescaling costs only positive powers of
the actual half length. All estimates retain its original material sample.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set ContinuousFlexibility.Statements CanonicalGeometry
open scoped ContDiff BigOperators Topology

/-- Actual negative inverse/source data for the scalar-column constructor.
The old enumeration is fixed before the material scale and all orders.
The optical host is supplied for the same component, independently of
its stored half sample. No zeroth inverse-coordinate bound is required. -/
theorem n04bActualTypedAtlas_negative_scalarSource_material_data
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {R : ReturnEquationData S}
    {L : ReturnCorrectionData S} {base loss : ℕ} {ε K₀ : ℝ}
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (hN : NonlinearPropertiesThrough03 D T S C R L base loss ε)
    (hfield : N04bFieldRegularity D S C L base ε)
    (e₀ : ℕ ≃ N04PieceIndex D) (hK₀ : 0 < K₀)
    (hoptical : ∀ m, ∃ j, Ioo (C.left m) (C.right m) ⊆ D.cells j ∧
      ∀ r ∈ Ioo (C.left m) (C.right m),
        K₀⁻¹ * T.E0 (T.sample j) ^ (-K₀) *
          min (r - C.left m) (C.right m - r) ≤ -deriv D.w r / (r * D.w r)) :
    let K := n04bActualTypedAtlas hT hS hN hfield e₀
    let piece := fun i : ℕ × Bool => e₀.symm (.inl i)
    let X := fun (i : ℕ × Bool) (t : ℝ) =>
      (K.inverseChart (C.referenceState, 0) (piece i)
        (canonicalUnitPoint K (piece i) (t, 0))).1
    let F := fun (i : ℕ × Bool) (t : ℝ) =>
      atom D T S C L K (C.referenceState, 0) (piece i) .sourceFactor (t, 0)
    ∃ C0 : ℝ, 1 ≤ C0 ∧ (∀ j, 1 ≤ C0 * T.E0 (T.sample j)) ∧
      (∀ i, ContDiffOn ℝ ∞ (X i) (Ioo (0 : ℝ) 1) ∧
        ContDiffOn ℝ ∞ (F i) (Ioo (0 : ℝ) 1) ∧
        (∀ x ∈ Ioo (0 : ℝ) 1, X i x ∈ radialCore D) ∧
        ∀ p ∈ unitStrip,
          K.inverseChart (C.referenceState, 0) (piece i)
            (canonicalUnitPoint K (piece i) p) = (X i p.1, p.2) ∧
          atom D T S C L K (C.referenceState, 0) (piece i) .sourceFactor p = F i p.1) ∧
      ∀ N : ℕ, ∃ A : ℝ, 1 ≤ A ∧ ∀ i x,
        x ∈ Ioo (0 : ℝ) 1 → ∀ q, q ≤ N →
          |iteratedDeriv q (F i) x| ≤ A * (C0 * T.E0 (T.sample (K.cell (piece i)))) ^ A ∧
          (1 ≤ q → |iteratedDeriv q (X i) x| ≤
            A * (C0 * T.E0 (T.sample (K.cell (piece i)))) ^ A) := by
  classical
  dsimp only
  let K := n04bActualTypedAtlas hT hS hN hfield e₀
  let piece : ℕ × Bool → ℕ := fun i => e₀.symm (.inl i)
  let X : (ℕ × Bool) → ℝ → ℝ := fun i t =>
    (K.inverseChart (C.referenceState, 0) (piece i)
      (canonicalUnitPoint K (piece i) (t, 0))).1
  let F : (ℕ × Bool) → ℝ → ℝ := fun i t =>
    atom D T S C L K (C.referenceState, 0) (piece i) .sourceFactor (t, 0)
  let ρ : ℕ × Bool → ℝ := fun i => K.right (piece i) - K.left (piece i)
  let a : (ℕ × Bool) → ℝ → ℝ := fun i t => K.left (piece i) + ρ i * t
  let χ : (ℕ × Bool) → ℝ → ℝ := fun i ξ =>
    (K.inverseChart (C.referenceState, 0) (piece i) (ξ, 0)).1
  let H : (ℕ × Bool) → ℝ → ℝ := fun i r => K.height (C.referenceState, 0) (piece i) (r, 0)
  let g : (ℕ × Bool) → ℝ → ℝ := fun i ξ => H i (χ i ξ) ^ 3 * D.w (χ i ξ)
  let cut := n04bActualReferenceCut hN
  let I : (ℕ × Bool) → Set ℝ := fun i =>
    Ioo (n04bNegativeLeft C cut i) (n04bNegativeRight C cut i)
  let J : (ℕ × Bool) → Set ℝ := fun i => Ioo (K.left (piece i)) (K.right (piece i))
  have hD := n04b_profileGeometry_of_through03 hN
  have hi (i : ℕ × Bool) : e₀ (piece i) = .inl i := e₀.apply_symm_apply _
  have ha (i : ℕ × Bool) : ContDiff ℝ ∞ (a i) :=
    contDiff_const.add (contDiff_const.mul contDiff_id)
  have hmeta (i : ℕ × Bool) : 0 < ρ i ∧ MapsTo (a i) (Ioo (0 : ℝ) 1) (J i) := by
    have hl : K.left (piece i) = 0 := by
      simp only [K, n04bActualTypedAtlas, n04bTypedAtlasData_left]
    have hr : K.right (piece i) = n04bRootCutRadius (C.travel i.1) := by
      simp only [K, n04bActualTypedAtlas, n04bTypedAtlasData_right, hi]
    have hρ : 0 < ρ i := by
      rw [show ρ i = K.right (piece i) - K.left (piece i) from rfl, hl, hr, sub_zero]
      exact n04bRootCutRadius_pos (n04b_referenceTravel_pos hD hN.1.1.2.2.2.1 i.1)
    refine ⟨hρ, ?_⟩
    intro t ht
    change K.left (piece i) < K.left (piece i) + ρ i * t ∧
      K.left (piece i) + ρ i * t < K.right (piece i)
    have hh : ρ i * t < ρ i := (mul_lt_mul_of_pos_left ht.2 hρ).trans_eq (mul_one _)
    exact ⟨lt_add_of_pos_right _ (mul_pos hρ ht.1), by dsimp only [ρ] at hh; linarith only [hh]⟩
  have heq (i : ℕ × Bool) : EqOn (F i) (fun t => g i (a i t)) (Ioo (0 : ℝ) 1) := by
    intro t ht
    have hh := (n04Coordinates_actual_reference_negative_geometry_fields
      hT hS hN hfield e₀ i.1 i.2).2 (a i t, 0) ⟨(hmeta i).2 ht, mem_univ _⟩
    exact hh.2.2.1
  have hdata (i : ℕ × Bool) : ContDiffOn ℝ ∞ (X i) (Ioo (0 : ℝ) 1) ∧
      ContDiffOn ℝ ∞ (F i) (Ioo (0 : ℝ) 1) ∧
      (∀ x ∈ Ioo (0 : ℝ) 1, X i x ∈ radialCore D) ∧
      ∀ p ∈ unitStrip,
        K.inverseChart (C.referenceState, 0) (piece i)
          (canonicalUnitPoint K (piece i) p) = (X i p.1, p.2) ∧
        atom D T S C L K (C.referenceState, 0) (piece i) .sourceFactor p = F i p.1 := by
    have hs := n04Coordinates_actual_reference_negative_scalar_inverse hT hS hN hfield e₀ i.1 i.2
    have hχ : ContDiffOn ℝ ∞ (χ i) (J i) := hs.2.2.1
    have hH : ContDiffOn ℝ ∞ (H i) (I i) := hs.2.1
    have hm : MapsTo (χ i) (J i) (I i) := hs.2.2.2.1
    have hg : ContDiffOn ℝ ∞ (g i) (J i) :=
      ((hH.pow 3).mul hD.2.2.1.1.contDiffOn).comp hχ hm
    refine ⟨hχ.comp (ha i).contDiffOn (hmeta i).2,
      (hg.comp (ha i).contDiffOn (hmeta i).2).congr (fun t ht => heq i ht), ?_, ?_⟩
    · intro x hx
      have hh := n04b_negativeHalf_subset (n04bActualReferenceCut_mem hN) i (hm ((hmeta i).2 hx))
      have hc := n01Properties_negativeRadialComponent hN.1.1 i.1
      exact ⟨hc.1.trans hh.1, hh.2.trans hc.2.2.1⟩
    · intro p hp
      have hh := (n04Coordinates_actual_reference_negative_geometry_fields
        hT hS hN hfield e₀ i.1 i.2).2 (a i p.1, p.2) ⟨(hmeta i).2 hp.1, mem_univ _⟩
      refine ⟨hh.1, ?_⟩
      exact hh.2.2.1.trans (heq i hp.1).symm
  obtain ⟨CH, hCH, hfloorH, hprofile⟩ :=
    n04bActualTypedAtlas_reference_half_heightProfile_material_jets hT hS hN hfield e₀ hK₀
  obtain ⟨CI, hCI, _, BI, hBI, hinverse⟩ :=
    n04bActualTypedAtlas_reference_half_inverse_material_jets hT hS hN hfield e₀ hK₀
  obtain ⟨BN, AN, hBN, hAN, hlength⟩ :=
    n04bActualTypedAtlas_negative_length_material_bounds hT hS hN hfield e₀
  let C0 : ℝ := CH + CI
  have hC0 : 1 ≤ C0 := by dsimp only [C0]; linarith only [hCH, hCI]
  have hCH0 : CH ≤ C0 := le_add_of_nonneg_right (zero_le_one.trans hCI)
  have hCI0 : CI ≤ C0 := le_add_of_nonneg_left (zero_le_one.trans hCH)
  have hfloor (j : ℕ) : 1 ≤ C0 * T.E0 (T.sample j) :=
    (hfloorH j).trans (mul_le_mul_of_nonneg_right hCH0
      (hT.2.1 _ (materialSample_mem_interval hN.1.1.1.1 hT j)).2.2.1.le)
  refine ⟨C0, hC0, hfloor, hdata, ?_⟩
  intro N
  obtain ⟨BH, hBH, hproduct⟩ := hprofile 3 false N
  let total : ℝ := ∑ q : Fin (N + 1), BI q.val
  have htotal : 0 ≤ total := Finset.sum_nonneg fun q _ => zero_le_one.trans (hBI q.val)
  let A : ℝ := 1 + BH + BN + AN + total
  have hA : 1 ≤ A := by dsimp only [A]; linarith only [hBH, hBN, hAN, htotal]
  have hBHA : BH ≤ A := by dsimp only [A]; linarith only [hBN, hAN, htotal]
  have hBNA : BN ≤ A := by dsimp only [A]; linarith only [hBH, hAN, htotal]
  have hANA : AN ≤ A := by dsimp only [A]; linarith only [hBH, hBN, htotal]
  have hBIA (q : ℕ) (hq : q ≤ N) : BI q ≤ A := by
    have hh : BI q ≤ total := Finset.single_le_sum (fun j _ => zero_le_one.trans (hBI j.val))
      (Finset.mem_univ (⟨q, by omega⟩ : Fin (N + 1)))
    dsimp only [A]
    linarith only [hh, hBH, hBN, hAN]
  let coefficient : ℝ := A ^ (N + 1)
  let exponent : ℝ := A * ((N + 1 : ℕ) : ℝ)
  have hc : 0 ≤ coefficient := pow_nonneg (zero_le_one.trans hA) _
  have he : 0 ≤ exponent := mul_nonneg (zero_le_one.trans hA) (Nat.cast_nonneg _)
  let B : ℝ := 1 + coefficient + exponent
  have hB : 1 ≤ B := by dsimp only [B]; linarith only [hc, he]
  have hcB : coefficient ≤ B := by dsimp only [B]; linarith only [he]
  have heB : exponent ≤ B := by dsimp only [B]; linarith only [hc]
  refine ⟨B, hB, ?_⟩
  intro i x hx q hq
  obtain ⟨j, hhost, hraw⟩ := hoptical i.1
  let E : ℝ := T.E0 (T.sample (K.cell (piece i)))
  let W : ℝ := C0 * E
  let M : ℝ := A * W ^ A
  have hE : 0 < E := (hT.2.1 _ (materialSample_mem_interval hN.1.1.1.1 hT (K.cell (piece i)))).2.2.1
  have hW : 1 ≤ W := hfloor (K.cell (piece i))
  have hEW : E ≤ W := by simpa only [one_mul] using mul_le_mul_of_nonneg_right hC0 hE.le
  have hM : 1 ≤ M := one_le_mul_of_one_le_of_one_le hA (Real.one_le_rpow hW (zero_le_one.trans hA))
  have hpack {c p V : ℝ} (hV : 0 ≤ V) (hVW : V ≤ W) (hp : 0 ≤ p)
      (hcA : c ≤ A) (hpA : p ≤ A) : c * V ^ p ≤ M :=
    mul_le_mul hcA ((Real.rpow_le_rpow hV hVW hp).trans
      (Real.rpow_le_rpow_of_exponent_le hW hpA)) (Real.rpow_nonneg hV _) (zero_le_one.trans hA)
  have hρM : ρ i ≤ M := ((hlength (piece i) i.1 i.2 (hi i)).2.2.2).trans
    (hpack hE.le hEW hAN hBNA hANA)
  have hfinal : M ^ (N + 1) ≤ B * W ^ B := by
    calc
      _ = coefficient * W ^ exponent := by
        dsimp only [M, coefficient, exponent]
        rw [mul_pow, ← Real.rpow_mul_natCast (zero_le_one.trans hW) A (N + 1)]
      _ ≤ _ := mul_le_mul hcB (Real.rpow_le_rpow_of_exponent_le hW heB)
        (Real.rpow_nonneg (zero_le_one.trans hW) _) (zero_le_one.trans hB)
  have hunit (f : ℝ → ℝ) (hf : |iteratedDeriv q f (a i x)| ≤ M) :
      |iteratedDeriv q (fun t => f (a i t)) x| ≤ B * W ^ B := by
    change |iteratedDeriv q (fun t => f (K.left (piece i) + ρ i * t)) x| ≤ _
    rw [n07a_iteratedDeriv_comp_affine, abs_mul, abs_pow, abs_of_pos (hmeta i).1]
    calc
      _ ≤ ρ i ^ q * M := mul_le_mul_of_nonneg_left hf (pow_nonneg (hmeta i).1.le _)
      _ ≤ M ^ q * M := mul_le_mul_of_nonneg_right
        (pow_le_pow_left₀ (hmeta i).1.le hρM q) (zero_le_one.trans hM)
      _ = M ^ (q + 1) := (pow_succ M q).symm
      _ ≤ M ^ (N + 1) := pow_le_pow_right₀ hM (by omega)
      _ ≤ _ := hfinal
  refine ⟨?_, ?_⟩
  · rw [(heq i).iteratedDeriv_of_isOpen isOpen_Ioo q hx]
    apply hunit (g i)
    have hb := (hproduct (piece i) i.1 i.2 (hi i) j hhost hraw).2
      (a i x) ((hmeta i).2 hx) q hq
    have hg : |iteratedDeriv q (g i) (a i x)| ≤ BH * (CH * E) ^ BH := by
      simpa only [Bool.false_eq_true, ↓reduceIte, Real.rpow_ofNat] using hb
    exact hg.trans (hpack (mul_nonneg (zero_le_one.trans hCH) hE.le)
      (mul_le_mul_of_nonneg_right hCH0 hE.le) (zero_le_one.trans hBH) hBHA hBHA)
  · intro hq1
    apply hunit (χ i)
    have hb := hinverse (piece i) i.1 i.2 (hi i) j hhost hraw
      (a i x) ((hmeta i).2 hx) (q - 1)
    rw [Nat.sub_add_cancel hq1] at hb
    exact hb.trans (hpack (mul_nonneg (zero_le_one.trans hCI) hE.le)
      (mul_le_mul_of_nonneg_right hCI0 hE.le) (zero_le_one.trans (hBI (q - 1)))
      (hBIA (q - 1) (by omega)) (hBIA (q - 1) (by omega)))

end ContinuousFlexibility.Analysis
