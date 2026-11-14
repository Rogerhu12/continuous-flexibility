module

public import ContinuousFlexibility.Analysis.ActualNegativeReferenceHeightProfileJets
public import ContinuousFlexibility.Analysis.ActualNegativeLengthMaterialBounds
public import ContinuousFlexibility.Analysis.WholeReferenceGaugeAtlasData
public import ContinuousFlexibility.Analysis.MaterialEnvelopeNormalization
public import ContinuousFlexibility.Analysis.LocalMixedProductBounds
public import ContinuousFlexibility.Analysis.N07aCanonicalUnitCoefficient
public import ContinuousFlexibility.Analysis.N08RadialFamilyMaterialJets

/-!
# Ten actual negative geometric atoms at the original sample

Only the material envelope is enlarged. The chart, inverse, height, true
optical radius, physical half and stored sample remain those of the same K.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter ContinuousFlexibility.Statements
open CanonicalGeometry
open scoped ContDiff Topology BigOperators

private def negativeGeometryScalar (l lam ρ : ℝ) (Y χ H w : ℝ → ℝ) : Atom → ℝ → ℝ
  | .chartRadial => fun x => Y (l + lam * x) / ρ
  | .inverseRadial => fun x => (χ (ρ * x) - l) / lam
  | .height => fun x => H (l + lam * x)
  | .heightInverse => fun x => (H (l + lam * x))⁻¹
  | .jacobian => fun x => H (l + lam * x) ^ (-2 : ℝ) * (w (l + lam * x))⁻¹
  | .jacobianInverse => fun x => H (l + lam * x) ^ 2 * w (l + lam * x)
  | .sourceFactor => fun x => H (χ (ρ * x)) ^ 3 * w (χ (ρ * x))
  | .sourceFactorInverse => fun x => H (χ (ρ * x)) ^ (-3 : ℝ) * (w (χ (ρ * x)))⁻¹
  | _ => fun _ => 0

private theorem negativeGeometry_affine_bound {M : ℝ} (hM : 1 ≤ M)
    (f : ℝ → ℝ) (d c x : ℝ) {s n : ℕ} (hn : n ≤ s) (hc : |c| ≤ M)
    (hf : |iteratedDeriv n f (d + c * x)| ≤ M) :
    |iteratedDeriv n (fun t => f (d + c * t)) x| ≤ M ^ (s + 2) := by
  rw [n07a_iteratedDeriv_comp_affine, abs_mul, abs_pow]
  calc
    _ ≤ M ^ n * M := mul_le_mul (pow_le_pow_left₀ (abs_nonneg _) hc n) hf
      (abs_nonneg _) (pow_nonneg (zero_le_one.trans hM) _)
    _ = M ^ (n + 1) := (pow_succ M n).symm
    _ ≤ _ := pow_le_pow_right₀ hM (by omega)

private theorem negativeGeometry_normalized_bound {M : ℝ} (hM : 1 ≤ M)
    (f : ℝ → ℝ) (d c a b x : ℝ) {s n : ℕ} (hn : n ≤ s)
    (hc : |c| ≤ M) (hb : |b⁻¹| ≤ M) (hzero : |(f (d + c * x) - a) / b| ≤ 1)
    (hf : ∀ j, 1 ≤ j → j ≤ s → |iteratedDeriv j f (d + c * x)| ≤ M) :
    |iteratedDeriv n (fun t => (f (d + c * t) - a) / b) x| ≤ M ^ (s + 2) := by
  by_cases hn0 : n = 0
  · subst n
    exact hzero.trans (one_le_pow₀ hM)
  have he : (fun t => (f (d + c * t) - a) / b) =
      fun t => (-a + f (d + c * t)) / b := by funext t; congr 1; ring
  rw [he, iteratedDeriv_div_const, iteratedDeriv_const_add (by omega : 0 < n),
    n07a_iteratedDeriv_comp_affine, div_eq_mul_inv, abs_mul, abs_mul, abs_pow]
  calc
    _ ≤ (M ^ n * M) * M := mul_le_mul
      (mul_le_mul (pow_le_pow_left₀ (abs_nonneg _) hc n) (hf n (by omega) hn)
        (abs_nonneg _) (pow_nonneg (zero_le_one.trans hM) _)) hb
      (abs_nonneg _) (mul_nonneg (pow_nonneg (zero_le_one.trans hM) _) (zero_le_one.trans hM))
    _ = M ^ (n + 2) := by rw [pow_add, pow_two]; ring
    _ ≤ _ := pow_le_pow_right₀ hM (by omega)

/-- Uniform spatial jets of all ten geometric atoms on every negative
piece of the same whole reference atlas. No final primitive estimate is
an input, and the actual optical host is not identified with K.cell. -/
theorem n04WholeReferenceGauge_negative_geometryReferenceJets_enlargedMaterialData
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {R : ReturnEquationData S}
    {L : ReturnCorrectionData S} {base loss : ℕ} {ε K₀ : ℝ}
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (hN : NonlinearPropertiesThrough03 D T S C R L base loss ε)
    (hfield : N04bFieldRegularity D S C L base ε)
    (e₀ : ℕ ≃ N04PieceIndex D) (hK₀ : 0 < K₀) :
    ∀ s : ℕ, ∃ BM : ℝ, 0 < BM ∧
    ∀ (e : ℕ ≃ N04WholePieceIndex D)
      (cell : N04PositiveComponent D.a D.b (deriv D.w) → ℕ)
      (ψ χ₀ : N04PositiveComponent D.a D.b (deriv D.w) → PolarPoint → PolarPoint)
      (h₀ : N04PositiveComponent D.a D.b (deriv D.w) → PolarPoint → ℝ)
      (τ σ : (AnnularState S × ℝ) → N04PositiveComponent D.a D.b (deriv D.w) → PolarPoint → PolarPoint)
      (Q : (AnnularState S × ℝ) → N04PositiveComponent D.a D.b (deriv D.w) → PolarPoint → ℝ) (N : Set ℝ),
      (∀ m, ∃ j, Ioo (C.left m) (C.right m) ⊆ D.cells j ∧
        ∀ r ∈ Ioo (C.left m) (C.right m),
          K₀⁻¹ * T.E0 (T.sample j) ^ (-K₀) * min (r - C.left m) (C.right m - r) ≤
            -deriv D.w r / (r * D.w r)) →
      let K := n04bActualTypedAtlas hT hS hN hfield e₀
      let V := n04WholeReferenceGaugeAtlasData C L K e cell ψ χ₀ h₀ τ σ Q N
      let U := enlargedMaterialData T
      ∀ m, V.positive m = false → ∀ v : Atom,
        (v = .chartRadial ∨ v = .chartAngleDefect ∨ v = .inverseRadial ∨
          v = .inverseAngleDefect ∨ v = .height ∨ v = .heightInverse ∨
          v = .jacobian ∨ v = .jacobianInverse ∨ v = .sourceFactor ∨ v = .sourceFactorInverse) →
        ∀ p ∈ unitStrip, ∀ a b : ℕ, a + b ≤ s →
          |mixedDerivative a b (atom D U S C L V (C.referenceState, 0) m v) p| ≤
            BM * U.E0 (U.sample (V.cell m)) ^ BM := by
  classical
  let K := n04bActualTypedAtlas hT hS hN hfield e₀
  let U := enlargedMaterialData T
  obtain ⟨CP, hCP, _, hproducts⟩ :=
    n04bActualTypedAtlas_reference_half_heightProfile_material_jets hT hS hN hfield e₀ hK₀
  obtain ⟨CH, hCH, _, hheight⟩ :=
    n04bActualTypedAtlas_reference_half_height_physical_power_material_jets hT hS hN hfield e₀ hK₀
  obtain ⟨CI, hCI, _, BI, hBI, hinverse⟩ :=
    n04bActualTypedAtlas_reference_half_inverse_material_jets hT hS hN hfield e₀ hK₀
  obtain ⟨BH, hBH, hh⟩ := hheight 1
  obtain ⟨BHi, hBHi, hhi⟩ := hheight (-1)
  obtain ⟨BN, AN, hBN, hAN, hlength⟩ := n04bActualTypedAtlas_negative_length_material_bounds hT hS hN hfield e₀
  let C0 : ℝ := CP + CH + CI
  have hC0 : 1 ≤ C0 := by dsimp only [C0]; linarith only [hCP, hCH, hCI]
  have hscales : CP ≤ C0 ∧ CH ≤ C0 ∧ CI ≤ C0 := by
    refine ⟨?_, ?_, ?_⟩ <;> dsimp only [C0] <;> linarith only [hCP, hCH, hCI]
  intro s
  obtain ⟨BJ, hBJ, hj⟩ := hproducts (-2) true s
  obtain ⟨BJi, hBJi, hji⟩ := hproducts 2 false s
  obtain ⟨BS, hBS, hs⟩ := hproducts 3 false s
  obtain ⟨BSi, hBSi, hsi⟩ := hproducts (-3) true s
  let total : ℝ := ∑ q : Fin (s + 1), (BH q.val + BHi q.val + BI q.val)
  have htotal : 0 ≤ total := Finset.sum_nonneg fun q _ =>
    add_nonneg (add_nonneg (zero_le_one.trans (hBH q.val)) (zero_le_one.trans (hBHi q.val)))
      (zero_le_one.trans (hBI q.val))
  let A : ℝ := 1 + BN + AN + BJ + BJi + BS + BSi + total
  have hA : 1 ≤ A := by dsimp only [A]; linarith only [hBN, hAN, hBJ, hBJi, hBS, hBSi, htotal]
  have hAparts : BN ≤ A ∧ AN ≤ A ∧ BJ ≤ A ∧ BJi ≤ A ∧ BS ≤ A ∧ BSi ≤ A := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> dsimp only [A] <;>
      linarith only [hBN, hAN, hBJ, hBJi, hBS, hBSi, htotal]
  have hprefix (q : ℕ) (hq : q ≤ s) : BH q ≤ A ∧ BHi q ≤ A ∧ BI q ≤ A := by
    have hsum : BH q + BHi q + BI q ≤ total := Finset.single_le_sum
      (fun t _ => add_nonneg (add_nonneg (zero_le_one.trans (hBH t.val))
        (zero_le_one.trans (hBHi t.val))) (zero_le_one.trans (hBI t.val)))
      (Finset.mem_univ (⟨q, by omega⟩ : Fin (s + 1)))
    refine ⟨?_, ?_, ?_⟩ <;> dsimp only [A] <;>
      linarith only [hsum, hBN, hAN, hBJ, hBJi, hBS, hBSi, hBH q, hBHi q, hBI q]
  let exponent : ℝ := A * ((s + 2 : ℕ) : ℝ)
  let coefficient : ℝ := A ^ (s + 2) * C0 ^ exponent
  obtain ⟨BM, hBM, hfinal⟩ := coefficientEnvelope_pack coefficient exponent
  refine ⟨BM, hBM, ?_⟩
  intro e cell ψ χ₀ h₀ τ σ Q N hoptical
  dsimp only
  let V := n04WholeReferenceGaugeAtlasData C L K e cell ψ χ₀ h₀ τ σ Q N
  intro m hm v hv p hp a b hab
  cases he : e m with
  | inr i =>
      have hpos : V.positive m = true := by
        simp only [V, n04WholeReferenceGaugeAtlasData, n04WholeCanonicalAtlasData,
          n04bWithInteriorDivision, n04WholePiecePositive, he]
      exact False.elim (Bool.false_ne_true (hpos.symm.trans hm).symm)
  | inl j =>
      let k := if j.2 then (K.cutPair j.1).2 else (K.cutPair j.1).1
      have hk : e₀ k = .inl j := by
        rcases j with ⟨m, side⟩
        cases side <;> simp only [K, k, n04bActualTypedAtlas, n04bTypedAtlasData_cutPair,
          Bool.false_eq_true, ite_false, ite_true, Equiv.apply_symm_apply]
      have hki : e₀.symm (.inl (j.1, j.2)) = k := by rw [← hk, e₀.symm_apply_apply]
      have hnegFields : V.left m = K.left k ∧ V.right m = K.right k ∧
          V.physicalLeft m = K.physicalLeft k ∧ V.physicalRight m = K.physicalRight k ∧
          physicalPieceOpen S V (C.referenceState, 0) m =
            physicalPieceOpen S K (C.referenceState, 0) k ∧
          V.cell m = K.cell k ∧ V.positive m = false ∧
          V.chart (C.referenceState, 0) m = K.chart (C.referenceState, 0) k ∧
          V.inverseChart (C.referenceState, 0) m = K.inverseChart (C.referenceState, 0) k ∧
          V.height (C.referenceState, 0) m = K.height (C.referenceState, 0) k ∧
          V.coefficients (C.referenceState, 0) m = K.coefficients (C.referenceState, 0) k ∧
          V.potential (C.referenceState, 0) m = K.potential (C.referenceState, 0) k :=
        n04WholeReferenceGaugeAtlasData_negative_fields
          C L K e cell ψ χ₀ h₀ τ σ Q N (C.referenceState, 0) m j he
      obtain ⟨hl, hr, hpl, hpr, _, hsample, _, hF, hG, hH, _, _⟩ := hnegFields
      let cut := n04bActualReferenceCut hN
      let l := n04bNegativeLeft C cut j
      let r := n04bNegativeRight C cut j
      let lam := r - l
      let ρ := n04bRootCutRadius (C.travel j.1)
      let Y := fun t : ℝ => (K.chart (C.referenceState, 0) k (t, 0)).1
      let H := fun t : ℝ => K.height (C.referenceState, 0) k (t, 0)
      let χ := fun t : ℝ => (K.inverseChart (C.referenceState, 0) k (t, 0)).1
      have hlK : K.left k = 0 := by simp only [K, n04bActualTypedAtlas, n04bTypedAtlasData_left]
      have hrK : K.right k = ρ := by simp only [K, n04bActualTypedAtlas, n04bTypedAtlasData_right, hk, ρ]
      have hplK : K.physicalLeft k = l := by change n04bReferenceTypedLeft C cut (e₀ k) = l; rw [hk]; rfl
      have hprK : K.physicalRight k = r := by change n04bReferenceTypedRight C cut (e₀ k) = r; rw [hk]; rfl
      have hlr : l < r := (n04b_negativeHalf_bounds hN.1.1.2.2.2.1 (n04bActualReferenceCut_mem hN) j).2.1
      have hlam : 0 < lam := sub_pos.mpr hlr
      have hρ : 0 < ρ := n04bRootCutRadius_pos
        (n04b_referenceTravel_pos (n04b_profileGeometry_of_through03 hN) hN.1.1.2.2.2.1 j.1)
      have hphys {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) : l + lam * x ∈ Ioo l r := by
        refine ⟨lt_add_of_pos_right l (mul_pos hlam hx.1), ?_⟩
        have ht := mul_lt_mul_of_pos_left hx.2 hlam
        dsimp only [lam] at ht ⊢
        linarith only [ht]
      have hcan {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) : ρ * x ∈ Ioo (K.left k) (K.right k) := by
        rw [hlK, hrK]
        exact ⟨mul_pos hρ hx.1, (mul_lt_mul_of_pos_left hx.2 hρ).trans_eq (mul_one ρ)⟩
      have hscalar := n04Coordinates_actual_reference_negative_scalar_inverse hT hS hN hfield e₀ j.1 j.2
      have hfields := n04Coordinates_actual_reference_negative_geometry_fields hT hS hN hfield e₀ j.1 j.2
      simp only [hki] at hscalar hfields
      obtain ⟨host, hhost, hraw⟩ := hoptical j.1
      let E := T.E0 (T.sample (K.cell k))
      let t := U.E0 (U.sample (K.cell k))
      let W := C0 * t
      let M := A * W ^ A
      have hcore := materialSample_mem_interval hN.1.1.1.1 hT (K.cell k)
      have hE : 0 < E := (hT.2.1 _ hcore).2.2.1
      have ht : 1 ≤ t := one_le_enlargedMaterialData_E0 hT hcore
      have hEt : E ≤ t := le_enlargedMaterialData_E0 T (T.sample (K.cell k))
      have hW : 1 ≤ W := one_le_mul_of_one_le_of_one_le hC0 ht
      have hM : 1 ≤ M := one_le_mul_of_one_le_of_one_le hA (Real.one_le_rpow hW (zero_le_one.trans hA))
      have hpack {c d Z : ℝ} (hZ : 0 ≤ Z) (hZC : Z ≤ C0) (hd : 0 ≤ d)
          (hcA : c ≤ A) (hdA : d ≤ A) : c * (Z * E) ^ d ≤ M :=
        mul_le_mul hcA ((Real.rpow_le_rpow (mul_nonneg hZ hE.le)
          (mul_le_mul hZC hEt hE.le (zero_le_one.trans hC0)) hd).trans
            (Real.rpow_le_rpow_of_exponent_le hW hdA))
          (Real.rpow_nonneg (mul_nonneg hZ hE.le) _) (zero_le_one.trans hA)
      have hlengthM : lam⁻¹ ≤ M ∧ lam ≤ M ∧ ρ⁻¹ ≤ M ∧ ρ ≤ M := by
        have hh := hlength k j.1 j.2 hk
        rw [hplK, hprK, hlK, hrK, sub_zero] at hh
        have hb : BN * E ^ AN ≤ M := by
          simpa only [one_mul] using hpack zero_le_one hC0 hAN hAparts.1 hAparts.2.1
        exact ⟨hh.1.trans hb, hh.2.1.trans hb, hh.2.2.1.trans hb, hh.2.2.2.trans hb⟩
      have hprodCost {B : ℝ} (hB : 1 ≤ B) (hBA : B ≤ A) :
          B * (CP * E) ^ B ≤ M :=
        hpack (zero_le_one.trans hCP) hscales.1 (zero_le_one.trans hB) hBA hBA
      have hJB (x : ℝ) (hx : x ∈ Ioo l r) (q : ℕ) (hq : q ≤ s) :
          |iteratedDeriv q (fun u => H u ^ (-2 : ℝ) * (D.w u)⁻¹) x| ≤ M :=
        ((hj k j.1 j.2 hk host hhost hraw).1 x hx q hq).trans
          (hprodCost hBJ hAparts.2.2.1)
      have hJIB (x : ℝ) (hx : x ∈ Ioo l r) (q : ℕ) (hq : q ≤ s) :
          |iteratedDeriv q (fun u => H u ^ 2 * D.w u) x| ≤ M := by
        simpa only [Bool.false_eq_true, ite_false, Real.rpow_two] using
          ((hji k j.1 j.2 hk host hhost hraw).1 x hx q hq).trans (hprodCost hBJi hAparts.2.2.2.1)
      have hSB (x : ℝ) (hx : x ∈ Ioo (K.left k) (K.right k)) (q : ℕ) (hq : q ≤ s) :
          |iteratedDeriv q (fun u => H (χ u) ^ 3 * D.w (χ u)) x| ≤ M := by
        simpa only [Bool.false_eq_true, ite_false, Function.comp_def, Real.rpow_natCast,
          Real.rpow_ofNat] using!
          ((hs k j.1 j.2 hk host hhost hraw).2 x hx q hq).trans (hprodCost hBS hAparts.2.2.2.2.1)
      have hSIB (x : ℝ) (hx : x ∈ Ioo (K.left k) (K.right k)) (q : ℕ) (hq : q ≤ s) :
          |iteratedDeriv q (fun u => H (χ u) ^ (-3 : ℝ) * (D.w (χ u))⁻¹) x| ≤ M :=
        ((hsi k j.1 j.2 hk host hhost hraw).2 x hx q hq).trans (hprodCost hBSi hAparts.2.2.2.2.2)
      have hHB (x : ℝ) (hx : x ∈ Ioo l r) (q : ℕ) (hq : q ≤ s) :
          |iteratedDeriv q H x| ≤ M ∧ |iteratedDeriv q (fun u => (H u)⁻¹) x| ≤ M := by
        constructor
        · simpa only [Real.rpow_one] using (hh k j.1 j.2 hk host hhost hraw x hx 0 q).trans
            (hpack (zero_le_one.trans hCH) hscales.2.1 (zero_le_one.trans (hBH q)) (hprefix q hq).1 (hprefix q hq).1)
        · simpa only [Real.rpow_neg_one] using (hhi k j.1 j.2 hk host hhost hraw x hx 0 q).trans
            (hpack (zero_le_one.trans hCH) hscales.2.1 (zero_le_one.trans (hBHi q)) (hprefix q hq).2.1 (hprefix q hq).2.1)
      have hχB (x : ℝ) (hx : x ∈ Ioo (K.left k) (K.right k)) (q : ℕ) (hq : 1 ≤ q) (hqs : q ≤ s) :
          |iteratedDeriv q χ x| ≤ M := by
        have hb := hinverse k j.1 j.2 hk host hhost hraw x hx (q - 1)
        rw [Nat.sub_add_cancel hq] at hb
        exact hb.trans (hpack (zero_le_one.trans hCI) hscales.2.2 (zero_le_one.trans (hBI (q - 1)))
          (hprefix (q - 1) (by omega)).2.2 (hprefix (q - 1) (by omega)).2.2)
      have hYB (x : ℝ) (hx : x ∈ Ioo l r) (q : ℕ) (hq : 1 ≤ q) (hqs : q ≤ s) :
          |iteratedDeriv q Y x| ≤ M := by
        have hu := radialUnit_scalar_normalization (hscalar.2.2.2.2.2.2.1 x hx).2
        have hg : (fun u => |deriv Y u|) =ᶠ[𝓝 x] (fun u => H u ^ (-2 : ℝ) * (D.w u)⁻¹) := by
          filter_upwards [isOpen_Ioo.mem_nhds hx] with u hu'
          exact (radialUnit_scalar_normalization (hscalar.2.2.2.2.2.2.1 u hu').2).2.2
        have hejet := radialUnit_abs_jet_of_abs_germ
          (((hscalar.1.contDiffAt (isOpen_Ioo.mem_nhds hx)).derivWithin (m := ∞)
            (by simp)).continuousAt) hu.1 hg (q - 1)
        rw [← iteratedDeriv_succ', Nat.sub_add_cancel hq] at hejet
        exact hejet.trans_le (hJB x hx (q - 1) (by omega))
      have hnorm {l r y : ℝ} (hlr : l < r) (hy : y ∈ Ioo l r) : |(y - l) / (r - l)| ≤ 1 := by
        rw [abs_of_pos (div_pos (sub_pos.mpr hy.1) (sub_pos.mpr hlr))]
        exact (div_le_one (sub_pos.mpr hlr)).mpr (sub_le_sub_right hy.2.le l)
      have hscalarBound (x : ℝ) (hx : x ∈ Ioo (0 : ℝ) 1) (n : ℕ) (hn : n ≤ s) :
          |iteratedDeriv n (negativeGeometryScalar l lam ρ Y χ H D.w v) x| ≤ M ^ (s + 2) := by
        have hYrange := (hfields.1 (l + lam * x, 0) ⟨hphys hx, mem_univ _⟩).2.2.1
        rw [hlK, hrK] at hYrange
        have hχrange := hscalar.2.2.2.1 (hcan hx)
        have hYzero : |Y (l + lam * x) / ρ| ≤ 1 := by simpa only [sub_zero] using hnorm hρ hYrange
        have hχzero : |(χ (ρ * x) - l) / lam| ≤ 1 := hnorm hlr hχrange
        cases v
        case chartRadial =>
          simpa only [negativeGeometryScalar, sub_zero] using
            negativeGeometry_normalized_bound hM Y l lam 0 ρ x hn
              (by simpa only [abs_of_pos hlam] using hlengthM.2.1)
              (by simpa only [abs_of_pos (inv_pos.mpr hρ)] using hlengthM.2.2.1)
              (by simpa only [sub_zero] using hYzero) (hYB _ (hphys hx))
        case inverseRadial =>
          simpa only [negativeGeometryScalar, zero_add] using
            negativeGeometry_normalized_bound hM χ 0 ρ l lam x hn
              (by simpa only [abs_of_pos hρ] using hlengthM.2.2.2)
              (by simpa only [abs_of_pos (inv_pos.mpr hlam)] using hlengthM.1)
              (by simpa only [zero_add] using hχzero)
              (fun q hq hqs => by simpa only [zero_add] using hχB (ρ * x) (hcan hx) q hq hqs)
        case height =>
          exact negativeGeometry_affine_bound hM H l lam x hn
            (by simpa only [abs_of_pos hlam] using hlengthM.2.1) (hHB _ (hphys hx) n hn).1
        case heightInverse =>
          exact negativeGeometry_affine_bound hM (fun u => (H u)⁻¹) l lam x hn
            (by simpa only [abs_of_pos hlam] using hlengthM.2.1) (hHB _ (hphys hx) n hn).2
        case jacobian =>
          exact negativeGeometry_affine_bound hM (fun u => H u ^ (-2 : ℝ) * (D.w u)⁻¹)
            l lam x hn (by simpa only [abs_of_pos hlam] using hlengthM.2.1)
            (hJB _ (hphys hx) n hn)
        case jacobianInverse =>
          exact negativeGeometry_affine_bound hM (fun u => H u ^ 2 * D.w u) l lam x hn
            (by simpa only [abs_of_pos hlam] using hlengthM.2.1) (hJIB _ (hphys hx) n hn)
        case sourceFactor =>
          simpa only [negativeGeometryScalar, zero_add] using
            negativeGeometry_affine_bound hM (fun u => H (χ u) ^ 3 * D.w (χ u)) 0 ρ x hn
              (by simpa only [abs_of_pos hρ] using hlengthM.2.2.2)
              (by simpa only [zero_add] using hSB (ρ * x) (hcan hx) n hn)
        case sourceFactorInverse =>
          simpa only [negativeGeometryScalar, zero_add] using
            negativeGeometry_affine_bound hM (fun u => H (χ u) ^ (-3 : ℝ) * (D.w (χ u))⁻¹)
              0 ρ x hn (by simpa only [abs_of_pos hρ] using hlengthM.2.2.2)
              (by simpa only [zero_add] using hSIB (ρ * x) (hcan hx) n hn)
        all_goals
          simp only [negativeGeometryScalar, iteratedDeriv_const, ite_self, abs_zero]
          exact pow_nonneg (zero_le_one.trans hM) _
      have hsource : canonicalSource S V (C.referenceState, 0) m (fun _ => 1) =
          canonicalSource S K (C.referenceState, 0) k (fun _ => 1) := by
        funext q
        simp only [canonicalSource, hF, hG, hH]
      have hEq : EqOn (atom D U S C L V (C.referenceState, 0) m v)
          (fun q => negativeGeometryScalar l lam ρ Y χ H D.w v q.1) unitStrip := by
        intro q hq
        have hxq : l + (r - l) * q.1 ∈ Ioo l r := hphys hq.1
        have hf := hfields.1 (l + (r - l) * q.1, q.2) ⟨hxq, mem_univ _⟩
        have hg := hfields.2 (ρ * q.1, q.2) ⟨hcan hq.1, mem_univ _⟩
        have hf1 : K.chart (C.referenceState, 0) k (l + (r - l) * q.1, q.2) =
            (Y (l + (r - l) * q.1), q.2) := hf.1
        have hf2 : K.height (C.referenceState, 0) k (l + (r - l) * q.1, q.2) =
            H (l + (r - l) * q.1) := hf.2.1
        have hf5 : |planeJacobian (K.chart (C.referenceState, 0) k) (l + (r - l) * q.1, q.2)| =
            H (l + (r - l) * q.1) ^ (-2 : ℝ) * (D.w (l + (r - l) * q.1))⁻¹ := hf.2.2.2.2.1
        have hf6 : |planeJacobian (K.chart (C.referenceState, 0) k) (l + (r - l) * q.1, q.2)|⁻¹ =
            H (l + (r - l) * q.1) ^ 2 * D.w (l + (r - l) * q.1) := hf.2.2.2.2.2
        have hg1 : K.inverseChart (C.referenceState, 0) k (ρ * q.1, q.2) =
            (χ (ρ * q.1), q.2) := hg.1
        have hg3 : canonicalSource S K (C.referenceState, 0) k (fun _ => 1) (ρ * q.1, q.2) =
            H (χ (ρ * q.1)) ^ 3 * D.w (χ (ρ * q.1)) := hg.2.2.1
        have hg4 : (canonicalSource S K (C.referenceState, 0) k (fun _ => 1) (ρ * q.1, q.2))⁻¹ =
            H (χ (ρ * q.1)) ^ (-3 : ℝ) * (D.w (χ (ρ * q.1)))⁻¹ := hg.2.2.2
        rcases hv with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
        · simp only [atom, hF, physicalUnitPoint, hl, hr, hpl, hpr, hlK, hrK, hplK, hprK,
            sub_zero, hf1, negativeGeometryScalar, lam]
        · simp only [atom, hF, physicalUnitPoint, hpl, hpr, hplK, hprK, hf1,
            negativeGeometryScalar, sub_self]
        · simp only [atom, hG, canonicalUnitPoint, hl, hr, hpl, hpr, hlK, hrK, hplK, hprK,
            sub_zero, zero_add, hg1, negativeGeometryScalar, lam]
        · simp only [atom, hG, canonicalUnitPoint, hl, hr, hlK, hrK, sub_zero, zero_add, hg1,
            negativeGeometryScalar, sub_self]
        · simp only [atom, hH, physicalUnitPoint, hpl, hpr, hplK, hprK, hf2,
            negativeGeometryScalar, lam]
        · simp only [atom, hH, physicalUnitPoint, hpl, hpr, hplK, hprK, hf2,
            negativeGeometryScalar, lam]
        · simp only [atom, hF, physicalUnitPoint, hpl, hpr, hplK, hprK, hf5,
            negativeGeometryScalar, lam]
        · simp only [atom, hF, physicalUnitPoint, hpl, hpr, hplK, hprK, hf6,
            negativeGeometryScalar, lam]
        · simp only [atom, hsource, canonicalUnitPoint, hl, hr, hlK, hrK, sub_zero, zero_add,
            hg3, negativeGeometryScalar]
        · simp only [atom, hsource, canonicalUnitPoint, hl, hr, hlK, hrK, sub_zero, zero_add,
            hg4, negativeGeometryScalar]
      rw [mixedDerivative_eqOn_of_isOpen (isOpen_Ioo.prod isOpen_univ) hEq a b hp,
        n08_mixedDerivative_radial, hsample]
      have hnumeric : M ^ (s + 2) ≤ BM * t ^ BM := by
        calc
          _ = coefficient * t ^ exponent := by
            dsimp only [M, W, coefficient, exponent]
            rw [mul_pow, ← Real.rpow_mul_natCast (zero_le_one.trans hW) A (s + 2),
              Real.mul_rpow (zero_le_one.trans hC0) (zero_le_one.trans ht)]
            ring
          _ ≤ _ := hfinal t ht
      by_cases hb : b = 0
      · rw [if_pos hb]
        exact (hscalarBound p.1 hp.1 a (by omega)).trans hnumeric
      · rw [if_neg hb, abs_zero]
        exact mul_nonneg hBM.le (Real.rpow_nonneg (zero_le_one.trans ht) _)

end ContinuousFlexibility.Analysis
