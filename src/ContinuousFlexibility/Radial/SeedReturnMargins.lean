import ContinuousFlexibility.Radial.MorseNegativeCover
import ContinuousFlexibility.Radial.SeedCentralReturn
import ContinuousFlexibility.Radial.ReferenceFiniteIndexFloor
import ContinuousFlexibility.Radial.TwoTailReferenceAssembly

/-!
# Return margins for the actual glued seed

All negative intervals are retained Morse intervals or the central turning
interval. The actual surgery coordinate transports their cell coverage.
A finite index floor treats the compact central interval, and cell
saturation then gives whole-interval containment. The analytic profile,
Jacobi field and endpoints are never changed by these two operations.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open Set Real
open ContinuousFlexibility.Statements
open scoped ContDiff

private def ModelReturnAt (D : ReferenceData) (r : ℝ) : Prop :=
  ∃ l h : ℝ, ∃ n d : ℕ,
    NegativeRadialComponent D l h ∧ r ∈ Ioo l h ∧
    1 ≤ n ∧ 0 < d ∧ (¬ ∃ k : ℕ, k ^ 2 = d) ∧
    (d : ℝ) ≤ exp ((n : ℝ) ^ 2) + 2 ∧
    radialTravel D l h = Real.pi / (2 * sqrt (d : ℝ)) ∧
    ∀ t ∈ Ioo l h, ∃ m, D.cellIndex m = n ∧ t ∈ D.cells m

/-- The same transport argument applies to the left and right model
tails. Its cell premises are the actual coordinate pullback identities. -/
private theorem modelReturnAt_scaled_tail
    {T : MorseChainData} {σ : ℕ → ℝ} {D E : ReferenceData} {C : ℕ → ℝ}
    (hreal : MorseChainRealization T σ D C) (hσ : ∀ n, 1 ≤ σ n ∧ σ n ≤ 2)
    (side : Bool) {start N : ℕ} (hstart : T.index ≤ start) (hN : 1 ≤ N)
    {R H : ℝ} (hR : 0 < R) (hH : 0 < H)
    (hE : ContDiff ℝ ∞ E.w)
    (hcore : ∀ s ∈ radialTailInterval D side (morseChainSeam T side start),
      R * s ∈ radialCore E)
    (hprofile : ∀ s ∈ radialTailInterval D side (morseChainSeam T side start),
      E.w (R * s) = H * R * D.w s)
    (hcells : ∀ m s, s ∈ radialTailInterval D side (morseChainSeam T side start) →
      s ∈ D.cells m → R * s ∈ E.cells m)
    (hindex : ∀ m, E.cellIndex m = max (D.cellIndex m) N)
    {r : ℝ}
    (hr : r ∈ radialTailInterval D side (morseChainSeam T side start))
    (hneg : deriv D.w r < 0) :
    ModelReturnAt E (R * r) := by
  obtain ⟨n, hn, l, h, hcomponent, hrI, hclosed, htravel, hcover⟩ :=
    morseRealization_negative_tail_component hreal hσ side hstart hr hneg
  have hlh := hcomponent.2.1
  have hl := hclosed (left_mem_Icc.mpr hlh.le)
  have hh := hclosed (right_mem_Icc.mpr hlh.le)
  have htail : radialTailInterval D side (morseChainSeam T side start) =
      Ioo (if side then morseChainSeam T side start else D.a)
        (if side then D.b else morseChainSeam T side start) := by
    cases side <;> rfl
  have htransport := negativeRadialComponent_travel_of_tail_identity hR hH hcomponent
    (hcore l hl).1 (hcore h hh).2 hreal.geometry.2.2.1.1 hE
    (by simpa only [htail] using hclosed)
    (by simpa only [htail] using hprofile)
  have hdpos : 0 < T.d n := by
    have hp : (0 : ℝ) < T.d n := (exp_pos _).trans_le (hreal.1 n hn).1
    exact_mod_cast hp
  have hsize : (T.d n : ℝ) ≤ exp (((max n N : ℕ) : ℝ) ^ 2) + 2 := by
    rw [hreal.d_eq n hn]
    have hcast : (n : ℝ) ≤ (max n N : ℕ) := by exact_mod_cast Nat.le_max_left n N
    have hsq : (n : ℝ) ^ 2 ≤ ((max n N : ℕ) : ℝ) ^ 2 := by
      exact pow_le_pow_left₀ (Nat.cast_nonneg n : (0 : ℝ) ≤ (n : ℝ)) hcast 2
    exact (morseChainInteger_lt n).le.trans
      (add_le_add (exp_le_exp.mpr hsq) (le_refl 2))
  refine ⟨R * l, R * h, max n N, T.d n, htransport.1, ?_,
    hN.trans (Nat.le_max_right _ _), hdpos, (hreal.1 n hn).2.1, hsize,
    htransport.2.trans htravel, ?_⟩
  · exact ⟨mul_lt_mul_of_pos_left hrI.1 hR, mul_lt_mul_of_pos_left hrI.2 hR⟩
  · intro t ht
    have hs : t / R ∈ Ioo l h := by
      constructor
      · exact (lt_div_iff₀ hR).mpr (by simpa only [mul_comm] using ht.1)
      · exact (div_lt_iff₀ hR).mpr (by simpa only [mul_comm] using ht.2)
    obtain ⟨m, hm, hmem⟩ := hcover (t / R) hs
    have hnew := hcells m (t / R) (hclosed (Ioo_subset_Icc_self hs)) hmem
    have hcancel : R * (t / R) = t := by field_simp [hR.ne']
    rw [hcancel] at hnew
    exact ⟨m, by rw [hindex m, hm], hnew⟩

private theorem two_is_not_nat_square : ¬ ∃ k : ℕ, k ^ 2 = 2 := by
  rintro ⟨k, hk⟩
  by_cases hk0 : k = 0
  · simp only [hk0, zero_pow (by decide : (2 : ℕ) ≠ 0)] at hk
    omega
  by_cases hk1 : k = 1
  · simp only [hk1, one_pow] at hk
    omega
  have hk2 : 2 ≤ k := by omega
  nlinarith only [hk, hk2]

/-- The actual glued construction establishes all return margins on the
same reference as its global second-mode solution. -/
theorem SeedGluedPair.exists_accumulating_reference_with_construction_geometry
    {T : MorseChainData} {σ : ℕ → ℝ} {D : ReferenceData} {C : ℕ → ℝ}
    {c d : ℝ} {uL uR : ℝ → ℝ} {K : SeedCentralCutoff} {q : ℝ}
    (G : SeedGluedPair D c d uL uR K q)
    (hreal : MorseChainRealization T σ D C) (hσ : ∀ n, 1 ≤ σ n ∧ σ n ≤ 2)
    (hq : 0 < q) {start : ℕ} (hstart : T.index ≤ start)
    (hcseam : c = morseChainSeam T false start)
    (hdseam : d = morseChainSeam T true start)
    (hc : c ∈ radialCore D) (hd : d ∈ radialCore D) (hcd : c < d) :
    ∃ E : ReferenceData,
      E.a = G.radiusL * D.a ∧ E.b = G.radiusR * D.b ∧
      E.w = G.profile ∧ E.phi = G.height ∧
      IsAccumulatingProfile E ∧ RadialConstructionGeometry E := by
  obtain ⟨E₀, hEa, hEb, hEw, hEphi, hAccum₀, e, heCells, heIndex, heLeft, heRight⟩ :=
    exists_accumulating_reference_of_two_tail_surgery_with_cells
      ⟨C, hreal.accumulating⟩ G.radiusL_pos G.radius_order G.heightL_pos G.heightR_pos
      hc.1 hcd hd.2 G.geometry
      (fun r hr => (G.left_tail r hr).1) (fun r hr => (G.right_tail r hr).1)
  have hGeo₀ : RadialProfileGeometry E₀ := (Classical.choose_spec hAccum₀).1
  let l := centralRadius (-sqrt centralOscillatorA)
  let h := centralRadius (sqrt centralOscillatorA)
  have hcentral := G.central_model_return hq hc hd
  have hcomponent : NegativeRadialComponent E₀ l h := by
    simpa only [NegativeRadialComponent, l, h, hEa, hEb, hEw] using hcentral.1
  have htravel : radialTravel E₀ l h = Real.pi / (2 * sqrt 2) := by
    simpa only [radialTravel, l, h, hEw] using hcentral.2
  have hKcore : Icc l h ⊆ radialCore E₀ := by
    intro r hr
    exact ⟨hcomponent.1.trans_le hr.1, hr.2.trans_lt hcomponent.2.2.1⟩
  obtain ⟨N, hN, hcentralCover⟩ :=
    exists_floorReferenceIndex_compact_cover hAccum₀ isCompact_Icc hKcore
  let F := floorReferenceIndex E₀ N
  have hF : IsAccumulatingProfile F := isAccumulatingProfile_floorReferenceIndex hAccum₀ N hN
  have hindex (m : ℕ) : F.cellIndex m = max (D.cellIndex m) N := by
    change max (E₀.cellIndex m) N = max (D.cellIndex m) N
    simp only [heIndex, max_assoc, max_eq_right hN]
  have hRR : 0 < G.radiusR := G.radiusL_pos.trans_le G.radius_order
  have hdpos : 0 < d := hreal.geometry.1.trans hd.1
  have hleftCore (s : ℝ) (hs : s ∈ Ioo D.a c) :
      G.radiusL * s ∈ radialCore F := by
    change E₀.a < G.radiusL * s ∧ G.radiusL * s < E₀.b
    rw [hEa, hEb]
    constructor
    · exact mul_lt_mul_of_pos_left hs.1 G.radiusL_pos
    · exact ((mul_lt_mul_of_pos_left (hs.2.trans hcd) G.radiusL_pos).trans_le
        (mul_le_mul_of_nonneg_right G.radius_order hdpos.le)).trans
        (mul_lt_mul_of_pos_left hd.2 hRR)
  have hrightCore (s : ℝ) (hs : s ∈ Ioo d D.b) :
      G.radiusR * s ∈ radialCore F := by
    change E₀.a < G.radiusR * s ∧ G.radiusR * s < E₀.b
    rw [hEa, hEb]
    constructor
    · exact (mul_le_mul_of_nonneg_right G.radius_order hreal.geometry.1.le).trans_lt
        (mul_lt_mul_of_pos_left (hd.1.trans hs.1) hRR)
    · exact mul_lt_mul_of_pos_left hs.2 hRR
  have hleftCells (m : ℕ) (s : ℝ) (hs : s ∈ Ioo D.a c) (hm : s ∈ D.cells m) :
      G.radiusL * s ∈ F.cells m := by
    change G.radiusL * s ∈ E₀.cells m
    rw [heCells]
    change e (G.radiusL * s) ∈ D.cells m
    rw [← heLeft s hs.2.le, e.apply_symm_apply]
    exact hm
  have hrightCells (m : ℕ) (s : ℝ) (hs : s ∈ Ioo d D.b) (hm : s ∈ D.cells m) :
      G.radiusR * s ∈ F.cells m := by
    change G.radiusR * s ∈ E₀.cells m
    rw [heCells]
    change e (G.radiusR * s) ∈ D.cells m
    rw [← heRight s hs.1.le, e.apply_symm_apply]
    exact hm
  have hmodels (r : ℝ) (hr : r ∈ radialCore F) (hneg : deriv F.w r < 0) :
      ModelReturnAt F r := by
    have hrG : r ∈ Ioo (G.radiusL * D.a) (G.radiusR * D.b) := by
      change E₀.a < r ∧ r < E₀.b at hr
      simpa only [Set.mem_Ioo, hEa, hEb] using hr
    have hnegG : deriv G.profile r < 0 := by
      change deriv E₀.w r < 0 at hneg
      simpa only [hEw] using hneg
    rcases G.negative_deriv_cases hq hrG hnegG with hleft | hmiddle | hright
    · obtain ⟨s, hs, rfl, hsneg⟩ := hleft
      apply modelReturnAt_scaled_tail (E := F) hreal hσ false hstart hN
        G.radiusL_pos G.heightL_pos hGeo₀.2.2.1.1
        (by simpa only [radialTailInterval, Bool.false_eq_true, ↓reduceIte, ← hcseam]
          using hleftCore)
        (by
          intro t ht
          change E₀.w (G.radiusL * t) = _
          rw [hEw]
          exact (G.left_tail t (by simpa only
            [radialTailInterval, Bool.false_eq_true, ↓reduceIte, ← hcseam] using ht)).1)
        (by simpa only [radialTailInterval, Bool.false_eq_true, ↓reduceIte, ← hcseam]
          using hleftCells) hindex
        (by simpa only [radialTailInterval, Bool.false_eq_true, ↓reduceIte, ← hcseam] using hs)
        hsneg
    · obtain ⟨hrMiddle, hnegCentral⟩ := hmiddle
      have hrpos : 0 < r := (exp_pos K.left).trans hrMiddle.1
      have hx : centralModelCoordinate r ^ 2 < centralOscillatorA := by
        apply (centralRadialProfile_deriv_neg_iff (by norm_num : (0 : ℝ) < 1) _).mp
        rw [centralRadius_modelCoordinate hrpos]
        exact hnegCentral
      have hxI := sq_lt.mp hx
      have hrI : r ∈ Ioo l h :=
        ⟨(strictMono_centralRadius hxI.1).trans_eq (centralRadius_modelCoordinate hrpos),
          (centralRadius_modelCoordinate hrpos).symm.trans_lt
            (strictMono_centralRadius hxI.2)⟩
      refine ⟨l, h, N, 2, hcomponent, hrI, hN, by decide, two_is_not_nat_square,
        ?_, htravel, ?_⟩
      · have hp := (exp_pos ((N : ℝ) ^ 2)).le
        norm_num only [Nat.cast_ofNat]
        linarith only [hp]
      · intro t ht
        exact hcentralCover t (Ioo_subset_Icc_self ht)
    · obtain ⟨s, hs, rfl, hsneg⟩ := hright
      apply modelReturnAt_scaled_tail (E := F) hreal hσ true hstart hN
        hRR G.heightR_pos hGeo₀.2.2.1.1
        (by simpa only [radialTailInterval, ↓reduceIte, ← hdseam] using hrightCore)
        (by
          intro t ht
          change E₀.w (G.radiusR * t) = _
          rw [hEw]
          exact (G.right_tail t (by simpa only
            [radialTailInterval, ↓reduceIte, ← hdseam] using ht)).1)
        (by simpa only [radialTailInterval, ↓reduceIte, ← hdseam] using hrightCells) hindex
        (by simpa only [radialTailInterval, ↓reduceIte, ← hdseam] using hs) hsneg
  refine ⟨saturateReferenceCells F, hEa, hEb, hEw, hEphi,
    isAccumulatingProfile_saturateReferenceCells hF, ?_, ?_⟩
  · intro r hr
    change radialJacobi 4 E₀.w E₀.phi r = 0
    rw [hEw, hEphi]
    apply G.equation r
    change E₀.a < r ∧ r < E₀.b at hr
    simpa only [Set.mem_Ioo, hEa, hEb] using hr
  · exact radialReturnMargins_saturate_of_model_components hmodels

end ContinuousFlexibility.Radial
