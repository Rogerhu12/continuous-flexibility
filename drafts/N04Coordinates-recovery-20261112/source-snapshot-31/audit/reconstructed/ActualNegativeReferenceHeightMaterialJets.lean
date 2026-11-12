import ContinuousFlexibility.Analysis.ActualNegativeOpticalRootDivision
import ContinuousFlexibility.Analysis.ActualNegativeReferenceAiryHeight
import ContinuousFlexibility.Analysis.OpticalHalfAiryHeightMaterialJets
import ContinuousFlexibility.Analysis.ReferenceInverseProfileMaterialJets
import ContinuousFlexibility.Analysis.MaterialGlobalEndpointModels
import Mathlib.Topology.Order.Compact

/-!
# Actual reference height jets on the complete negative half

The stored atlas height is the same optical integral height, not a root
extension selected at each order. The factor, its positive square-root
representative, and the actual half are fixed before asking for a jet.
All costs are paid at the original half sample. The raw optical lower
bound remains explicit until supplied by the retained construction.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter ContinuousFlexibility.Statements
open scoped ContDiff Topology

private theorem negativeHalf_material_pack
    {e E A P M : ℝ} (he : 0 ≤ e) (heE : e ≤ E) (hE : 1 ≤ E)
    (hP : 0 ≤ P) (hAM : A ≤ M) (hPM : P ≤ M) (hM : 1 ≤ M) :
    A * e ^ P ≤ M * E ^ M :=
  mul_le_mul hAM ((Real.rpow_le_rpow he heE hP).trans
    (Real.rpow_le_rpow_of_exponent_le hE hPM))
    (Real.rpow_nonneg he _) (zero_le_one.trans hM)

private theorem negativeHalf_inward_abs_jet
    (f : ℝ → ℝ) (l r : ℝ) (side : Bool) (n : ℕ) (x : ℝ) :
    |iteratedDeriv n (fun y => f (inwardComponentPoint l r side y)) x| =
      |iteratedDeriv n f (inwardComponentPoint l r side x)| := by
  cases side with
  | false =>
      simp only [inwardComponentPoint, Bool.false_eq_true, ↓reduceIte,
        iteratedDeriv_comp_const_add]
  | true =>
      simp only [inwardComponentPoint, ↓reduceIte, iteratedDeriv_comp_const_sub,
        smul_eq_mul, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul]

private theorem negativeHalf_profile_compact_jets
    {D : ReferenceData} (hD : RadialProfileGeometry D) :
    ∃ M : ℕ → ℝ, (∀ n, 1 ≤ M n) ∧ ∀ n r, r ∈ Icc D.a D.b →
      |iteratedDeriv n D.w r| ≤ M n := by
  classical
  have hb (n : ℕ) : ∃ A : ℝ, ∀ r ∈ Icc D.a D.b, ‖iteratedDeriv n D.w r‖ ≤ A :=
    isCompact_Icc.exists_bound_of_continuousOn
      (ContDiff.continuous_iteratedDeriv n hD.2.2.1.1 (by simp)).continuousOn
  choose A hA using hb
  refine ⟨(fun n => 1 + |A n|), (fun n => le_add_of_nonneg_right (abs_nonneg _)), ?_⟩
  intro n r hr
  have he : |iteratedDeriv n D.w r| ≤ A n := by
    simpa only [Real.norm_eq_abs] using hA n r hr
  exact (he.trans (le_abs_self _)).trans (le_add_of_nonneg_left zero_le_one)

/-- A common sample scale and all-order constants control every real
power of the actual stored reference height throughout either open
optical half. The true host is an input to the optical lower bound and
is never identified with the sample cell stored by the atlas. -/
theorem n04bActualTypedAtlas_reference_half_height_power_material_jets
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {R : ReturnEquationData S}
    {L : ReturnCorrectionData S} {base loss : ℕ} {ε K₀ : ℝ}
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (hN : NonlinearPropertiesThrough03 D T S C R L base loss ε)
    (hfield : N04bFieldRegularity D S C L base ε) (e : ℕ ≃ N04PieceIndex D)
    (hK₀ : 0 < K₀) :
    let K := n04bActualTypedAtlas hT hS hN hfield e
    let cut := n04bActualReferenceCut hN
    ∃ C0 : ℝ, 1 ≤ C0 ∧ (∀ j, 1 ≤ C0 * T.E0 (T.sample j)) ∧
      ∀ a : ℝ, ∃ B : ℕ → ℝ, (∀ n, 1 ≤ B n) ∧
      ∀ k m side, e k = .inl (m, side) →
      ∀ j, Ioo (C.left m) (C.right m) ⊆ D.cells j →
      (∀ r ∈ Ioo (C.left m) (C.right m),
        K₀⁻¹ * T.E0 (T.sample j) ^ (-K₀) *
          min (r - C.left m) (C.right m - r) ≤ -deriv D.w r / (r * D.w r)) →
      ∀ x, x ∈ Ioo (0 : ℝ)
          (n04bNegativeRight C cut (m, side) - n04bNegativeLeft C cut (m, side)) →
      ∀ θ : ℝ, ∀ n : ℕ,
        |iteratedDeriv n (fun t => K.height (C.referenceState, 0) k
          (inwardComponentPoint (C.left m) (C.right m) side t, θ) ^ a) x| ≤
            B n * (C0 * T.E0 (T.sample (K.cell k))) ^ (B n) := by
  classical
  dsimp only
  let K := n04bActualTypedAtlas hT hS hN hfield e
  let cut := n04bActualReferenceCut hN
  have hD := n04b_profileGeometry_of_through03 hN
  obtain ⟨C0, hC0, hfloor⟩ := material_E0_uniform_scaled_lower hT hN.1.1.1.1
  obtain ⟨Ag, Pg, hAg, hPg, Bg, Qg, hBg, hQg, hdivision⟩ :=
    n04bActualTypedAtlas_opticalRootDivision_half_material hT hS hN hfield e hK₀
  obtain ⟨Mw, hMw, hwJets⟩ := negativeHalf_profile_compact_jets hD
  obtain ⟨Ki, Pi, hKi, hPi, hiPoint⟩ :=
    material_inverseProfile_finite_point_jets hT hN.1.1.1.1 0
  obtain ⟨Ks, Ps, hKs, hPs, hiSample⟩ :=
    n04bActualTypedAtlas_negative_material_sample_weights hT hS hN hfield e 0 0 Pi hPi
  let A : ℕ → ℝ := fun n => 1 + Ag n + Pg n + Mw n
  have hA (n : ℕ) : 1 ≤ A n := by
    dsimp only [A]
    linarith only [hAg n, hPg n, hMw n]
  have hgA (n : ℕ) : Ag n ≤ A n := by
    dsimp only [A]
    linarith only [hPg n, hMw n]
  have hpA (n : ℕ) : Pg n ≤ A n := by
    dsimp only [A]
    linarith only [hAg n, hMw n]
  have hwA (n : ℕ) : Mw n ≤ A n := by
    dsimp only [A]
    linarith only [hAg n, hPg n]
  let M : ℝ := 1 + A 0 + Bg + Qg + Ki * Ks + Ps
  have hKiKs : 0 < Ki * Ks := mul_pos hKi hKs
  have hM : 1 ≤ M := by
    dsimp only [M]
    linarith only [hA 0, hBg, hQg, hKiKs, hPs]
  have hA0M : A 0 ≤ M := by
    dsimp only [M]
    linarith only [hBg, hQg, hKiKs, hPs]
  have hBgM : Bg ≤ M := by
    dsimp only [M]
    linarith only [hA 0, hQg, hKiKs, hPs]
  have hQgM : Qg ≤ M := by
    dsimp only [M]
    linarith only [hA 0, hBg, hKiKs, hPs]
  have hKiKsM : Ki * Ks ≤ M := by
    dsimp only [M]
    linarith only [hA 0, hBg, hQg, hPs]
  have hPsM : Ps ≤ M := by
    dsimp only [M]
    linarith only [hA 0, hBg, hQg, hKiKs]
  refine ⟨C0, hC0, (fun j => hfloor _ (materialSample_mem_interval hN.1.1.1.1 hT j)), ?_⟩
  intro a
  obtain ⟨B, hB, hheightJets⟩ := opticalHalf_airyHeight_power_material_jets a M hM A hA
  refine ⟨B, hB, ?_⟩
  intro k m side hk j hhost hoptical
  let d : ℝ := n04bNegativeRight C cut (m, side) - n04bNegativeLeft C cut (m, side)
  let U : ℝ := C0 * T.E0 (T.sample (K.cell k))
  have hU : 1 ≤ U := hfloor _ (materialSample_mem_interval hN.1.1.1.1 hT (K.cell k))
  have hE : 0 < T.E0 (T.sample (K.cell k)) :=
    (hT.2.1 _ (materialSample_mem_interval hN.1.1.1.1 hT (K.cell k))).2.2.1
  have hEU : T.E0 (T.sample (K.cell k)) ≤ U := by
    simpa only [one_mul] using mul_le_mul_of_nonneg_right hC0 hE.le
  have hcut := n04bActualReferenceCut_mem hN m
  have hd : 0 < d := by
    cases side <;> simp only [d, n04bNegativeRight, n04bNegativeLeft,
      Bool.false_eq_true, ↓reduceIte]
    · exact sub_pos.mpr hcut.1
    · exact sub_pos.mpr hcut.2
  have hdL : d ≤ C.right m - C.left m := by
    cases side <;> simp only [d, n04bNegativeRight, n04bNegativeLeft,
      Bool.false_eq_true, ↓reduceIte] <;> linarith only [hcut.1, hcut.2]
  have hcomp := n01Properties_negativeRadialComponent hN.1.1 m
  have hr (x : ℝ) (hx : x ∈ Icc (0 : ℝ) d) :
      inwardComponentPoint (C.left m) (C.right m) side x ∈ Icc (C.left m) (C.right m) :=
    inwardComponentPoint_mem side ⟨hx.1, hx.2.trans hdL⟩
  have hcore (x : ℝ) (hx : x ∈ Icc (0 : ℝ) d) :
      inwardComponentPoint (C.left m) (C.right m) side x ∈ radialCore D :=
    ⟨hcomp.1.trans_le (hr x hx).1, (hr x hx).2.trans_lt hcomp.2.2.1⟩
  obtain ⟨g, hg, hfactor, hgJets, hgInverse⟩ := hdivision k m side hk j hhost hoptical
  have hgPack (n : ℕ) (x : ℝ) (hx : x ∈ Icc (0 : ℝ) d) :
      |iteratedDeriv n g x| ≤ A n * U ^ (A n) :=
    (hgJets n x ⟨hx.1, hx.2.trans hdL⟩).trans
      (negativeHalf_material_pack hE.le hEU hU (hPg n) (hgA n) (hpA n) (hA n))
  have hgValues (x : ℝ) (hx : x ∈ Icc (0 : ℝ) d) :
      0 < g x ∧ g x ≤ M * U ^ M ∧ (g x)⁻¹ ≤ M * U ^ M := by
    have hi := hgInverse x hx
    refine ⟨hi.1, ?_, ?_⟩
    · have hj : |g x| ≤ A 0 * U ^ (A 0) := by
        simpa only [iteratedDeriv_zero] using hgPack 0 x hx
      exact ((le_abs_self _).trans hj).trans
        (negativeHalf_material_pack (zero_le_one.trans hU) le_rfl hU
          (zero_le_one.trans (hA 0)) hA0M hA0M hM)
    · exact hi.2.trans (negativeHalf_material_pack hE.le hEU hU hQg hBgM hQgM hM)
  let w : ℝ → ℝ := fun x => D.w (inwardComponentPoint (C.left m) (C.right m) side x)
  have hinward : ContDiff ℝ ∞ (inwardComponentPoint (C.left m) (C.right m) side) := by
    cases side
    · exact contDiff_const.add contDiff_id
    · exact contDiff_const.sub contDiff_id
  have hw : ContDiff ℝ ∞ w := hD.2.2.1.1.comp hinward
  have hwPack (n : ℕ) (x : ℝ) (hx : x ∈ Icc (0 : ℝ) d) :
      |iteratedDeriv n w x| ≤ A n * U ^ (A n) := by
    change |iteratedDeriv n
      (fun y => D.w (inwardComponentPoint (C.left m) (C.right m) side y)) x| ≤ _
    rw [negativeHalf_inward_abs_jet D.w (C.left m) (C.right m) side n x]
    exact (hwJets n _ ⟨(hcore x hx).1.le, (hcore x hx).2.le⟩).trans
      ((hwA n).trans (le_mul_of_one_le_right (zero_le_one.trans (hA n))
        (Real.one_le_rpow hU (zero_le_one.trans (hA n)))))
  have hwValues (x : ℝ) (hx : x ∈ Icc (0 : ℝ) d) :
      ContDiffAt ℝ ∞ w x ∧ 0 < w x ∧
        w x ≤ M * U ^ M ∧ (w x)⁻¹ ≤ M * U ^ M := by
    have hwpos : 0 < w x := hD.2.2.2.2.1 _ (hcore x hx)
    refine ⟨hw.contDiffAt, hwpos, ?_, ?_⟩
    · have hj : |w x| ≤ A 0 * U ^ (A 0) := by
        simpa only [iteratedDeriv_zero] using hwPack 0 x hx
      exact ((le_abs_self _).trans hj).trans
        (negativeHalf_material_pack (zero_le_one.trans hU) le_rfl hU
          (zero_le_one.trans (hA 0)) hA0M hA0M hM)
    · have hi : (w x)⁻¹ ≤ Ki * T.E0
          (inwardComponentPoint (C.left m) (C.right m) side x) ^ Pi := by
        have hip := hiPoint _ (hcore x hx) 0 le_rfl
        change |(w x)⁻¹| ≤ Ki * T.E0
          (inwardComponentPoint (C.left m) (C.right m) side x) ^ Pi at hip
        simpa only [abs_of_pos (inv_pos.mpr hwpos)] using hip
      have hs : T.E0 (inwardComponentPoint (C.left m) (C.right m) side x) ^ Pi ≤
          Ks * T.E0 (T.sample (K.cell k)) ^ Ps := by
        simpa only [Real.rpow_zero, one_mul] using hiSample k m side hk _ (hr x hx)
      have hi' : (w x)⁻¹ ≤ (Ki * Ks) * T.E0 (T.sample (K.cell k)) ^ Ps :=
        hi.trans ((mul_le_mul_of_nonneg_left hs hKi.le).trans_eq (by ring))
      exact hi'.trans (negativeHalf_material_pack hE.le hEU hU hPs hKiKsM hPsM hM)
  let V : ℝ := M * U ^ M
  have hV : 0 < V := mul_pos (zero_lt_one.trans_le hM)
    (Real.rpow_pos_of_pos (zero_lt_one.trans_le hU) _)
  have hgRange : ∀ x ∈ Icc (0 : ℝ) d, V⁻¹ ≤ g x ∧ g x ≤ V := by
    intro x hx
    refine ⟨?_, (hgValues x hx).2.1⟩
    have hh := inv_anti₀ (inv_pos.mpr (hgValues x hx).1) (hgValues x hx).2.2
    simpa only [inv_inv] using hh
  obtain ⟨c, hc, hcpos, hAveragePos, hcGerm, _⟩ :=
    exists_opticalHalfAiryAverage_of_factor_bounds hg hd.le (inv_pos.mpr hV) hgRange
  have hjets := hheightJets U hU g c w d hg hc
    (fun x hx => (hcGerm x hx).1) hgValues hwValues
    (fun n x hx => ⟨hgPack n x hx, hwPack n x hx⟩)
  have hek : e.symm (.inl (m, side)) = k := by rw [← hk, e.symm_apply_apply]
  intro x hx θ n
  have he : EqOn
      (fun t => K.height (C.referenceState, 0) k
        (inwardComponentPoint (C.left m) (C.right m) side t, θ) ^ a)
      (fun t => n06AiryRadialHeight c w t ^ a) (Ioo (0 : ℝ) d) := by
    intro t ht
    have hh := n04Coordinates_actual_reference_negative_airy_height
      hT hS hN hfield e m side hdL
      (fun y hy => hfactor y ⟨hy.1, hy.2.trans hdL⟩)
      hc hcpos hAveragePos (fun y hy => ((hcGerm y hy).1).self_of_nhds) ht θ
    change K.height (C.referenceState, 0) (e.symm (.inl (m, side)))
      (inwardComponentPoint (C.left m) (C.right m) side t, θ) =
        n06AiryRadialHeight c w t at hh
    rw [hek] at hh
    exact congrArg (fun v : ℝ => v ^ a) hh
  rw [he.iteratedDeriv_of_isOpen isOpen_Ioo n hx]
  exact hjets x ⟨hx.1.le, hx.2.le⟩ n

/-- The same estimates in the actual physical radius have no orientation
cost: the inward coordinate has slope of absolute value one. -/
theorem n04bActualTypedAtlas_reference_half_height_physical_power_material_jets
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {R : ReturnEquationData S}
    {L : ReturnCorrectionData S} {base loss : ℕ} {ε K₀ : ℝ}
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (hN : NonlinearPropertiesThrough03 D T S C R L base loss ε)
    (hfield : N04bFieldRegularity D S C L base ε) (e : ℕ ≃ N04PieceIndex D)
    (hK₀ : 0 < K₀) :
    let K := n04bActualTypedAtlas hT hS hN hfield e
    let cut := n04bActualReferenceCut hN
    ∃ C0 : ℝ, 1 ≤ C0 ∧ (∀ j, 1 ≤ C0 * T.E0 (T.sample j)) ∧
      ∀ a : ℝ, ∃ B : ℕ → ℝ, (∀ n, 1 ≤ B n) ∧
      ∀ k m side, e k = .inl (m, side) →
      ∀ j, Ioo (C.left m) (C.right m) ⊆ D.cells j →
      (∀ r ∈ Ioo (C.left m) (C.right m),
        K₀⁻¹ * T.E0 (T.sample j) ^ (-K₀) *
          min (r - C.left m) (C.right m - r) ≤ -deriv D.w r / (r * D.w r)) →
      ∀ r, r ∈ Ioo (n04bNegativeLeft C cut (m, side))
          (n04bNegativeRight C cut (m, side)) →
      ∀ θ : ℝ, ∀ n : ℕ,
        |iteratedDeriv n (fun t => K.height (C.referenceState, 0) k (t, θ) ^ a) r| ≤
          B n * (C0 * T.E0 (T.sample (K.cell k))) ^ (B n) := by
  dsimp only
  let K := n04bActualTypedAtlas hT hS hN hfield e
  let cut := n04bActualReferenceCut hN
  obtain ⟨C0, hC0, hfloor, hfamily⟩ :=
    n04bActualTypedAtlas_reference_half_height_power_material_jets hT hS hN hfield e hK₀
  refine ⟨C0, hC0, hfloor, ?_⟩
  intro a
  obtain ⟨B, hB, hjets⟩ := hfamily a
  refine ⟨B, hB, ?_⟩
  intro k m side hk j hhost hoptical r hr θ n
  let x : ℝ := if side then C.right m - r else r - C.left m
  have hx : x ∈ Ioo (0 : ℝ)
      (n04bNegativeRight C cut (m, side) - n04bNegativeLeft C cut (m, side)) := by
    cases side <;> simp only [x, n04bNegativeRight, n04bNegativeLeft,
      Bool.false_eq_true, ↓reduceIte] at hr ⊢ <;> constructor <;> linarith only [hr.1, hr.2]
  have he : inwardComponentPoint (C.left m) (C.right m) side x = r := by
    cases side <;> simp only [x, inwardComponentPoint, Bool.false_eq_true, ↓reduceIte] <;> ring
  have hb := hjets k m side hk j hhost hoptical x hx θ n
  have hejet := negativeHalf_inward_abs_jet
    (fun t => K.height (C.referenceState, 0) k (t, θ) ^ a)
    (C.left m) (C.right m) side n x
  rw [he] at hejet
  rw [hejet] at hb
  exact hb

end ContinuousFlexibility.Analysis
