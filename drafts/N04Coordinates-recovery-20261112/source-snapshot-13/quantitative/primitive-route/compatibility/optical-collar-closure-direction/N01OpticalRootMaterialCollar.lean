import ContinuousFlexibility.Analysis.N01OpticalRootDivision
import ContinuousFlexibility.Analysis.N01ComponentMaterialWidth
import ContinuousFlexibility.Analysis.SmoothDivisionExplicitCollar
import ContinuousFlexibility.Analysis.RetainedReferenceOpticalEnvelope

/-!
# A material collar of the actual retained optical root divisor

The actual first jet of the normalized optical divisor fixes the collar.
Its inverse width has one sampled material bound before the component or
endpoint is chosen. The public construction theorem obtains the simple
root lower bound from the same retained reference certificate; it does
not replace an existing reference or postulate a common state germ.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter
open ContinuousFlexibility.Statements
open scoped Topology ContDiff

/-- Cancel the positive inward coordinate before taking the actual
one-sided limit of the normalized divisor. -/
theorem normalizedOpticalRootDivision_lower_at_zero
    {D : ReferenceData} {l h κ : ℝ} {g : ℝ → ℝ}
    (hlh : l < h) (rightEnd : Bool) (hg : ContDiff ℝ ∞ g)
    (hfactor : ∀ t ∈ Icc (0 : ℝ) (h - l),
      n01aOpticalRadicand D.w (inwardComponentPoint l h rightEnd t) = t * g t)
    (hlower : ∀ r ∈ Ioo l h,
      κ * min (r - l) (h - r) ≤ n01aOpticalRadicand D.w r) :
    κ ≤ g 0 := by
  have hρ : 0 < (h - l) / 2 := half_pos (sub_pos.mpr hlh)
  have hgeometry (t : ℝ) (ht : t ∈ Ioo (0 : ℝ) ((h - l) / 2)) :
      inwardComponentPoint l h rightEnd t ∈ Ioo l h ∧
      min (inwardComponentPoint l h rightEnd t - l)
        (h - inwardComponentPoint l h rightEnd t) = t := by
    cases rightEnd with
    | false =>
      simp only [inwardComponentPoint, Bool.false_eq_true, ↓reduceIte]
      constructor
      · constructor <;> linarith only [ht.1, ht.2]
      · rw [min_eq_left (by linarith only [ht.2])]
        ring
    | true =>
      simp only [inwardComponentPoint, ↓reduceIte]
      constructor
      · constructor <;> linarith only [ht.1, ht.2]
      · rw [min_eq_right (by linarith only [ht.2])]
        ring
  have hcl : (0 : ℝ) ∈ closure (Ioo (0 : ℝ) ((h - l) / 2)) := by
    rw [closure_Ioo hρ.ne]
    exact ⟨le_rfl, hρ.le⟩
  haveI : NeBot (𝓝[Ioo (0 : ℝ) ((h - l) / 2)] (0 : ℝ)) :=
    mem_closure_iff_nhdsWithin_neBot.mp hcl
  have hb : ∀ᶠ t in 𝓝[Ioo (0 : ℝ) ((h - l) / 2)] (0 : ℝ), κ ≤ g t := by
    filter_upwards [self_mem_nhdsWithin] with t ht
    have htfull : t ∈ Icc (0 : ℝ) (h - l) := by
      constructor
      · exact ht.1.le
      · linarith only [ht.2, hlh]
    have he := hlower _ (hgeometry t ht).1
    rw [(hgeometry t ht).2, hfactor t htfull] at he
    exact (mul_le_mul_left ht.1).mp (by simpa only [mul_comm κ t] using he)
  exact ge_of_tendsto hg.continuous.continuousAt.continuousWithinAt.tendsto hb

private theorem normalizedOpticalRoot_material_collars_of_lower
    {D : ReferenceData} {T : MaterialData} {Sp : PhysicalSpacesData}
    {C : NonlinearGeometryData Sp} {base loss : ℕ} {ε Kκ Pκ : ℝ}
    (hN : N01Properties D T Sp C base loss ε) (hT : IsMaterialData D T)
    (hKκ : 0 < Kκ) (hPκ : 0 ≤ Pκ)
    (hlower : ∀ m j : ℕ, Ioo (C.left m) (C.right m) ⊆ D.cells j →
      ∃ κ : ℝ, 0 < κ ∧ κ⁻¹ ≤ Kκ * T.E0 (T.sample j) ^ Pκ ∧
        ∀ r ∈ Ioo (C.left m) (C.right m),
          κ * min (r - C.left m) (C.right m - r) ≤ n01aOpticalRadicand D.w r) :
    ∃ A P : ℕ → ℝ, ∃ Kδ Pδ : ℝ,
      (∀ n, 0 < A n) ∧ (∀ n, 0 ≤ P n) ∧ 0 < Kδ ∧ 0 ≤ Pδ ∧
      ∀ m j : ℕ, Ioo (C.left m) (C.right m) ⊆ D.cells j →
      ∃ κ δ : ℝ, 0 < κ ∧ κ⁻¹ ≤ Kκ * T.E0 (T.sample j) ^ Pκ ∧
        δ = simpleZeroExplicitCollarRadius ((C.right m - C.left m) / 2) κ
          (A 1 * T.E0 (T.sample j) ^ P 1) ∧
        0 < δ ∧ δ ≤ (C.right m - C.left m) / 2 ∧
        δ⁻¹ ≤ Kδ * T.E0 (T.sample j) ^ Pδ ∧
        ∀ rightEnd : Bool, ∃ g : ℝ → ℝ, ContDiff ℝ ∞ g ∧
          (∀ t ∈ Icc (0 : ℝ) (C.right m - C.left m),
            n01aOpticalRadicand D.w
              (inwardComponentPoint (C.left m) (C.right m) rightEnd t) = t * g t) ∧
          κ ≤ g 0 ∧
          (∀ t ∈ Icc (0 : ℝ) δ, κ / 2 ≤ g t ∧ g t ≤ g 0 + κ / 2) ∧
          ∀ n t, t ∈ Icc (0 : ℝ) (C.right m - C.left m) →
            |iteratedDeriv n g t| ≤ A n * T.E0 (T.sample j) ^ P n := by
  obtain ⟨A, P, hA, hP, hdivision⟩ :=
    exists_normalizedOpticalRootDivision_material_family hN.1.1 hT
  obtain ⟨Kρ, Pρ, hKρ, hPρ, hwidth⟩ :=
    hN.component_halfWidth_inverse_material_bound hT
  obtain ⟨C₀, hC₀, hfloor⟩ := material_E0_uniform_scaled_lower hT hN.1.1
  have hC₀pos : 0 < C₀ := zero_lt_one.trans_le hC₀
  let Pδ : ℝ := Pρ + Pκ + P 1
  let Kδ : ℝ := (Kρ + 2 * (A 1 + 1) * Kκ) * C₀ ^ Pδ
  have hPδ : 0 ≤ Pδ := add_nonneg (add_nonneg hPρ hPκ) (hP 1)
  have hAone : 0 < A 1 := hA 1
  have hKδ : 0 < Kδ := by
    dsimp only [Kδ]
    positivity
  refine ⟨A, P, Kδ, Pδ, hA, hP, hKδ, hPδ, ?_⟩
  intro m j hhost
  have hcomp := n01Properties_negativeRadialComponent hN m
  have hρ : 0 < (C.right m - C.left m) / 2 := half_pos (sub_pos.mpr hcomp.2.1)
  have hE : 0 < T.E0 (T.sample j) :=
    (hT.2.1 _ (materialSample_mem_interval hN.1.1 hT j)).2.2.1
  let E := T.E0 (T.sample j)
  have hW : 1 ≤ C₀ * E := hfloor _ (materialSample_mem_interval hN.1.1 hT j)
  have hEW : E ≤ C₀ * E := by
    calc
      E = 1 * E := (one_mul E).symm
      _ ≤ C₀ * E := mul_le_mul_of_nonneg_right hC₀ hE.le
  obtain ⟨κ, hκ, hκinv, hoptical⟩ := hlower m j hhost
  let M := A 1 * E ^ P 1
  have hM : 0 ≤ M := mul_nonneg (hA 1).le (Real.rpow_nonneg hE.le _)
  let δ := simpleZeroExplicitCollarRadius ((C.right m - C.left m) / 2) κ M
  obtain ⟨hδ, hδρ, hδM, hδinv⟩ := simpleZeroExplicitCollarRadius_bounds hρ hκ hM
  have hρW : ((C.right m - C.left m) / 2)⁻¹ ≤ Kρ * (C₀ * E) ^ Pρ :=
    (hwidth m j hhost).trans (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow hE.le hEW hPρ) hKρ.le)
  have hκW : κ⁻¹ ≤ Kκ * (C₀ * E) ^ Pκ :=
    hκinv.trans (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow hE.le hEW hPκ) hKκ.le)
  have hMW : M ≤ A 1 * (C₀ * E) ^ P 1 := mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow hE.le hEW (hP 1)) (hA 1).le
  have hδW : δ⁻¹ ≤ (Kρ + 2 * (A 1 + 1) * Kκ) * (C₀ * E) ^ Pδ :=
    simpleZeroExplicitCollarRadius_inverse_polynomial hW hKρ.le hKκ.le (hA 1).le
      hPρ hPκ (hP 1) hρW hκW hκ hM hMW
  have hδE : δ⁻¹ ≤ Kδ * E ^ Pδ := by
    calc
      δ⁻¹ ≤ (Kρ + 2 * (A 1 + 1) * Kκ) * (C₀ * E) ^ Pδ := hδW
      _ = Kδ * E ^ Pδ := by
        rw [Real.mul_rpow hC₀pos.le hE.le]
        dsimp only [Kδ]
        ring
  refine ⟨κ, δ, hκ, hκinv, rfl, hδ, hδρ, hδE, ?_⟩
  intro rightEnd
  obtain ⟨g, hg, hfactor, hgbound⟩ :=
    hdivision (C.left m) (C.right m) j hcomp hhost rightEnd
  have hg0 : κ ≤ g 0 :=
    normalizedOpticalRootDivision_lower_at_zero hcomp.2.1 rightEnd hg hfactor hoptical
  refine ⟨g, hg, hfactor, hg0, ?_, hgbound⟩
  apply explicit_positive_collar_of_deriv_bound hρ hκ hM hg0
    (fun t _ => hg.differentiable (by simp) t)
  intro t ht
  have htfull : t ∈ Icc (0 : ℝ) (C.right m - C.left m) := by
    refine ⟨ht.1, ?_⟩
    linarith only [ht.2, hcomp.2.1]
  simpa only [iteratedDeriv_one] using hgbound 1 t htfull

end ContinuousFlexibility.Analysis

namespace ContinuousFlexibility.Radial

open Set
open ContinuousFlexibility.Statements ContinuousFlexibility.Analysis
open scoped ContDiff

/-- The same retained reference supplies both the raw optical lower and
the N01 derivative/width inputs. No estimate for the final transport is
assumed and no Through03 certificate is moved to another witness. -/
theorem retainedReference_normalizedOpticalRoot_material_collars
    {S : SelectedTailData} {K : SeedCentralCutoff} {q length : ℝ}
    (R : SeedRetainedPair S K q length) (hS : IsSelectedTail S)
    (hstart : 100 ≤ S.chain.index)
    (hband : radialFrequencyBand S.chain S.Cstar S.chain.index 2) (hq : 0 < q)
    {Γ : ConnectedReferenceGeometry} (hΓ : Γ.Realizes)
    (hw : Γ.reference.w = R.pair.profile) (hcoordinates : R11aRetainedCoordinates R Γ)
    {T : MaterialData} {Sp : PhysicalSpacesData} {C : NonlinearGeometryData Sp}
    {base loss : ℕ} {ε : ℝ} (hT : IsMaterialData Γ.reference T)
    (hN : N01Properties Γ.reference T Sp C base loss ε) :
    ∃ A P : ℕ → ℝ, ∃ Kκ Pκ Kδ Pδ : ℝ,
      (∀ n, 0 < A n) ∧ (∀ n, 0 ≤ P n) ∧ 0 < Kκ ∧ 0 ≤ Pκ ∧ 0 < Kδ ∧ 0 ≤ Pδ ∧
      ∀ m j : ℕ, Ioo (C.left m) (C.right m) ⊆ Γ.reference.cells j →
      ∃ κ δ : ℝ, 0 < κ ∧ κ⁻¹ ≤ Kκ * T.E0 (T.sample j) ^ Pκ ∧
        δ = simpleZeroExplicitCollarRadius ((C.right m - C.left m) / 2) κ
          (A 1 * T.E0 (T.sample j) ^ P 1) ∧
        0 < δ ∧ δ ≤ (C.right m - C.left m) / 2 ∧
        δ⁻¹ ≤ Kδ * T.E0 (T.sample j) ^ Pδ ∧
        ∀ rightEnd : Bool, ∃ g : ℝ → ℝ, ContDiff ℝ ∞ g ∧
          (∀ t ∈ Icc (0 : ℝ) (C.right m - C.left m),
            n01aOpticalRadicand Γ.reference.w
              (inwardComponentPoint (C.left m) (C.right m) rightEnd t) = t * g t) ∧
          κ ≤ g 0 ∧
          (∀ t ∈ Icc (0 : ℝ) δ, κ / 2 ≤ g t ∧ g t ≤ g 0 + κ / 2) ∧
          ∀ n t, t ∈ Icc (0 : ℝ) (C.right m - C.left m) →
            |iteratedDeriv n g t| ≤ A n * T.E0 (T.sample j) ^ P n := by
  obtain ⟨Kκ, Pκ, hKκ, hPκ, hlower⟩ :=
    retainedReference_uniform_optical_envelope R hS hstart hband hq hΓ hw hcoordinates hT
  obtain ⟨A, P, Kδ, Pδ, hA, hP, hKδ, hPδ, hresult⟩ :=
    normalizedOpticalRoot_material_collars_of_lower hN hT hKκ hPκ
      (fun m j hhost => hlower _ _ j (n01Properties_negativeRadialComponent hN m) hhost)
  exact ⟨A, P, Kκ, Pκ, Kδ, Pδ, hA, hP, hKκ, hPκ, hKδ, hPδ, hresult⟩

end ContinuousFlexibility.Radial
