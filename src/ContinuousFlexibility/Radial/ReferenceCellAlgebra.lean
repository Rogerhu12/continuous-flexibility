import ContinuousFlexibility.Radial.ReferenceCellL2
import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.Topology.Algebra.InfiniteSum.Ring

/-!
# Algebra of the actual reference spaces

The cell-square estimates use the genuine two-dimensional square integral.
They therefore retain the measurability and integrability conditions needed by
the Bochner integral.
-/

namespace ContinuousFlexibility.Statements

open Set MeasureTheory Filter

theorem radialAngularMean_const_mul (c : ℝ) (f : ℝ → ℝ) :
    radialAngularMean (fun θ => c * f θ) = c * radialAngularMean f := by
  unfold radialAngularMean
  rw [intervalIntegral.integral_const_mul]
  ring

theorem referenceCellSquare_const_mul (D : ReferenceData) (m : ℕ)
    (c : ℝ) (f : PolarPoint → ℝ) :
    referenceCellSquare D m (fun x => c * f x) = c ^ 2 * referenceCellSquare D m f := by
  unfold referenceCellSquare
  have heq :
      (fun r => radialAngularMean
        (fun θ => (D.localizer m r * (c * f (r, θ))) ^ 2)) =
      fun r => c ^ 2 * radialAngularMean
        (fun θ => (D.localizer m r * f (r, θ)) ^ 2) := by
    funext r
    have hpoint :
        (fun θ : ℝ => (D.localizer m r * (c * f (r, θ))) ^ 2) =
        fun θ => c ^ 2 * (D.localizer m r * f (r, θ)) ^ 2 := by
      funext θ
      ring
    rw [hpoint, radialAngularMean_const_mul]
  rw [heq, intervalIntegral.integral_const_mul]

theorem sourceCellSquare_const_mul (D : ReferenceData) (γ M c : ℝ)
    (f : PolarPoint → ℝ) (m : ℕ) :
    sourceCellSquare D γ M (fun x => c * f x) m =
      c ^ 2 * sourceCellSquare D γ M f m := by
  unfold sourceCellSquare
  rw [referenceCellSquare_const_mul]
  ring

theorem outputCellSquare_const_mul (D : ReferenceData) (γ M c : ℝ)
    (f : PolarPoint → ℝ) (m : ℕ) :
    outputCellSquare D γ M (fun x => c * f x) m =
      c ^ 2 * outputCellSquare D γ M f m := by
  unfold outputCellSquare
  rw [referenceCellSquare_const_mul]
  ring

theorem referenceCellSquare_add_le {D : ReferenceData} (hab : D.a ≤ D.b)
    (m : ℕ) {f g : PolarPoint → ℝ}
    (hf : RadialCellIntegrable D f) (hg : RadialCellIntegrable D g) :
    referenceCellSquare D m (fun x => f x + g x) ≤
      2 * (referenceCellSquare D m f + referenceCellSquare D m g) := by
  have hbound :
      (∫ x, (D.localizer m x.1 * (f x + g x)) ^ 2 ∂radialPhysicalMeasure D) ≤
      ∫ x, 2 * ((D.localizer m x.1 * f x) ^ 2 +
        (D.localizer m x.1 * g x) ^ 2) ∂radialPhysicalMeasure D := by
    refine integral_mono ((hf.add hg) m).integrable_sq
      (((hf m).integrable_sq.add (hg m).integrable_sq).const_mul 2) ?_
    intro x
    nlinarith [sq_nonneg (D.localizer m x.1 * f x - D.localizer m x.1 * g x)]
  rw [integral_const_mul, integral_add (hf m).integrable_sq
    (hg m).integrable_sq] at hbound
  rw [referenceCellSquare_eq_integral hab m (hf.add hg),
    referenceCellSquare_eq_integral hab m hf,
    referenceCellSquare_eq_integral hab m hg]
  calc
    _ ≤ (2 * Real.pi)⁻¹ *
        (2 * ((∫ x, (D.localizer m x.1 * f x) ^ 2 ∂radialPhysicalMeasure D) +
          ∫ x, (D.localizer m x.1 * g x) ^ 2 ∂radialPhysicalMeasure D)) :=
      mul_le_mul_of_nonneg_left hbound (by positivity)
    _ = _ := by ring

theorem sourceCellSquare_add_le {D : ReferenceData} (hab : D.a ≤ D.b)
    (γ M : ℝ) (m : ℕ) {f g : PolarPoint → ℝ}
    (hf : RadialCellIntegrable D f) (hg : RadialCellIntegrable D g) :
    sourceCellSquare D γ M (fun x => f x + g x) m ≤
      2 * (sourceCellSquare D γ M f m + sourceCellSquare D γ M g m) := by
  unfold sourceCellSquare
  calc
    _ ≤ Real.exp (2 * M * radialQ (D.cellIndex m) +
        2 * γ * radialS (D.cellIndex m)) *
          (2 * (referenceCellSquare D m f + referenceCellSquare D m g)) :=
      mul_le_mul_of_nonneg_left (referenceCellSquare_add_le hab m hf hg)
        (Real.exp_pos _).le
    _ = _ := by ring

theorem outputCellSquare_add_le {D : ReferenceData} (hab : D.a ≤ D.b)
    (γ M : ℝ) (m : ℕ) {f g : PolarPoint → ℝ}
    (hf : RadialCellIntegrable D f) (hg : RadialCellIntegrable D g) :
    outputCellSquare D γ M (fun x => f x + g x) m ≤
      2 * (outputCellSquare D γ M f m + outputCellSquare D γ M g m) := by
  unfold outputCellSquare
  calc
    _ ≤ Real.exp (-2 * M * radialQ (D.cellIndex m) +
        2 * γ * radialS (D.cellIndex m)) *
          (2 * (referenceCellSquare D m f + referenceCellSquare D m g)) :=
      mul_le_mul_of_nonneg_left (referenceCellSquare_add_le hab m hf hg)
        (Real.exp_pos _).le
    _ = _ := by ring

theorem sourceCellSquare_summable_const_mul {D : ReferenceData} {γ M : ℝ}
    {f : PolarPoint → ℝ} (hs : Summable (sourceCellSquare D γ M f)) (c : ℝ) :
    Summable (sourceCellSquare D γ M (fun x => c * f x)) := by
  have heq : sourceCellSquare D γ M (fun x => c * f x) =
      fun m => c ^ 2 * sourceCellSquare D γ M f m := by
    funext m
    exact sourceCellSquare_const_mul D γ M c f m
  rw [heq]
  exact Summable.mul_left (c ^ 2) hs

theorem outputCellSquare_summable_const_mul {D : ReferenceData} {γ M : ℝ}
    {f : PolarPoint → ℝ} (hs : Summable (outputCellSquare D γ M f)) (c : ℝ) :
    Summable (outputCellSquare D γ M (fun x => c * f x)) := by
  have heq : outputCellSquare D γ M (fun x => c * f x) =
      fun m => c ^ 2 * outputCellSquare D γ M f m := by
    funext m
    exact outputCellSquare_const_mul D γ M c f m
  rw [heq]
  exact Summable.mul_left (c ^ 2) hs

theorem sourceCellSquare_summable_add {D : ReferenceData} (hab : D.a ≤ D.b)
    {γ M : ℝ} {f g : PolarPoint → ℝ}
    (hf : RadialCellIntegrable D f) (hg : RadialCellIntegrable D g)
    (hsf : Summable (sourceCellSquare D γ M f))
    (hsg : Summable (sourceCellSquare D γ M g)) :
    Summable (sourceCellSquare D γ M (fun x => f x + g x)) := by
  apply (Summable.mul_left 2 (hsf.add hsg)).of_norm_bounded
  intro m
  rw [Real.norm_of_nonneg (sourceCellSquare_nonneg hab γ M (hf.add hg) m)]
  exact sourceCellSquare_add_le hab γ M m hf hg

theorem outputCellSquare_summable_add {D : ReferenceData} (hab : D.a ≤ D.b)
    {γ M : ℝ} {f g : PolarPoint → ℝ}
    (hf : RadialCellIntegrable D f) (hg : RadialCellIntegrable D g)
    (hsf : Summable (outputCellSquare D γ M f))
    (hsg : Summable (outputCellSquare D γ M g)) :
    Summable (outputCellSquare D γ M (fun x => f x + g x)) := by
  apply (Summable.mul_left 2 (hsf.add hsg)).of_norm_bounded
  intro m
  rw [Real.norm_of_nonneg (outputCellSquare_nonneg hab γ M (hf.add hg) m)]
  exact outputCellSquare_add_le hab γ M m hf hg

theorem outputRemainder_add (D : ReferenceData) (aL bL : ℝ) (U V : RadialUnknown) :
    outputRemainder D (aL + bL) (U + V) =
      fun x => outputRemainder D aL U x + outputRemainder D bL V x := by
  funext x
  change U.1 x + V.1 x - (aL + bL) * D.chiLeft x.1 =
    (U.1 x - aL * D.chiLeft x.1) + (V.1 x - bL * D.chiLeft x.1)
  ring

theorem outputRemainder_smul (D : ReferenceData) (aL c : ℝ) (U : RadialUnknown) :
    outputRemainder D (c * aL) (c • U) =
      fun x => c * outputRemainder D aL U x := by
  funext x
  change c * U.1 x - (c * aL) * D.chiLeft x.1 =
    c * (U.1 x - aL * D.chiLeft x.1)
  ring

theorem OutputRealization.add {D : ReferenceData} (hab : D.a ≤ D.b)
    {γ M aL bL : ℝ} {U V : RadialUnknown}
    (hU : OutputRealization D γ M aL U) (hV : OutputRealization D γ M bL V) :
    OutputRealization D γ M (aL + bL) (U + V) := by
  rcases hU with ⟨hUl, hUs, hUp, hUe⟩
  rcases hV with ⟨hVl, hVs, hVp, hVe⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [outputRemainder_add]
    exact hUl.add hVl
  · rw [outputRemainder_add]
    exact outputCellSquare_summable_add hab hUl hVl hUs hVs
  · intro x
    change U.1 (x + (0, Real.pi)) + V.1 (x + (0, Real.pi)) = U.1 x + V.1 x
    rw [hUp x, hVp x]
  · intro r θ
    change U.1 (r, -θ) + V.1 (r, -θ) = U.1 (r, θ) + V.1 (r, θ)
    rw [hUe r θ, hVe r θ]

theorem OutputRealization.smul {D : ReferenceData} {γ M aL : ℝ} {U : RadialUnknown}
    (hU : OutputRealization D γ M aL U) (c : ℝ) :
    OutputRealization D γ M (c * aL) (c • U) := by
  rcases hU with ⟨hUl, hUs, hUp, hUe⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [outputRemainder_smul]
    exact hUl.const_mul c
  · rw [outputRemainder_smul]
    exact outputCellSquare_summable_const_mul hUs c
  · intro x
    change c * U.1 (x + (0, Real.pi)) = c * U.1 x
    rw [hUp x]
  · intro r θ
    change c * U.1 (r, -θ) = c * U.1 (r, θ)
    rw [hUe r θ]

theorem OutputMember.add {D : ReferenceData} (hab : D.a ≤ D.b)
    {γ M : ℝ} {U V : RadialUnknown}
    (hU : OutputMember D γ M U) (hV : OutputMember D γ M V) :
    OutputMember D γ M (U + V) := by
  obtain ⟨aL, hU⟩ := hU
  obtain ⟨bL, hV⟩ := hV
  exact ⟨aL + bL, OutputRealization.add hab hU hV⟩

theorem OutputMember.smul {D : ReferenceData} {γ M : ℝ} {U : RadialUnknown}
    (hU : OutputMember D γ M U) (c : ℝ) :
    OutputMember D γ M (c • U) := by
  obtain ⟨aL, hU⟩ := hU
  exact ⟨c * aL, hU.smul c⟩

theorem SourceMember.smul {D : ReferenceData} {γ M : ℝ} {F : RadialSource}
    (hF : SourceMember D γ M F) (c : ℝ) :
    SourceMember D γ M (c • F) := by
  rcases hF with ⟨hFl, hFs, hFp, hFe, hFm, hF0⟩
  change SourceMember D γ M ((fun x => c * F.1 x), c * F.2)
  refine ⟨hFl.const_mul c, sourceCellSquare_summable_const_mul hFs c, ?_, ?_, ?_, ?_⟩
  · intro x
    change c * F.1 (x + (0, Real.pi)) = c * F.1 x
    rw [hFp x]
  · intro r θ
    change c * F.1 (r, -θ) = c * F.1 (r, θ)
    rw [hFe r θ]
  · simpa only [radialAngularMean_const_mul] using hFm.const_mul c
  · simp only [radialAngularMean_const_mul, intervalIntegral.integral_const_mul,
      hF0, mul_zero]


/-- Local `L²` membership and the partition of unity give integrable angular
sections for almost every physical radius. -/
theorem RadialCellIntegrable.ae_angular_intervalIntegrable
    {D : ReferenceData} {f : PolarPoint → ℝ}
    (hf : RadialCellIntegrable D f) (hD : RadialPartition D) :
    ∀ᵐ r ∂volume.restrict (radialCore D),
      IntervalIntegrable (fun θ => f (r, θ)) volume 0 (2 * Real.pi) := by
  letI : IsFiniteMeasure (radialPhysicalMeasure D) := by
    rw [radialPhysicalMeasure_eq_prod]
    dsimp only [radialCore]
    infer_instance
  have hslice (m : ℕ) :
      ∀ᵐ r ∂volume.restrict (radialCore D),
        Integrable (fun θ => D.localizer m r * f (r, θ))
          (volume.restrict (Ioc (0 : ℝ) (2 * Real.pi))) := by
    have hi : Integrable (fun x : PolarPoint => D.localizer m x.1 * f x)
        ((volume.restrict (radialCore D)).prod
          (volume.restrict (Ioc (0 : ℝ) (2 * Real.pi)))) := by
      rw [← radialPhysicalMeasure_eq_prod]
      exact MemLp.integrable (show (1 : ℝ≥0∞) ≤ 2 by norm_num) (hf m)
    exact hi.prod_right_ae
  have hall :
      ∀ᵐ r ∂volume.restrict (radialCore D), ∀ m : ℕ,
        Integrable (fun θ => D.localizer m r * f (r, θ))
          (volume.restrict (Ioc (0 : ℝ) (2 * Real.pi))) :=
    ae_all_iff.2 hslice
  have hmem : ∀ᵐ r ∂volume.restrict (radialCore D), r ∈ radialCore D :=
    ae_restrict_mem measurableSet_Ioo
  filter_upwards [hall, hmem] with r hr hrmem
  have hnonzero : ∃ m : ℕ, D.localizer m r ≠ 0 := by
    by_contra h
    have hz : ∀ m : ℕ, D.localizer m r = 0 := by
      intro m
      by_contra hm
      exact h ⟨m, hm⟩
    have hsum : (∑' m : ℕ, D.localizer m r) = 0 := by
      simp only [hz, tsum_zero]
    exact zero_ne_one (hsum.symm.trans (hD.2.2.2.2.1 r hrmem).2)
  obtain ⟨m, hm⟩ := hnonzero
  apply (intervalIntegrable_iff_integrableOn_Ioc_of_le
    (show (0 : ℝ) ≤ 2 * Real.pi by positivity)).2
  simpa only [← mul_assoc, inv_mul_cancel₀ hm, one_mul] using
    (hr m).const_mul ((D.localizer m r)⁻¹)

/-- Angular averaging is additive almost everywhere on the annulus.
The slice integrability hypotheses are obtained from actual local `L²`. -/
theorem radialAngularMean_add_ae {D : ReferenceData} (hD : RadialPartition D)
    {f g : PolarPoint → ℝ}
    (hf : RadialCellIntegrable D f) (hg : RadialCellIntegrable D g) :
    (fun r => radialAngularMean (fun θ => f (r, θ) + g (r, θ))) =ᵐ[volume.restrict (radialCore D)]
        (fun r => radialAngularMean (fun θ => f (r, θ)) +
          radialAngularMean (fun θ => g (r, θ))) := by
  filter_upwards [hf.ae_angular_intervalIntegrable hD,
    hg.ae_angular_intervalIntegrable hD] with r hfr hgr
  unfold radialAngularMean
  rw [intervalIntegral.integral_add hfr hgr]
  ring

theorem SourceMember.add {D : ReferenceData} (hab : D.a ≤ D.b)
    (hD : RadialPartition D) {γ M : ℝ} {F G : RadialSource}
    (hF : SourceMember D γ M F) (hG : SourceMember D γ M G) :
    SourceMember D γ M (F + G) := by
  rcases hF with ⟨hFl, hFs, hFp, hFe, hFm, hF0⟩
  rcases hG with ⟨hGl, hGs, hGp, hGe, hGm, hG0⟩
  have hmean :
      (fun r => radialAngularMean (fun θ => F.1 (r, θ) + G.1 (r, θ))) =ᵐ[volume.restrict (uIoc D.a D.b)]
          (fun r => radialAngularMean (fun θ => F.1 (r, θ)) +
            radialAngularMean (fun θ => G.1 (r, θ))) := by
    rw [uIoc_of_le hab, ← restrict_Ioo_eq_restrict_Ioc]
    exact radialAngularMean_add_ae hD hFl hGl
  change SourceMember D γ M ((fun x => F.1 x + G.1 x), F.2 + G.2)
  refine ⟨hFl.add hGl, sourceCellSquare_summable_add hab hFl hGl hFs hGs,
    ?_, ?_, ?_, ?_⟩
  · intro x
    change F.1 (x + (0, Real.pi)) + G.1 (x + (0, Real.pi)) = F.1 x + G.1 x
    rw [hFp x, hGp x]
  · intro r θ
    change F.1 (r, -θ) + G.1 (r, -θ) = F.1 (r, θ) + G.1 (r, θ)
    rw [hFe r θ, hGe r θ]
  · exact (hFm.add hGm).congr_ae hmean.symm
  · change (∫ r in D.a..D.b,
      radialAngularMean (fun θ => F.1 (r, θ) + G.1 (r, θ))) = 0
    rw [intervalIntegral.integral_congr_ae_restrict hmean,
      intervalIntegral.integral_add hFm hGm, hF0, hG0, add_zero]

end ContinuousFlexibility.Statements
