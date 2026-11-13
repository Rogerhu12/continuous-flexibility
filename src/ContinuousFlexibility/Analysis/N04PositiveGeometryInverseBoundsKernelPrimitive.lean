import ContinuousFlexibility.Analysis.N04PositiveGeometryInverseBoundsKernelSlope

/-!
# Uniform jets of the literal finite coefficient radial collar

Rescaling only the integration variable rewrites the original moving
primitive as an integral over the fixed unit interval.  The full
coefficient and radial jets then follow from the preceding slope bounds.
Their constants depend on the common scalar envelopes, not on the
component, coefficient vector, or evaluation point.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set
open scoped ContDiff BigOperators Interval

theorem n04PositiveGeometry_scalarCollarKernel_unit_integral
    (n : ℕ) (l r δ : ℝ) (root : Bool) (p : (Fin (n + 1) → ℝ) × ℝ) :
    n04PositiveGeometry_scalarCollarKernel n l r δ root p =
      l + (r - l) * ((p.2 - l) * ∫ s in (0 : ℝ)..1,
        n04PositiveGeometry_collarNormalizedSlope n l r δ root p.1
          ((p.2 - l) * s + l)) := by
  rw [n04PositiveGeometry_scalarCollarKernel_formula]
  have he := intervalIntegral.smul_integral_comp_mul_add
    (n04PositiveGeometry_collarNormalizedSlope n l r δ root p.1)
    (a := (0 : ℝ)) (b := 1) (p.2 - l) l
  have he' : (p.2 - l) * (∫ s in (0 : ℝ)..1,
      n04PositiveGeometry_collarNormalizedSlope n l r δ root p.1 ((p.2 - l) * s + l)) =
      ∫ t in l..p.2, n04PositiveGeometry_collarNormalizedSlope n l r δ root p.1 t := by
    simpa only [smul_eq_mul, mul_zero, zero_add, mul_one, sub_add_cancel] using he
  rw [he']
  rfl

/-- Every ordinary coefficient/radial jet of the actual collar has a
single component polynomial envelope.  The evaluation radius need only
have such an envelope; in the atlas it lies in the fixed physical annulus. -/
theorem n04PositiveGeometry_scalarCollarKernel_bounds
    {I : Type} {W : I → ℝ} (hW : ∀ i, 1 ≤ W i) (n : ℕ) (root : Bool)
    (p : I → (Fin (n + 1) → ℝ) × ℝ) (l r δ : I → ℝ)
    (hp : HasPositiveEnvelope W (fun i => ‖p i‖))
    (hl : HasPositiveEnvelope W (fun i => |l i|))
    (hr : HasPositiveEnvelope W (fun i => |r i|))
    (hδ : HasPositiveEnvelope W (fun i => |(δ i)⁻¹|))
    (hspan : HasPositiveEnvelope W (fun i => |(r i - l i)⁻¹|))
    (hmiddle : HasPositiveEnvelope W
      (fun i => |(positiveReferenceMiddleMass (l i) (r i) (δ i))⁻¹|)) :
    N04PositiveKernelJetBounds W p
      (fun i => n04PositiveGeometry_scalarCollarKernel n (l i) (r i) (δ i) root) := by
  let P := Fin (n + 1) → ℝ
  let E := P × ℝ
  let J := {z : I × ℝ // z.2 ∈ uIcc (0 : ℝ) 1}
  let e : J → I := fun z => z.1.1
  let q : J → E × ℝ := fun z => (p (e z), z.1.2)
  have hW' (z : J) : 1 ≤ W (e z) := hW (e z)
  have hq : HasPositiveEnvelope (fun z : J => W (e z)) (fun z => ‖q z‖) := by
    apply ((n04PositiveGeometry_envelope_reindex hp e).add hW'
      (hasPositiveEnvelope_const (fun z => W (e z)) hW' 1)).mono
    intro z
    have hs : |z.1.2| ≤ 1 := by
      simpa only [sub_zero, abs_one] using abs_sub_left_of_mem_uIcc z.2
    rw [Prod.norm_def, Real.norm_eq_abs]
    exact max_le (le_add_of_nonneg_right zero_le_one)
      (hs.trans (le_add_of_nonneg_left (norm_nonneg _)))
  have ha (j : Fin (n + 1)) : N04PositiveKernelJetBounds
      (fun z : J => W (e z)) q (fun (_ : J) (y : E × ℝ) => y.1.1 j) := by
    let L : (E × ℝ) →L[ℝ] ℝ := (ContinuousLinearMap.proj j).comp
      ((ContinuousLinearMap.fst ℝ P ℝ).comp (ContinuousLinearMap.fst ℝ E ℝ))
    apply (N04PositiveKernelJetBounds.linear hW' L hq).congr
    intro z
    funext y
    simp only [L, ContinuousLinearMap.comp_apply, ContinuousLinearMap.coe_fst',
      ContinuousLinearMap.proj_apply]
  have hx : N04PositiveKernelJetBounds (fun z : J => W (e z)) q
      (fun (_ : J) (y : E × ℝ) => y.1.2) := by
    let L : (E × ℝ) →L[ℝ] ℝ :=
      (ContinuousLinearMap.snd ℝ P ℝ).comp (ContinuousLinearMap.fst ℝ E ℝ)
    apply (N04PositiveKernelJetBounds.linear hW' L hq).congr
    intro z
    funext y
    simp only [L, ContinuousLinearMap.comp_apply, ContinuousLinearMap.coe_fst',
      ContinuousLinearMap.coe_snd']
  have hs : N04PositiveKernelJetBounds (fun z : J => W (e z)) q
      (fun (_ : J) (y : E × ℝ) => y.2) :=
    N04PositiveKernelJetBounds.linear hW' (ContinuousLinearMap.snd ℝ E ℝ) hq
  have hbase := N04PositiveKernelJetBounds.const (p := q) hW' (fun z => l (e z))
    (n04PositiveGeometry_envelope_reindex hl e)
  have ht := ((hx.sub hbase hW').mul hs hW').add hbase hW'
  let F : I → E × ℝ → ℝ := fun i y => n04PositiveGeometry_collarNormalizedSlope n
    (l i) (r i) (δ i) root y.1.1 ((y.1.2 - l i) * y.2 + l i)
  have hF := n04PositiveGeometry_collarNormalizedSlope_bounds (p := q) hW' n root
    (fun (_ : J) (y : E × ℝ) => y.1.1)
    (fun (z : J) (y : E × ℝ) => (y.1.2 - l (e z)) * y.2 + l (e z))
    (fun z => l (e z)) (fun z => r (e z)) (fun z => δ (e z)) ha ht hq
    (n04PositiveGeometry_envelope_reindex hl e)
    (n04PositiveGeometry_envelope_reindex hr e)
    (n04PositiveGeometry_envelope_reindex hδ e)
    (n04PositiveGeometry_envelope_reindex hspan e)
    (n04PositiveGeometry_envelope_reindex hmiddle e)
  have hlength : HasPositiveEnvelope W (fun _ => |(1 : ℝ) - 0|) :=
    hasPositiveEnvelope_const W hW |(1 : ℝ) - 0|
  have hI := n04PositiveGeometry_kernel_intervalIntegral_bounds hW p
    (fun _ => 0) (fun _ => 1) F
    (fun i => hF.smooth ⟨(i, 0), left_mem_uIcc⟩) hlength hF
  have hL := N04PositiveKernelJetBounds.const (p := p) hW l hl
  have hspanValue : HasPositiveEnvelope W (fun i => |r i - l i|) :=
    (hr.add hW hl).mono (fun _ => abs_sub _ _)
  have hM := N04PositiveKernelJetBounds.const (p := p) hW
    (fun i => r i - l i) hspanValue
  have hR : N04PositiveKernelJetBounds W p (fun (_ : I) (y : E) => y.2) :=
    N04PositiveKernelJetBounds.linear hW (ContinuousLinearMap.snd ℝ P ℝ) hp
  have hprimitive := hL.add (hM.mul ((hR.sub hL hW).mul hI hW) hW) hW
  apply hprimitive.congr
  intro i
  funext y
  exact (n04PositiveGeometry_scalarCollarKernel_unit_integral n (l i) (r i)
    (δ i) root y).symm

end ContinuousFlexibility.Analysis
