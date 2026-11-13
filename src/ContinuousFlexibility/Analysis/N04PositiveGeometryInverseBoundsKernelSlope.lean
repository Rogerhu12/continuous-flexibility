import ContinuousFlexibility.Analysis.N04PositiveGeometryInverseBoundsKernelFormula

/-!
# Uniform coefficient jets of the actual normalized radial slope

The only scalar costs are the endpoints, selected width, physical mass
and fixed middle mass.  The finite Taylor fields, endpoint cutoffs and
normalizing integral are the original displayed formulas.  All constants
are uniform in the component and coefficient vector.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set
open scoped ContDiff BigOperators Interval

theorem n04PositiveGeometry_envelope_reindex
    {I J : Type*} {W f : I → ℝ} (h : HasPositiveEnvelope W f) (e : J → I) :
    HasPositiveEnvelope (fun j => W (e j)) (fun j => f (e j)) := by
  obtain ⟨C, A, hC, hA, hb⟩ := h
  exact ⟨C, A, hC, hA, fun j => hb (e j)⟩

section ScalarAlgebra

variable {I E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {W : I → ℝ} {p : I → E}

theorem n04PositiveGeometry_endpointCutoffKernel_bounds
    (hW : ∀ i, 1 ≤ W i) (t : I → E → ℝ) (c δ : I → ℝ)
    (ht : N04PositiveKernelJetBounds W p t)
    (hc : HasPositiveEnvelope W (fun i => |c i|))
    (hδ : HasPositiveEnvelope W (fun i => |(δ i)⁻¹|)) :
    N04PositiveKernelJetBounds W p
      (fun i y => positiveEndpointCutoff (c i) (δ i) (t i y)) := by
  have hshift := ht.sub (N04PositiveKernelJetBounds.const (p := p) hW c hc) hW
  have hscaled := hshift.mul
    (N04PositiveKernelJetBounds.const (p := p) hW (fun i => (δ i)⁻¹) hδ) hW
  simpa only [positiveEndpointCutoff, div_eq_mul_inv] using hscaled.cutoff hW

def n04PositiveGeometry_collarEndpointSlopeSum (n : ℕ)
    (l r δ : ℝ) (root : Bool) (a : Fin (n + 1) → ℝ) (t : ℝ) : ℝ :=
  positiveEndpointCutoff l δ t *
      (n04PositiveGeometry_collarSlopeKernel n l r root a false t / (r - l)) +
    positiveEndpointCutoff r δ t *
      (n04PositiveGeometry_collarSlopeKernel n l r root a true t / (r - l))

theorem n04PositiveGeometry_collarEndpointSlopeSum_bounds
    (hW : ∀ i, 1 ≤ W i) (n : ℕ) (root : Bool)
    (a : I → E → Fin (n + 1) → ℝ) (t : I → E → ℝ) (l r δ : I → ℝ)
    (ha : ∀ j, N04PositiveKernelJetBounds W p (fun i y => a i y j))
    (ht : N04PositiveKernelJetBounds W p t)
    (hl : HasPositiveEnvelope W (fun i => |l i|))
    (hr : HasPositiveEnvelope W (fun i => |r i|))
    (hδ : HasPositiveEnvelope W (fun i => |(δ i)⁻¹|))
    (hspan : HasPositiveEnvelope W (fun i => |(r i - l i)⁻¹|)) :
    N04PositiveKernelJetBounds W p
      (fun i y => n04PositiveGeometry_collarEndpointSlopeSum n
        (l i) (r i) (δ i) root (a i y) (t i y)) := by
  have hleft := n04PositiveGeometry_endpointCutoffKernel_bounds hW t l δ ht hl hδ
  have hright := n04PositiveGeometry_endpointCutoffKernel_bounds hW t r δ ht hr hδ
  have hm := N04PositiveKernelJetBounds.const (p := p) hW
    (fun i => (r i - l i)⁻¹) hspan
  have hS (side : Bool) := n04PositiveGeometry_collarSlopeKernel_bounds hW n root side
    a t l r ha ht hl hr
  simpa only [n04PositiveGeometry_collarEndpointSlopeSum, div_eq_mul_inv] using
    (hleft.mul ((hS false).mul hm hW) hW).add
      (hright.mul ((hS true).mul hm hW) hW) hW

end ScalarAlgebra

/-- The actual fixed normalization integral has uniform coefficient jets.
No derivative of the integration endpoints is introduced: they were
selected before the coefficient vector. -/
theorem n04PositiveGeometry_collarEndMass_bounds
    {I E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [ProperSpace E]
    {W : I → ℝ} {p : I → E}
    (hW : ∀ i, 1 ≤ W i) (n : ℕ) (root : Bool)
    (a : I → E → Fin (n + 1) → ℝ) (l r δ : I → ℝ)
    (ha : ∀ j, N04PositiveKernelJetBounds W p (fun i y => a i y j))
    (hp : HasPositiveEnvelope W (fun i => ‖p i‖))
    (hl : HasPositiveEnvelope W (fun i => |l i|))
    (hr : HasPositiveEnvelope W (fun i => |r i|))
    (hδ : HasPositiveEnvelope W (fun i => |(δ i)⁻¹|))
    (hspan : HasPositiveEnvelope W (fun i => |(r i - l i)⁻¹|)) :
    N04PositiveKernelJetBounds W p
      (fun i y => ∫ s in l i..r i,
        n04PositiveGeometry_collarEndpointSlopeSum n (l i) (r i) (δ i) root (a i y) s) := by
  let J := {z : I × ℝ // z.2 ∈ uIcc (l z.1) (r z.1)}
  let e : J → I := fun z => z.1.1
  let q : J → E × ℝ := fun z => (p (e z), z.1.2)
  have hW' (z : J) : 1 ≤ W (e z) := hW (e z)
  have hlength : HasPositiveEnvelope W (fun i => |r i - l i|) :=
    (hr.add hW hl).mono (fun _ => abs_sub _ _)
  have hq : HasPositiveEnvelope (fun z : J => W (e z)) (fun z => ‖q z‖) := by
    have h := (n04PositiveGeometry_envelope_reindex hp e).add hW'
      ((n04PositiveGeometry_envelope_reindex hlength e).add hW'
        (n04PositiveGeometry_envelope_reindex hl e))
    apply h.mono
    intro z
    have hs : |z.1.2| ≤ |r (e z) - l (e z)| + |l (e z)| := by
      calc
        _ = |(z.1.2 - l (e z)) + l (e z)| := by rw [sub_add_cancel]
        _ ≤ |z.1.2 - l (e z)| + |l (e z)| := abs_add_le _ _
        _ ≤ _ := add_le_add_right (abs_sub_left_of_mem_uIcc z.2) _
    rw [Prod.norm_def, Real.norm_eq_abs]
    exact max_le (le_add_of_nonneg_right (by positivity))
      (hs.trans (le_add_of_nonneg_left (norm_nonneg _)))
  let L : (E × ℝ) →L[ℝ] E := ContinuousLinearMap.fst ℝ E ℝ
  have ha' (j : Fin (n + 1)) : N04PositiveKernelJetBounds
      (fun z : J => W (e z)) q (fun z y => a (e z) y.1 j) :=
    ((ha j).reindex e).precompLinear hW' L q (fun _ => rfl)
  have ht : N04PositiveKernelJetBounds (fun z : J => W (e z)) q
      (fun (_ : J) (y : E × ℝ) => y.2) :=
    N04PositiveKernelJetBounds.linear hW' (ContinuousLinearMap.snd ℝ E ℝ) hq
  let F : I → E × ℝ → ℝ := fun i y => n04PositiveGeometry_collarEndpointSlopeSum n
    (l i) (r i) (δ i) root (a i y.1) y.2
  have hF := n04PositiveGeometry_collarEndpointSlopeSum_bounds (p := q) hW' n root
    (fun (z : J) (y : E × ℝ) => a (e z) y.1) (fun (_ : J) (y : E × ℝ) => y.2)
    (fun z => l (e z)) (fun z => r (e z)) (fun z => δ (e z)) ha' ht
    (n04PositiveGeometry_envelope_reindex hl e) (n04PositiveGeometry_envelope_reindex hr e)
    (n04PositiveGeometry_envelope_reindex hδ e) (n04PositiveGeometry_envelope_reindex hspan e)
  exact n04PositiveGeometry_kernel_intervalIntegral_bounds hW p l r F
    (fun i => hF.smooth ⟨(i, l i), left_mem_uIcc⟩) hlength hF

def n04PositiveGeometry_collarNormalizedSlope (n : ℕ)
    (l r δ : ℝ) (root : Bool) (a : Fin (n + 1) → ℝ) (t : ℝ) : ℝ :=
  positiveReferenceSlope l r δ
    (fun s => n04PositiveGeometry_collarSlopeKernel n l r root a false s / (r - l))
    (fun s => n04PositiveGeometry_collarSlopeKernel n l r root a true s / (r - l)) t

/-- The complete normalized slope, including its actual mass integral,
has polynomial bounds for every coefficient and radial derivative. -/
theorem n04PositiveGeometry_collarNormalizedSlope_bounds
    {I E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [ProperSpace E]
    {W : I → ℝ} {p : I → E}
    (hW : ∀ i, 1 ≤ W i) (n : ℕ) (root : Bool)
    (a : I → E → Fin (n + 1) → ℝ) (t : I → E → ℝ) (l r δ : I → ℝ)
    (ha : ∀ j, N04PositiveKernelJetBounds W p (fun i y => a i y j))
    (ht : N04PositiveKernelJetBounds W p t)
    (hp : HasPositiveEnvelope W (fun i => ‖p i‖))
    (hl : HasPositiveEnvelope W (fun i => |l i|))
    (hr : HasPositiveEnvelope W (fun i => |r i|))
    (hδ : HasPositiveEnvelope W (fun i => |(δ i)⁻¹|))
    (hspan : HasPositiveEnvelope W (fun i => |(r i - l i)⁻¹|))
    (hmiddle : HasPositiveEnvelope W
      (fun i => |(positiveReferenceMiddleMass (l i) (r i) (δ i))⁻¹|)) :
    N04PositiveKernelJetBounds W p
      (fun i y => n04PositiveGeometry_collarNormalizedSlope n
        (l i) (r i) (δ i) root (a i y) (t i y)) := by
  have hend := n04PositiveGeometry_collarEndpointSlopeSum_bounds hW n root
    a t l r δ ha ht hl hr hδ hspan
  have hmass := n04PositiveGeometry_collarEndMass_bounds hW n root a l r δ
    ha hp hl hr hδ hspan
  have hone := N04PositiveKernelJetBounds.const (p := p) hW (fun _ => 1)
    (by simpa only [abs_one] using hasPositiveEnvelope_const W hW 1)
  have hdenom := N04PositiveKernelJetBounds.const (p := p) hW
    (fun i => (positiveReferenceMiddleMass (l i) (r i) (δ i))⁻¹) hmiddle
  have hscale := (hone.sub hmass hW).mul hdenom hW
  have hleft := n04PositiveGeometry_endpointCutoffKernel_bounds hW t l δ ht hl hδ
  have hright := n04PositiveGeometry_endpointCutoffKernel_bounds hW t r δ ht hr hδ
  have hweight := (hone.sub hleft hW).sub hright hW
  simpa only [n04PositiveGeometry_collarNormalizedSlope, positiveReferenceSlope,
    positiveReferenceScale, positiveReferenceEndMass,
    n04PositiveGeometry_collarEndpointSlopeSum, div_eq_mul_inv] using
    hend.add (hscale.mul hweight hW) hW

end ContinuousFlexibility.Analysis
