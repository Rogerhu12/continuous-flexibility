import ContinuousFlexibility.Analysis.N07aGeometryOpenCoefficients
import ContinuousFlexibility.Analysis.N07aAngularBoundaryInverse
import Mathlib.Analysis.Calculus.MeanValue

/-!
# Bounded actual coordinate jets control the open inverse at the boundary

The primitive inverse-coordinate atoms have bounded first derivatives on
the unit strip. The ordinary one-dimensional mean value theorem in each
coordinate gives a genuine Lipschitz bound for the original open inverse.
Together with the boundary inverse lemma this supplies true inverse germs.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set ContinuousFlexibility.Statements CanonicalGeometry
open scoped ContDiff NNReal

theorem n07a_strip_scalar_lipschitz_bound {a b : ℝ} {f : PolarPoint → ℝ}
    (hf : ContDiffOn ℝ ∞ f (Ioo a b ×ˢ univ))
    {A B : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hr : ∀ p ∈ Ioo a b ×ˢ univ, |mixedDerivative 1 0 f p| ≤ A)
    (hθ : ∀ p ∈ Ioo a b ×ˢ univ, |mixedDerivative 0 1 f p| ≤ B)
    {p q : PolarPoint} (hp : p ∈ Ioo a b ×ˢ univ) (hq : q ∈ Ioo a b ×ˢ univ) :
    ‖f p - f q‖ ≤ (A + B) * ‖p - q‖ := by
  have hrd : ∀ r ∈ Ioo a b, DifferentiableAt ℝ (fun r => f (r, p.2)) r := by
    intro r hri
    exact ((hf.contDiffAt ((isOpen_Ioo.prod isOpen_univ).mem_nhds
      ⟨hri, mem_univ _⟩)).comp r (contDiffAt_id.prodMk contDiffAt_const)).differentiableAt (by simp)
  have hrb : ∀ r ∈ Ioo a b, ‖deriv (fun r => f (r, p.2)) r‖ ≤ A := by
    intro r hri
    simpa only [mixedDerivative, iteratedDeriv_zero, iteratedDeriv_one,
      Real.norm_eq_abs] using hr (r, p.2) ⟨hri, mem_univ _⟩
  have hθd : ∀ θ ∈ (univ : Set ℝ), DifferentiableAt ℝ (fun θ => f (q.1, θ)) θ := by
    intro θ _
    exact ((hf.contDiffAt (x := (q.1, θ)) ((isOpen_Ioo.prod isOpen_univ).mem_nhds
      ⟨hq.1, mem_univ _⟩)).comp θ (contDiffAt_const.prodMk contDiffAt_id)).differentiableAt (by simp)
  have hθb : ∀ θ ∈ (univ : Set ℝ), ‖deriv (fun θ => f (q.1, θ)) θ‖ ≤ B := by
    intro θ _
    simpa only [mixedDerivative, iteratedDeriv_zero, iteratedDeriv_one,
      Real.norm_eq_abs] using hθ (q.1, θ) ⟨hq.1, mem_univ _⟩
  have hR := (convex_Ioo a b).norm_image_sub_le_of_norm_deriv_le hrd hrb hq.1 hp.1
  have hT := (convex_univ : Convex ℝ (univ : Set ℝ)).norm_image_sub_le_of_norm_deriv_le
    hθd hθb (mem_univ q.2) (mem_univ p.2)
  have hpq₁ : ‖p.1 - q.1‖ ≤ ‖p - q‖ := by
    simpa only [Prod.fst_sub] using norm_fst_le (p - q)
  have hpq₂ : ‖p.2 - q.2‖ ≤ ‖p - q‖ := by
    simpa only [Prod.snd_sub] using norm_snd_le (p - q)
  calc
    ‖f p - f q‖ ≤ ‖f p - f (q.1, p.2)‖ + ‖f (q.1, p.2) - f q‖ :=
      norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ ≤ A * ‖p.1 - q.1‖ + B * ‖p.2 - q.2‖ := add_le_add hR hT
    _ ≤ A * ‖p - q‖ + B * ‖p - q‖ := add_le_add
      (mul_le_mul_of_nonneg_left hpq₁ hA) (mul_le_mul_of_nonneg_left hpq₂ hB)
    _ = _ := (add_mul _ _ _).symm

theorem n07a_radialAffine_lipschitz (d c : ℝ) :
    LipschitzWith ⟨|c| + 1, by positivity⟩ (fun p : PolarPoint => (d + c * p.1, p.2)) := by
  apply LipschitzWith.of_dist_le_mul
  intro p q
  rw [dist_eq_norm, dist_eq_norm, Prod.norm_def]
  simp only [Prod.fst_sub, Prod.snd_sub, Real.norm_eq_abs]
  apply max_le
  · rw [show d + c * p.1 - (d + c * q.1) = c * (p.1 - q.1) by ring, abs_mul]
    have hcoord : |p.1 - q.1| ≤ ‖p - q‖ := by
      simpa only [Prod.fst_sub, Real.norm_eq_abs] using norm_fst_le (p - q)
    exact (mul_le_mul_of_nonneg_left hcoord (abs_nonneg c)).trans
      (mul_le_mul_of_nonneg_right (by linarith : |c| ≤ |c| + 1) (norm_nonneg _))
  · have hcoord : |p.2 - q.2| ≤ ‖p - q‖ := by
      simpa only [Prod.snd_sub, Real.norm_eq_abs] using norm_snd_le (p - q)
    exact hcoord.trans (le_mul_of_one_le_left (norm_nonneg _)
      (show 1 ≤ |c| + 1 by linarith [abs_nonneg c]))

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {L : ReturnCorrectionData S} {K : CanonicalData S}

theorem n07a_inverseChart_lipschitz_of_atoms
    (z : AnnularState S × ℝ) (m : ℕ)
    (hcan : K.left m < K.right m) (hphys : K.physicalLeft m < K.physicalRight m)
    (hsmooth : ∀ a, ContDiffOn ℝ ∞ (atom D T S C L K z m a) unitStrip)
    (hbound : ∀ a i j, ∃ B : ℝ, 0 ≤ B ∧ ∀ p ∈ unitStrip,
      |mixedDerivative i j (atom D T S C L K z m a) p| ≤ B) :
    ∃ M : ℝ≥0, LipschitzOnWith M (K.inverseChart z m) (canonicalOpen S K m) := by
  obtain ⟨A, hA, hAr⟩ := hbound .inverseRadial 1 0
  obtain ⟨B, hB, hAθ⟩ := hbound .inverseRadial 0 1
  obtain ⟨E, hE, hEr⟩ := hbound .inverseAngleDefect 1 0
  obtain ⟨F, hF, hEθ⟩ := hbound .inverseAngleDefect 0 1
  let R := atom D T S C L K z m .inverseRadial
  let Θ := atom D T S C L K z m .inverseAngleDefect
  let G : PolarPoint → PolarPoint := K.inverseChart z m ∘ canonicalUnitPoint K m
  let l : ℝ := K.physicalRight m - K.physicalLeft m
  have hl : 0 < l := sub_pos.mpr hphys
  have hR (p : PolarPoint) : (G p).1 = K.physicalLeft m + l * R p := by
    dsimp only [G, R, atom, l, Function.comp_apply]
    field_simp [sub_ne_zero.mpr hphys.ne']
    ring
  have hΘ (p : PolarPoint) : (G p).2 = p.2 + Θ p := by
    dsimp only [G, Θ, atom, canonicalUnitPoint, Function.comp_apply]
    ring
  let M : ℝ := l * (A + B) + (E + F) + 1
  have hM : 0 ≤ M := by dsimp only [M]; positivity
  have hG : LipschitzOnWith ⟨M, hM⟩ G unitStrip := by
    apply LipschitzOnWith.of_dist_le_mul
    intro p hp q hq
    have hr := n07a_strip_scalar_lipschitz_bound (hsmooth .inverseRadial) hA hB hAr hAθ hp hq
    have ht := n07a_strip_scalar_lipschitz_bound (hsmooth .inverseAngleDefect) hE hF hEr hEθ hp hq
    rw [dist_eq_norm, dist_eq_norm, Prod.norm_def]
    simp only [Prod.fst_sub, Prod.snd_sub, hR, hΘ]
    apply max_le
    · rw [show K.physicalLeft m + l * R p - (K.physicalLeft m + l * R q) = l * (R p - R q) by ring,
        norm_mul, Real.norm_eq_abs, abs_of_pos hl]
      calc
        l * ‖R p - R q‖ ≤ l * ((A + B) * ‖p - q‖) := mul_le_mul_of_nonneg_left hr hl.le
        _ ≤ M * ‖p - q‖ := by
          rw [← mul_assoc]
          apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
          dsimp only [M]
          linarith
    · calc
        ‖p.2 + Θ p - (q.2 + Θ q)‖ = ‖(p.2 - q.2) + (Θ p - Θ q)‖ := by congr 1; ring
        _ ≤ ‖p.2 - q.2‖ + ‖Θ p - Θ q‖ := norm_add_le _ _
        _ ≤ ‖p - q‖ + (E + F) * ‖p - q‖ := add_le_add
          (by simpa only [Prod.snd_sub] using norm_snd_le (p - q)) ht
        _ ≤ M * ‖p - q‖ := by
          dsimp only [M]
          nlinarith [mul_nonneg (mul_nonneg hl.le (add_nonneg hA hB)) (norm_nonneg (p - q))]
  let c : ℝ := (K.right m - K.left m)⁻¹
  let d : ℝ := -(K.left m) * c
  have hI : LipschitzWith ⟨|c| + 1, by positivity⟩ (n07aCanonicalUnitInversePoint K m) := by
    have he : n07aCanonicalUnitInversePoint K m = fun p => (d + c * p.1, p.2) := by
      funext p
      apply Prod.ext
      · dsimp only [n07aCanonicalUnitInversePoint, d, c]
        rw [div_eq_mul_inv]
        ring
      · rfl
    rw [he]
    exact n07a_radialAffine_lipschitz d c
  have hcomp := hG.comp hI.lipschitzOnWith (n07aCanonicalUnitInversePoint_maps hcan)
  refine ⟨⟨M, hM⟩ * ⟨|c| + 1, by positivity⟩, ?_⟩
  simpa only [G, Function.comp_def, n07aCanonicalUnitPoint_inverse hcan] using hcomp

theorem n07a_current_inverseChart_lipschitz {base : ℕ} {ε : ℝ}
    (href : ReferenceJets D T S C L K) (hcur : CurrentJets D T S C L K base ε)
    (z : Parameter S) (hz : z ∈ sectorNeighborhood S base ε ε) (m : ℕ)
    (hcan : K.left m < K.right m) (hphys : K.physicalLeft m < K.physicalRight m) :
    ∃ M : ℝ≥0, LipschitzOnWith M (K.inverseChart (liftSectorParameter S C z) m)
      (canonicalOpen S K m) :=
  n07a_inverseChart_lipschitz_of_atoms (liftSectorParameter S C z) m hcan hphys
    (fun a => (hcur.1 z hz m a).1)
    (fun a i j => n07a_currentAtom_bounded href hcur z hz m a i j)

theorem n07a_reference_inverseChart_lipschitz
    (href : ReferenceJets D T S C L K) (m : ℕ)
    (hcan : K.left m < K.right m) (hphys : K.physicalLeft m < K.physicalRight m) :
    ∃ M : ℝ≥0, LipschitzOnWith M (K.inverseChart (C.referenceState, 0) m)
      (canonicalOpen S K m) := by
  apply n07a_inverseChart_lipschitz_of_atoms (C.referenceState, 0) m hcan hphys
    (fun a => (href.1 m a).1)
  intro a i j
  obtain ⟨B, _, hB⟩ := href.2 (i + j)
  let A : ℝ := B * T.E0 (T.sample (K.cell m)) ^ B
  refine ⟨|A|, abs_nonneg _, fun p hp => ?_⟩
  exact (hB m a p hp i j le_rfl).trans (le_abs_self A)

end ContinuousFlexibility.Analysis
