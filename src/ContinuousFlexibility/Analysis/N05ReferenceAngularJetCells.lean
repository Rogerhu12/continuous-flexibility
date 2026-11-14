module

public import ContinuousFlexibility.Analysis.N05ReferenceAngularJetBasis

/-!
# Cell Parseval for actual finite angular derivatives

The field below uses ordinary iterated derivatives of the actual finite
cosine projection. Orthogonality of the normalized derivative basis gives
an exact cell square identity with the frequency power `(2 n)^(2 b)`.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Radial

open Set MeasureTheory
open scoped BigOperators
open ContinuousFlexibility.Statements

def n05_referenceHighAngularJet (J : Finset ℕ) (b : ℕ)
    (f : PolarPoint → ℝ) (x : PolarPoint) : ℝ :=
  iteratedDeriv b
    (fun θ => referenceBasisProjection (J.image (fun n => n + 2)) f (x.1, θ)) x.2

theorem n05_referenceHighAngularJet_synthesis
    (J : Finset ℕ) (b : ℕ) (f : PolarPoint → ℝ) :
    n05_referenceHighAngularJet J b f =
      r11bFiniteSynthesis J
        (fun n r => (((2 * (n + 2) : ℕ) : ℝ) ^ b) *
          referenceRadialCoefficient f (n + 2) r)
        (n05_referenceHighJetBasis b) := by
  unfold n05_referenceHighAngularJet
  rw [n05_referenceHighProjection_image]
  exact n05_referenceHighFiniteSynthesis_angularJet J
    (fun n => referenceRadialCoefficient f (n + 2)) b

theorem n05_referenceHighAngularJet_cell_parseval {D : ReferenceData}
    (hab : D.a ≤ D.b) {f : PolarPoint → ℝ} (hf : RadialCellIntegrable D f)
    (J : Finset ℕ) (b : ℕ) :
    RadialCellIntegrable D (n05_referenceHighAngularJet J b f) ∧
      ∀ m, referenceCellSquare D m (n05_referenceHighAngularJet J b f) =
        ∑ n ∈ J, (((2 * (n + 2) : ℕ) : ℝ) ^ (2 * b)) *
          ∫ r, (D.localizer m r * referenceRadialCoefficient f (n + 2) r) ^ 2
            ∂volume.restrict (radialCore D) := by
  have hc (n : ℕ) (_hn : n ∈ J) (m : ℕ) :
      MemLp (fun r => D.localizer m r *
        ((((2 * (n + 2) : ℕ) : ℝ) ^ b) * referenceRadialCoefficient f (n + 2) r))
        2 (volume.restrict (radialCore D)) := by
    have he : (fun r => D.localizer m r *
        ((((2 * (n + 2) : ℕ) : ℝ) ^ b) * referenceRadialCoefficient f (n + 2) r)) =
        fun r => (((2 * (n + 2) : ℕ) : ℝ) ^ b) *
          (D.localizer m r * referenceRadialCoefficient f (n + 2) r) := by
      funext r
      ring
    rw [he]
    exact (referenceRadialCoefficient_memLp_cell hf (n + 2) m).const_mul _
  simp only [n05_referenceHighAngularJet_synthesis]
  obtain ⟨hcell, heq⟩ := r11b_finiteSynthesis_cell_parseval_of_localized hab J
    (fun n r => (((2 * (n + 2) : ℕ) : ℝ) ^ b) *
      referenceRadialCoefficient f (n + 2) r)
    (n05_referenceHighJetBasis b) hc
    (fun n _ => n05_referenceHighJetBasis_memLp b n)
    (fun i _ j _ => n05_referenceHighJetBasis_pairing b i j)
  refine ⟨hcell, fun m => ?_⟩
  rw [heq m]
  apply Finset.sum_congr rfl
  intro n _
  have he : (fun r => (D.localizer m r *
      ((((2 * (n + 2) : ℕ) : ℝ) ^ b) * referenceRadialCoefficient f (n + 2) r)) ^ 2) =
      fun r => (((2 * (n + 2) : ℕ) : ℝ) ^ (2 * b)) *
        (D.localizer m r * referenceRadialCoefficient f (n + 2) r) ^ 2 := by
    funext r
    rw [Nat.mul_comm 2 b, pow_mul]
    ring
  rw [he, integral_const_mul]

theorem n05_referenceHighProjection_cell_square {D : ReferenceData}
    (hab : D.a ≤ D.b) {f : PolarPoint → ℝ} (hf : RadialCellIntegrable D f) (n m : ℕ) :
    referenceCellSquare D m (referenceBasisProjection {n + 2} f) =
      ∫ r, (D.localizer m r * referenceRadialCoefficient f (n + 2) r) ^ 2
        ∂volume.restrict (radialCore D) := by
  have h := (n05_referenceHighAngularJet_cell_parseval hab hf {n} 0).2 m
  have hjet : n05_referenceHighAngularJet {n} 0 f =
      referenceBasisProjection {n + 2} f := by
    funext p
    simp only [n05_referenceHighAngularJet, iteratedDeriv_zero, Finset.image_singleton]
  rw [hjet] at h
  simpa only [Nat.mul_zero, pow_zero, one_mul, Finset.sum_singleton] using h

/-- Exact cell identity in terms of the original singleton projection
squares, with no change of coordinates or equivalence constant. -/
theorem n05_referenceHighAngularJet_cell_square {D : ReferenceData}
    (hab : D.a ≤ D.b) {f : PolarPoint → ℝ} (hf : RadialCellIntegrable D f)
    (J : Finset ℕ) (b m : ℕ) :
    referenceCellSquare D m (n05_referenceHighAngularJet J b f) =
      ∑ n ∈ J, (((2 * (n + 2) : ℕ) : ℝ) ^ (2 * b)) *
        referenceCellSquare D m (referenceBasisProjection {n + 2} f) := by
  rw [(n05_referenceHighAngularJet_cell_parseval hab hf J b).2 m]
  apply Finset.sum_congr rfl
  intro n _
  rw [n05_referenceHighProjection_cell_square hab hf]

end ContinuousFlexibility.Radial
