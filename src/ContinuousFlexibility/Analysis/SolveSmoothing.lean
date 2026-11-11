import ContinuousFlexibility.Analysis.TameTransfer

/-!
# Smoothing on a tame complemented subspace

A projection may lose a fixed number of derivatives. At widely separated
orders the usual tail estimate applies after that loss. At nearby orders
one instead uses the forward smoothing estimate and the triangle inequality.
This permits the same smoothing family on the actual sector and source
subspaces, without assuming that their projections have zero loss.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter
open scoped Topology
open ContinuousFlexibility.Statements

section ProductTopology

variable {E F : Type*} [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
  [TopologicalSpace F] [AddCommGroup F] [Module ℝ F]

/-- The sum grading generates the ordinary product topology. -/
theorem withSeminorms_pairGrading {p : ℕ → Seminorm ℝ E} {q : ℕ → Seminorm ℝ F}
    (hp : WithSeminorms p) (hq : WithSeminorms q) :
    WithSeminorms (pairGrading p q) := by
  let r : Bool → ℕ → Seminorm ℝ (E × F) := fun b =>
    if b then (fun n => (q n).comp (LinearMap.snd ℝ E F))
    else (fun n => (p n).comp (LinearMap.fst ℝ E F))
  let t : Bool → TopologicalSpace (E × F) := fun b =>
    if b then TopologicalSpace.induced Prod.snd inferInstance
    else TopologicalSpace.induced Prod.fst inferInstance
  have ht (b : Bool) : WithSeminorms (topology := t b) (r b) := by
    cases b
    · exact (LinearMap.fst ℝ E F).withSeminorms_induced hp
    · exact (LinearMap.snd ℝ E F).withSeminorms_induced hq
  have hraw : WithSeminorms (SeminormFamily.sigma r) := by
    have h := withSeminorms_iInf ht
    simpa [t, iInf_bool_eq, inf_comm] using h
  apply hraw.congr
  · intro n
    refine ⟨{⟨false, n⟩, ⟨true, n⟩}, 2, ?_⟩
    intro x
    simp only [Seminorm.comp_id, Seminorm.smul_apply, NNReal.smul_def, smul_eq_mul]
    change p n x.1 + q n x.2 ≤ (2 : ℝ) * _
    have h1 : p n x.1 ≤ ({⟨false, n⟩, ⟨true, n⟩} : Finset (Sigma fun _ : Bool => ℕ)).sup
        (SeminormFamily.sigma r) x :=
      Seminorm.le_finset_sup_apply (by simp)
    have h2 : q n x.2 ≤ ({⟨false, n⟩, ⟨true, n⟩} : Finset (Sigma fun _ : Bool => ℕ)).sup
        (SeminormFamily.sigma r) x :=
      Seminorm.le_finset_sup_apply (by simp)
    linarith only [h1, h2]
  · intro z
    refine ⟨{z.2}, 1, ?_⟩
    rw [Finset.sup_singleton, one_smul, Seminorm.comp_id]
    intro x
    cases z with
    | mk b n =>
      cases b
      · exact le_add_of_nonneg_right (apply_nonneg (q n) x.2)
      · exact le_add_of_nonneg_left (apply_nonneg (p n) x.1)

end ProductTopology

section Projection

variable {E : Type*} [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]

/-- Smoothing passes to the range of a continuous tame projection, allowing
a fixed loss in the projection. The inherited grading is unchanged. -/
theorem hasSmoothing_submodule_of_tame_projection
    {p : ℕ → Seminorm ℝ E} (hpmono : Monotone p)
    (W : Submodule ℝ E) (P : E →L[ℝ] E)
    (hPW : ∀ x, P x ∈ W) (hPid : ∀ w ∈ W, P w = w)
    {r b : ℕ} (hPt : IsTameLinear p p P.toLinearMap r b)
    (hp : HasSmoothing p) :
    HasSmoothing (fun n => (p n).comp W.subtype) := by
  obtain ⟨base, loss, S, ha, hb, hc⟩ := hp
  let T : ℕ → W →L[ℝ] W := fun N =>
    ((P.comp (S N)).comp W.subtypeL).codRestrict W (fun x => hPW _)
  have hT (N : ℕ) (w : W) : ((T N w : W) : E) = P (S N w) := rfl
  refine ⟨max base b, loss + r, T, ?_, ?_, ?_⟩
  · intro m n hm hmn
    obtain ⟨CP, hCP⟩ := hPt n ((le_of_max_le_right hm).trans hmn)
    obtain ⟨C, hC, hSC⟩ := ha m (n + r) (le_of_max_le_left hm) (by omega)
    refine ⟨CP * C, mul_nonneg CP.2 hC, fun N w => ?_⟩
    simp only [Seminorm.comp_apply, Submodule.subtype_apply, hT]
    have h1 := hCP (S N w)
    simp only [ContinuousLinearMap.coe_coe] at h1
    calc
      p n (P (S N w)) ≤ CP * p (n + r) (S N w) := h1
      _ ≤ CP * (C * Real.exp ((((n + r : ℕ) : ℝ) - m + loss) * N) * p m w) := by
        exact mul_le_mul_of_nonneg_left (hSC N w) CP.2
      _ = CP * C * Real.exp (((n : ℝ) - m + (loss + r : ℕ)) * N) * p m w := by
        push_cast
        congr 2 <;> ring
  · intro m n hm hmn
    obtain ⟨CP, hCP⟩ := hPt m (le_of_max_le_right hm)
    by_cases hwide : m + r ≤ n
    · obtain ⟨C, hC, hSC⟩ := hb (m + r) n (by omega) hwide
      refine ⟨CP * C, mul_nonneg CP.2 hC, fun N w => ?_⟩
      simp only [Seminorm.comp_apply, Submodule.subtype_apply, Submodule.coe_sub, hT]
      have h1 := hCP ((w : E) - S N w)
      simp only [ContinuousLinearMap.coe_coe, map_sub, hPid w w.2] at h1
      calc
        p m ((w : E) - P (S N w)) ≤ CP * p (m + r) ((w : E) - S N w) := h1
        _ ≤ CP * (C * Real.exp (-((n : ℝ) - (m + r : ℕ) - loss) * N) * p n w) :=
          mul_le_mul_of_nonneg_left (hSC N w) CP.2
        _ = CP * C * Real.exp (-((n : ℝ) - m - (loss + r : ℕ)) * N) * p n w := by
          push_cast
          congr 2 <;> ring
    · have hn : n ≤ m + r := by omega
      obtain ⟨C, hC, hSC⟩ := ha n (m + r) (by omega) hn
      refine ⟨1 + CP * C, add_nonneg zero_le_one (mul_nonneg CP.2 hC), fun N w => ?_⟩
      simp only [Seminorm.comp_apply, Submodule.subtype_apply, Submodule.coe_sub, hT]
      have h1 := hCP (S N w)
      simp only [ContinuousLinearMap.coe_coe] at h1
      have heq : (((m + r : ℕ) : ℝ) - n + loss) * N =
          -((n : ℝ) - m - (loss + r : ℕ)) * N := by
        push_cast
        ring
      have he : 1 ≤ Real.exp (-((n : ℝ) - m - (loss + r : ℕ)) * N) := by
        apply Real.one_le_exp
        apply mul_nonneg _ (Nat.cast_nonneg _)
        have hnr : (n : ℝ) ≤ (m : ℝ) + r := by exact_mod_cast hn
        push_cast
        linarith only [hnr, Nat.cast_nonneg (α := ℝ) loss]
      calc
        p m ((w : E) - P (S N w)) ≤ p m w + p m (P (S N w)) :=
          map_sub_le_add _ _ _
        _ ≤ p n w + CP * p (m + r) (S N w) := add_le_add (hpmono hmn _) h1
        _ ≤ p n w + CP * (C * Real.exp ((((m + r : ℕ) : ℝ) - n + loss) * N) * p n w) :=
          add_le_add_left (mul_le_mul_of_nonneg_left (hSC N w) CP.2) _
        _ = p n w + CP * C * Real.exp (-((n : ℝ) - m - (loss + r : ℕ)) * N) * p n w := by
          rw [heq]
          ring
        _ ≤ Real.exp (-((n : ℝ) - m - (loss + r : ℕ)) * N) * p n w +
            CP * C * Real.exp (-((n : ℝ) - m - (loss + r : ℕ)) * N) * p n w := by
          exact add_le_add_right (le_mul_of_one_le_left (apply_nonneg _ _) he) _
        _ = (1 + CP * C) * Real.exp (-((n : ℝ) - m - (loss + r : ℕ)) * N) * p n w := by ring
  · intro w
    apply tendsto_subtype_rng.mpr
    have h := (P.continuous.tendsto (w : E)).comp (hc (w : E))
    rw [hPid w w.2] at h
    exact h

end Projection

end ContinuousFlexibility.Analysis
