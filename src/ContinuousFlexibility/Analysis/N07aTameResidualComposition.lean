module

public import ContinuousFlexibility.Analysis.SolveNewtonBridge
public import ContinuousFlexibility.Analysis.SolveTameSubspace
public import ContinuousFlexibility.Scalar.WeightedSmoothTameAlgebra
public import ContinuousFlexibility.Scalar.WeightedSmoothTameLinear

/-!
# Smooth tame substitution of an actual residual into an operator

This is the composition step for the N02/N03 return correction. The
subspace target is included in its complete projective ambient space for
composition, then restricted back to the same closed subspace.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set
open ContinuousFlexibility.Statements

variable {X Y H : Type*}
  [TopologicalSpace X] [AddCommGroup X] [Module ℝ X]
  [TopologicalSpace Y] [AddCommGroup Y] [Module ℝ Y]
  [TopologicalSpace H] [AddCommGroup H] [Module ℝ H]
  {F : ℕ → Type*} [∀ n, NormedAddCommGroup (F n)] [∀ n, NormedSpace ℝ (F n)]
  [∀ n, CompleteSpace (F n)] {bond : ∀ n, F (n + 1) →L[ℝ] F n}
  {p : ℕ → Seminorm ℝ X} {q : ℕ → Seminorm ℝ Y} {r : ℕ → Seminorm ℝ H}
  {t : ℕ → Seminorm ℝ (ProjectiveLimit F bond)}
  {U : Set X} {R : X → Y} {Q : X → Y → H → ProjectiveLimit F bond}

/-- Residual substitution into a jointly smooth tame operator preserves
the original open parameter domain and the whole height domain. -/
theorem n07a_tameResidualComposition
    (hp : Monotone p) (hr : Monotone r)
    (htp : WithSeminorms p) (htq : WithSeminorms q) (htr : WithSeminorms r)
    (hR : SmoothTameOn p q U R)
    (hQ : SmoothTameOn (pairGrading (pairGrading p q) r) t
      ((U ×ˢ univ) ×ˢ univ)
      (fun z : (X × Y) × H => Q z.1.1 z.1.2 z.2)) :
    SmoothTameOn (pairGrading p r) t (U ×ˢ univ)
      (fun z : X × H => Q z.1 (R z.1) z.2) := by
  let : IsTopologicalAddGroup X := htp.isTopologicalAddGroup
  let : ContinuousSMul ℝ X := htp.continuousSMul
  let : LocallyConvexSpace ℝ X := htp.toLocallyConvexSpace
  let : IsTopologicalAddGroup Y := htq.isTopologicalAddGroup
  let : ContinuousSMul ℝ Y := htq.continuousSMul
  let : LocallyConvexSpace ℝ Y := htq.toLocallyConvexSpace
  let : IsTopologicalAddGroup H := htr.isTopologicalAddGroup
  let : ContinuousSMul ℝ H := htr.continuousSMul
  let : LocallyConvexSpace ℝ H := htr.toLocallyConvexSpace
  have hU : IsOpen U := hR.choose.open_domain
  have hfst : SmoothTameOn (pairGrading p r) p (U ×ˢ univ)
      (fun z : X × H => z.1) :=
    smoothTameOn_continuousLinear_on (hU.prod isOpen_univ)
      (ContinuousLinearMap.fst ℝ X H) (scalar_pair_fst_isTame p r)
  have hsnd : SmoothTameOn (pairGrading p r) r (U ×ˢ univ)
      (fun z : X × H => z.2) :=
    smoothTameOn_continuousLinear_on (hU.prod isOpen_univ)
      (ContinuousLinearMap.snd ℝ X H) (scalar_pair_snd_isTame p r)
  have hRf : SmoothTameOn (pairGrading p r) q (U ×ˢ univ)
      (fun z : X × H => R z.1) := by
    have h := solve_smoothTameOn_precomp (p := pairGrading p r) hR (ContinuousLinearMap.fst ℝ X H)
      (A := 1) le_rfl (fun n z => by
        change p n z.1 ≤ 1 * (p n z.1 + r n z.2)
        simpa only [one_mul] using le_add_of_nonneg_right (apply_nonneg (r n) z.2))
    have hdom : (ContinuousLinearMap.fst ℝ X H) ⁻¹' U = U ×ˢ univ := by
      ext z
      simp only [Set.mem_preimage, ContinuousLinearMap.coe_fst', Set.mem_prod,
        Set.mem_univ, and_true]
    rw [hdom] at h
    exact h
  have hinput : SmoothTameOn (pairGrading p r) (pairGrading (pairGrading p q) r)
      (U ×ˢ univ) (fun z : X × H => ((z.1, R z.1), z.2)) :=
    smoothTameOn_prodMk_generic (tamePairGrading_monotone hp hr)
      (withSeminorms_pairGrading htp htr)
      (smoothTameOn_prodMk_generic (tamePairGrading_monotone hp hr)
        (withSeminorms_pairGrading htp htr) hfst hRf) hsnd
  exact smoothTameOn_comp_generic (tamePairGrading_monotone hp hr)
    (withSeminorms_pairGrading htp htr)
    (withSeminorms_pairGrading (withSeminorms_pairGrading htp htq) htr)
    hinput hQ (fun _ hz => ⟨⟨hz.1, mem_univ _⟩, mem_univ _⟩)

end ContinuousFlexibility.Analysis
