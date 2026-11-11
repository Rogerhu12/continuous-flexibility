import ContinuousFlexibility.Analysis.ScalarJetSchwarz
import Mathlib.GroupTheory.Perm.Sign

/-!
# Permutation symmetry of genuine scalar directional jets

The two leading directions commute by Schwarz. Differentiating an
already verified permutation identity along the first direction moves
this symmetry through an arbitrary tail. Adjacent transpositions then
generate every finite permutation. All derivatives used here belong to
the given directional tower.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open Set Filter Equiv Function
open scoped Topology

variable {E : Type*} [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
  [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]
  {U : Set E} {f : E → ℝ}

private theorem smoothDirections_comp_adjacent
    (J : SmoothDirections U f) (hUc : Convex ℝ U) :
    ∀ (n : ℕ) (i : Fin n) (x : E), x ∈ U → ∀ v : Fin (n + 1) → E,
      J.D (n + 1) x (v ∘ swap i.castSucc i.succ) = J.D (n + 1) x v := by
  intro n
  induction n with
  | zero => intro i; exact Fin.elim0 i
  | succ n ih =>
    intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · intro x hx v
      change J.D (n + 2) x (v ∘ swap (0 : Fin (n + 2)) 1) = _
      have hswap : v ∘ swap (0 : Fin (n + 2)) 1 =
          Fin.cons (v 1) (Fin.cons (v 0) (Fin.tail (Fin.tail v))) := by
        funext k
        refine Fin.cases ?_ (fun k => ?_) k
        · simp
        · refine Fin.cases ?_ (fun k => ?_) k
          · simp
          · simp [Function.comp_def, swap_apply_def, Fin.ext_iff, Fin.tail]
      have hcons : Fin.cons (v 0) (Fin.cons (v 1) (Fin.tail (Fin.tail v))) = v := by
        change Fin.cons (v 0) (Fin.cons (Fin.tail v 0) (Fin.tail (Fin.tail v))) = v
        rw [Fin.cons_self_tail, Fin.cons_self_tail]
      rw [hswap]
      exact (J.front_two_symmetric hUc n x hx (v 1) (v 0)
        (Fin.tail (Fin.tail v))).trans (congrArg (J.D (n + 2) x) hcons)
    · intro x hx v
      have hswap : v ∘ swap j.succ.castSucc j.succ.succ =
          Fin.cons (v 0) (Fin.tail v ∘ swap j.castSucc j.succ) := by
        funext k
        refine Fin.cases ?_ (fun k => ?_) k
        · simp [Function.comp_def, swap_apply_def, Fin.ext_iff]
        · change v (swap j.castSucc.succ j.succ.succ k.succ) =
            v ((swap j.castSucc j.succ k).succ)
          exact congrArg v
            ((Fin.succ_injective (n + 1)).map_swap j.castSucc j.succ k).symm
      have hline : Tendsto (fun t : ℝ => x + t • v 0) (𝓝 (0 : ℝ)) (𝓝 x) := by
        have hc : Continuous (fun t : ℝ => x + t • v 0) :=
          continuous_const.add (continuous_id.smul continuous_const)
        simpa only [zero_smul, add_zero] using hc.tendsto (0 : ℝ)
      have hmem : ∀ᶠ t in 𝓝 (0 : ℝ), x + t • v 0 ∈ U :=
        hline.eventually (J.open_domain.mem_nhds hx)
      have heq :
          (fun t : ℝ => J.D (n + 1) (x + t • v 0)
            (Fin.tail v ∘ swap j.castSucc j.succ)) =ᶠ[𝓝 0]
          (fun t : ℝ => J.D (n + 1) (x + t • v 0) (Fin.tail v)) :=
        hmem.mono (fun t ht => ih j (x + t • v 0) ht (Fin.tail v))
      have hx0 : x + (0 : ℝ) • v 0 ∈ U := by
        simpa only [zero_smul, add_zero] using hx
      have hL := J.hasDerivAt_line_jet x (v 0) (n + 1)
        (Fin.tail v ∘ swap j.castSucc j.succ) hx0
      have hR := J.hasDerivAt_line_jet x (v 0) (n + 1) (Fin.tail v) hx0
      have hd :
          J.D (n + 2) x (Fin.cons (v 0) (Fin.tail v ∘ swap j.castSucc j.succ)) =
          J.D (n + 2) x (Fin.cons (v 0) (Fin.tail v)) := by
        simpa only [zero_smul, add_zero] using
          hL.unique (hR.congr_of_eventuallyEq heq)
      rw [hswap]
      exact hd.trans (congrArg (J.D (n + 2) x) (Fin.cons_self_tail v))

/-- Genuine scalar directional jets are symmetric in all parameter slots. -/
theorem SmoothDirections.comp_perm (J : SmoothDirections U f) (hUc : Convex ℝ U)
    (n : ℕ) (x : E) (hx : x ∈ U) (v : Fin n → E) (σ : Perm (Fin n)) :
    J.D n x (v ∘ σ) = J.D n x v := by
  cases n with
  | zero =>
    apply congrArg (J.D 0 x)
    funext i
    exact Fin.elim0 i
  | succ n =>
    have hmem : σ ∈ Submonoid.closure
        (Set.range fun i : Fin n => swap i.castSucc i.succ) := by
      rw [Equiv.Perm.mclosure_swap_castSucc_succ]
      trivial
    have hperm : ∀ w : Fin (n + 1) → E,
        J.D (n + 1) x (w ∘ σ) = J.D (n + 1) x w := by
      induction hmem using Submonoid.closure_induction with
      | mem τ hτ =>
        obtain ⟨i, rfl⟩ := hτ
        exact smoothDirections_comp_adjacent J hUc n i x hx
      | one => intro w; rfl
      | mul τ υ _ _ hτ hυ =>
        intro w
        exact (hυ (w ∘ τ)).trans (hτ w)
    exact hperm v

/-- Bundled form of the permutation identity. -/
theorem SmoothDirections.domDomCongr_eq (J : SmoothDirections U f)
    (hUc : Convex ℝ U) (n : ℕ) (x : E) (hx : x ∈ U) (σ : Perm (Fin n)) :
    (J.D n x).domDomCongr σ = J.D n x := by
  ext v
  exact J.comp_perm hUc n x hx v σ

end ContinuousFlexibility.Statements
