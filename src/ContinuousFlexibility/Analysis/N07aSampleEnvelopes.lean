import ContinuousFlexibility.Analysis.N07aMaterialProductBounds

/-!
# Finite envelopes for actual jet formulas

Finite index sets and nonnegative integer powers preserve sampled
subpower growth. The complete expression is still absorbed only once.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis.N07aSampleSubpower

open Set
open scoped BigOperators
open ContinuousFlexibility.Statements

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {K : CanonicalData S}

theorem nat_pow (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T)
    {f : ℕ → ℝ} (hf : N07aSampleSubpower T K f) (n : ℕ) :
    N07aSampleSubpower T K (fun m => f m ^ n) := by
  induction n with
  | zero => simpa only [pow_zero] using const hD hT (K := K) 1
  | succ n ih => simpa only [pow_succ] using mul hD hT ih hf

theorem abs {f : ℕ → ℝ} (hf : N07aSampleSubpower T K f) :
    N07aSampleSubpower T K (fun m => |f m|) :=
  hf.mono (fun _ => by simp only [abs_abs, le_refl])

theorem finset_sum (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T)
    {ι : Type*} (s : Finset ι) (f : ι → ℕ → ℝ)
    (hf : ∀ i ∈ s, N07aSampleSubpower T K (f i)) :
    N07aSampleSubpower T K (fun m => ∑ i ∈ s, f i m) := by
  classical
  induction s using Finset.induction with
  | empty => simpa only [Finset.sum_empty] using const hD hT (K := K) 0
  | @insert i s hi ih =>
    simpa only [Finset.sum_insert hi] using
      (hf i (Finset.mem_insert_self i s)).add
        (ih (fun j hj => hf j (Finset.mem_insert_of_mem hj)))

theorem finset_prod (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T)
    {ι : Type*} (s : Finset ι) (f : ι → ℕ → ℝ)
    (hf : ∀ i ∈ s, N07aSampleSubpower T K (f i)) :
    N07aSampleSubpower T K (fun m => ∏ i ∈ s, f i m) := by
  classical
  induction s using Finset.induction with
  | empty => simpa only [Finset.prod_empty] using const hD hT (K := K) 1
  | @insert i s hi ih =>
    simpa only [Finset.prod_insert hi] using
      mul hD hT (hf i (Finset.mem_insert_self i s))
        (ih (fun j hj => hf j (Finset.mem_insert_of_mem hj)))

end ContinuousFlexibility.Analysis.N07aSampleSubpower
