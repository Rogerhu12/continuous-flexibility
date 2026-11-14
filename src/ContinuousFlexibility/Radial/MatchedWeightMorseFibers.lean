module

public import ContinuousFlexibility.Radial.MorseChainPartitionData
public import ContinuousFlexibility.Radial.MatchedWeightFibers

/-!
# The actual Morse partition has at most three cells at each level

The middle cell and the two outward tails use the existing Bool-times-Nat
enumeration. At any fixed attenuation level there is at most one cell
from each tail, and at most one middle cell. This is a level multiplicity
bound, independent of the pointwise overlap bound for the localizers.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Radial

open Real Set
open ContinuousFlexibility.Statements

/-- Every level fiber lies in an explicit set of at most three cell indices. -/
theorem morseTwoTailAt_level_fiber_subset (base n : ℕ) :
    {m | morseTwoTailAt base (fun _ k => base + k) m = n} ⊆
      ({0, morseTailIndex false (n - base), morseTailIndex true (n - base)} : Set ℕ) := by
  intro j hj
  cases j with
  | zero => simp
  | succ j =>
      let p := Equiv.boolProdNatEquivNat.symm j
      change base + p.2 = n at hj
      have hp₂ : p.2 = n - base := by omega
      have he : morseTailIndex p.1 p.2 = j + 1 := by
        unfold morseTailIndex
        rw [Prod.eta p]
        exact congrArg (· + 1) (Equiv.boolProdNatEquivNat.apply_symm_apply j)
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
      cases hs : p.1
      · exact Or.inr (Or.inl (by simpa only [hs, hp₂] using he.symm))
      · exact Or.inr (Or.inr (by simpa only [hs, hp₂] using he.symm))

/-- The finite-fiber hypothesis and its uniform bound for the actual encoding. -/
theorem morseTwoTailAt_level_fiber_bound (base n : ℕ) :
    Set.Finite {m | morseTwoTailAt base (fun _ k => base + k) m = n} ∧
      Set.ncard {m | morseTwoTailAt base (fun _ k => base + k) m = n} ≤ 3 := by
  have hsub := morseTwoTailAt_level_fiber_subset base n
  have hF : ({0, morseTailIndex false (n - base), morseTailIndex true (n - base)} : Set ℕ).Finite :=
    ((finite_singleton _).insert _).insert _
  refine ⟨hF.subset hsub, (ncard_le_ncard hsub hF).trans ?_⟩
  have hpair := ncard_insert_le (morseTailIndex false (n - base))
    ({morseTailIndex true (n - base)} : Set ℕ)
  have htriple := ncard_insert_le 0
    ({morseTailIndex false (n - base), morseTailIndex true (n - base)} : Set ℕ)
  rw [ncard_singleton] at hpair
  omega

/-- The actual reference record retains the same three-cell level bound. -/
theorem morsePartitionReference_cellIndex_fiber_bound {T : MorseChainData}
    (G : MorseChainGeometryWitness T) (w phi chi chiLeft : ℝ → ℝ) (n : ℕ) :
    Set.Finite {m | (morsePartitionReference G w phi chi chiLeft).cellIndex m = n} ∧
      Set.ncard {m | (morsePartitionReference G w phi chi chiLeft).cellIndex m = n} ≤ 3 :=
  morseTwoTailAt_level_fiber_bound T.index n

/-- Schur row and column sums on the genuine Morse cell enumeration. -/
theorem morsePartitionReference_kernel_sums_of_decay {T : MorseChainData}
    (G : MorseChainGeometryWitness T) (w phi chi chiLeft : ℝ → ℝ)
    {K : ℕ → ℕ → ℝ} {C η : ℝ}
    (hC : 0 ≤ C) (hη : 0 < η) (hK : ∀ k m, 0 ≤ K k m)
    (hle : ∀ k m, K k m ≤ C * Real.exp
      (-(η * |radialS ((morsePartitionReference G w phi chi chiLeft).cellIndex k) -
        radialS ((morsePartitionReference G w phi chi chiLeft).cellIndex m)|))) :
    (∀ k, Summable (fun m => K k m) ∧
      ∑' m, K k m ≤ C * (3 * matchedSchurFactor η)) ∧
    (∀ m, Summable (fun k => K k m) ∧
      ∑' k, K k m ≤ C * (3 * matchedSchurFactor η)) :=
  matched_level_kernel_sums_of_decay
    (morsePartitionReference G w phi chi chiLeft).cellIndex 3
    (fun n => (morsePartitionReference_cellIndex_fiber_bound G w phi chi chiLeft n).1)
    (fun n => (morsePartitionReference_cellIndex_fiber_bound G w phi chi chiLeft n).2)
    hC hη hK hle

end ContinuousFlexibility.Radial
