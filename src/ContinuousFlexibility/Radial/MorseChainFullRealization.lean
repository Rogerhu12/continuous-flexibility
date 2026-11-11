import ContinuousFlexibility.Radial.MorseChainRealization

/-!
# A uniformly realized family of accumulating Morse chains

The geometry is chosen once, before the height ratios.  The same geometric
constant and the same constant at each derivative order work for every
admissible height sequence.  The family is a total function of the sequence;
its endpoints and partition are independent of that sequence even outside
the admissible cube.

This is the geometric part of §5 of the readable manuscript, through
Lemma `lem:tail-flat`.  No spectral input from R04 is needed here.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open Real Set
open scoped ContDiff

/-- The profile family, with fixed geometric data for all height sequences. -/
def morseChainReferenceFamily {T : Statements.MorseChainData}
    (G : MorseChainGeometryWitness T) (phi : ℝ → ℝ)
    (σ : ℕ → ℝ) : Statements.ReferenceData := by
  classical
  exact morsePartitionReference G
    (if hσ : ∀ n, 1 ≤ σ n ∧ σ n ≤ 2 then morseChainGluedProfile G σ hσ else 0)
    phi 0 0

theorem morseChainReferenceFamily_admissible {T : Statements.MorseChainData}
    (G : MorseChainGeometryWitness T) (phi : ℝ → ℝ)
    (σ : ℕ → ℝ) (hσ : ∀ n, 1 ≤ σ n ∧ σ n ≤ 2) :
    morseChainReferenceFamily G phi σ =
      morsePartitionReference G (morseChainGluedProfile G σ hσ) phi 0 0 := by
  simp only [morseChainReferenceFamily, dif_pos hσ]

/-- Every prescribed starting index admits one geometry and one sequence
of constants realizing all admissible height choices simultaneously. -/
theorem exists_morseChainRealization (initial : ℕ) :
    ∃ T : Statements.MorseChainData, initial ≤ T.index ∧
      ∃ C : ℕ → ℝ, ∃ family : (ℕ → ℝ) → Statements.ReferenceData,
        (∀ σ, (∀ n, 1 ≤ σ n ∧ σ n ≤ 2) →
          Statements.MorseChainRealization T σ (family σ) C) ∧
        (∀ σ τ, (family σ).a = (family τ).a ∧
          (family σ).b = (family τ).b ∧ (family σ).cells = (family τ).cells) := by
  classical
  obtain ⟨T, hT, ⟨G⟩⟩ := exists_morseChainGeometry initial
  obtain ⟨phi, hPhi⟩ := exists_morseChainReference_auxiliary G
  obtain ⟨K, hK, hDist, hWidths⟩ :=
    morsePartitionReference_geometry_bounds G 0 phi 0 0
  choose J hJ hJets using exists_morsePartitionReference_profile_jetBounds G
  let C : ℕ → ℝ := fun s => max (J s) (max K G.rightEnd)
  have hJC (s : ℕ) : J s ≤ C s := le_max_left _ _
  have hKC : K ≤ C 0 := (le_max_left _ _).trans (le_max_right _ _)
  have hC (s : ℕ) : 0 < C s := (hJ s).trans_le (hJC s)
  have hWidth : G.rightEnd ≤ C 0 :=
    (le_max_right _ _).trans (le_max_right _ _)
  have hInv : (C 0)⁻¹ ≤ K⁻¹ := inv_anti₀ hK hKC
  refine ⟨T, hT, C, morseChainReferenceFamily G phi, ?_, ?_⟩
  · intro σ hσ
    rw [morseChainReferenceFamily_admissible G phi σ hσ]
    refine morseChainReference_realization G σ hσ phi 0 0 C hC hWidth hPhi
      (morseChainGluedProfile_flat G σ hσ).1 ?_ ?_ ?_
    · intro j r hr
      obtain ⟨hl, hu⟩ := hDist j r hr
      exact ⟨(mul_le_mul_of_nonneg_right hInv (exp_pos _).le).trans hl,
        hu.trans (mul_le_mul_of_nonneg_right hKC (exp_pos _).le)⟩
    · intro j
      obtain ⟨l, h, hsub, hlen⟩ := hWidths j
      exact ⟨l, h, hsub, hlen.trans (mul_le_mul_of_nonneg_right hKC (exp_pos _).le)⟩
    · intro j r hr s
      exact (hJets s σ hσ phi 0 0 j r hr).mono (hJ s).le (hJC s)
  · intro σ τ
    exact ⟨rfl, rfl, rfl⟩

end ContinuousFlexibility.Radial
