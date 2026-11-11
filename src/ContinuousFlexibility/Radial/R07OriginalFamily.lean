import ContinuousFlexibility.Radial.MorseChainFullRealization
import ContinuousFlexibility.Radial.MorseChainMassResistance

/-!
# Uniform constants for the fixed original geometry

The geometry and auxiliary compactly supported function are fixed before
the height selection. This exposes the uniform realization and mass bounds
for that actual family without replacing either of those choices.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open Real Set
open scoped ContDiff
open ContinuousFlexibility.Statements

theorem exists_r07OriginalFamily_constants {T : MorseChainData}
    (G : MorseChainGeometryWitness T) {phi : ℝ → ℝ}
    (hPhi : ContDiff ℝ ∞ phi ∧ (∀ x, x ≤ 1 ∨ G.rightEnd ≤ x → phi x = 0) ∧
      ∃ x ∈ Ioo 1 G.rightEnd, phi x ≠ 0) :
    ∃ C : ℕ → ℝ, ∀ σ, (∀ n, 1 ≤ σ n ∧ σ n ≤ 2) →
      MorseChainRealization T σ (morseChainReferenceFamily G phi σ) C ∧
      MorseMassResistanceBounds T σ (morseChainReferenceFamily G phi σ) C := by
  classical
  obtain ⟨K, hK, hDist, hWidths⟩ := morsePartitionReference_geometry_bounds G 0 phi 0 0
  choose J hJ hJets using exists_morsePartitionReference_profile_jetBounds G
  let C : ℕ → ℝ := fun s => max (J s) (max K G.rightEnd)
  have hJC (s : ℕ) : J s ≤ C s := le_max_left _ _
  have hKC : K ≤ C 0 := (le_max_left _ _).trans (le_max_right _ _)
  have hC (s : ℕ) : 0 < C s := (hJ s).trans_le (hJC s)
  have hWidth : G.rightEnd ≤ C 0 := (le_max_right _ _).trans (le_max_right _ _)
  have hInv : (C 0)⁻¹ ≤ K⁻¹ := inv_anti₀ hK hKC
  apply exists_morseChainMassResistanceConstants T C (morseChainReferenceFamily G phi)
  intro σ hσ
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

end ContinuousFlexibility.Radial
