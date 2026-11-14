module

public import ContinuousFlexibility.Radial.MorseDarbouxGround
public import ContinuousFlexibility.Radial.MorseWeylSequence
public import ContinuousFlexibility.Radial.MorseWeylExclusion

/-!
# Subthreshold Morse levels and their simplicity

Creation constructs every admissible level. Annihilation reduces any
subthreshold eigenvector to a ground vector in finitely many steps.
The positive factor norm makes each nonground lowering step injective
on the eigenspace.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Radial

open Real
open scoped RealInnerProductSpace InnerProductSpace

set_option backward.isDefEq.respectTransparency false

private theorem morseAssociatedGraph_eigen_smul {α w b E : ℝ} {u : MorseL2}
    (hu : (u, E • u) ∈ morseAssociatedGraph α w b) (c : ℝ) :
    (c • u, E • (c • u)) ∈ morseAssociatedGraph α w b := by
  rw [smul_comm E c]
  exact (morseAssociatedGraph α w b).smul_mem c hu

private theorem morseAssociatedGraph_eigen_sub {α w b E : ℝ} {u v : MorseL2}
    (hu : (u, E • u) ∈ morseAssociatedGraph α w b)
    (hv : (v, E • v) ∈ morseAssociatedGraph α w b) :
    (u - v, E • (u - v)) ∈ morseAssociatedGraph α w b := by
  rw [smul_sub]
  exact (morseAssociatedGraph α w b).sub_mem hu hv

private theorem morsePartner_weakEigen_smul {α w b E : ℝ} (hw : 0 < w) {u : MorseL2}
    (hu : Statements.WeakSchrodingerGraph (morsePartnerPotential α w b) u (E • u)) (c : ℝ) :
    Statements.WeakSchrodingerGraph (morsePartnerPotential α w b) (c • u) (E • (c • u)) :=
  (morsePartner_weakGraph_iff_associated α b hw _ _).mpr
    (morseAssociatedGraph_eigen_smul ((morsePartner_weakGraph_iff_associated α b hw _ _).mp hu) c)

/-- Every admissible Darboux level is an eigenvalue of the actual weak
operator. -/
theorem morsePartner_level_eigen {w : ℝ} (hw : 0 < w) (b : ℝ) (m : ℕ) :
    ∀ α : ℝ, (m : ℝ) < α →
      Statements.ActualEigenvalue (morsePartnerPotential α w b) (b - (α - (m : ℝ)) ^ 2) := by
  induction m with
  | zero =>
      intro α hm
      have hα : 0 < α := by simpa only [Nat.cast_zero] using hm
      rw [Nat.cast_zero, sub_zero]
      exact ⟨morseGroundL2 hα hw, morseGroundL2_ne_zero hα hw,
        (morsePartner_weakGraph_iff_associated α b hw _ _).mpr (morseGroundL2_mem_graph hα hw b)⟩
  | succ m ih =>
      intro α hm
      rw [Nat.cast_succ] at hm
      have hm' : (m : ℝ) < α - 1 := by linarith
      let E := b - (α - 1 - (m : ℝ)) ^ 2
      obtain ⟨u, hu, hweak⟩ := ih (α - 1) hm'
      have hgu : (u, E • u) ∈ morseAssociatedGraph (α - 1) w b :=
        (morsePartner_weakGraph_iff_associated (α - 1) b hw _ _).mp hweak
      obtain ⟨U, hU, _⟩ := hgu
      change morseEnergyBase U = u at hU
      have hGraphU : (morseEnergyBase U, E • morseEnergyBase U) ∈ morseAssociatedGraph (α - 1) w b := by
        rw [hU]
        exact (morsePartner_weakGraph_iff_associated (α - 1) b hw _ _).mp hweak
      have hα : 0 < α := by linarith [Nat.cast_nonneg (α := ℝ) m]
      have hgap : b - α ^ 2 < E := by
        have hd : α - 1 - (m : ℝ) < α := by linarith [Nat.cast_nonneg (α := ℝ) m]
        have hsq := (sq_lt_sq₀ (sub_nonneg.mpr hm'.le) hα.le).mpr hd
        dsimp [E]
        linarith
      have hLevel : b - (α - (m.succ : ℝ)) ^ 2 = E := by
        rw [Nat.cast_succ]
        dsimp [E]
        ring
      rw [hLevel]
      exact ⟨morseCreationL2 α w U,
        (morseCreationL2_eigen_ne_zero_iff U hGraphU (hU.symm ▸ hu)).mpr hgap,
        (morsePartner_weakGraph_iff_associated α b hw _ _).mpr (morseCreationL2_mem_graph hw U hGraphU)⟩

private theorem morseGround_eigenspace_span {α w b : ℝ} (hα : 0 < α) (hw : 0 < w)
    {u : MorseL2} (hu : u ≠ 0)
    (hweak : Statements.WeakSchrodingerGraph (morsePartnerPotential α w b) u ((b - α ^ 2) • u))
    (v : MorseL2) :
    Statements.WeakSchrodingerGraph (morsePartnerPotential α w b) v ((b - α ^ 2) • v) ↔
      ∃ c : ℝ, v = c • u := by
  constructor
  · intro hv
    obtain ⟨c₀, h₀⟩ := (morseGround_weakGraph_iff_span hα hw b u).mp hweak
    obtain ⟨c, hc⟩ := (morseGround_weakGraph_iff_span hα hw b v).mp hv
    have hc₀ : c₀ ≠ 0 := by
      intro hz
      apply hu
      simpa only [hz, zero_smul] using h₀
    refine ⟨c / c₀, ?_⟩
    rw [h₀, smul_smul, div_mul_cancel₀ _ hc₀, hc]
  · rintro ⟨c, rfl⟩
    exact morsePartner_weakEigen_smul hw hweak c

private theorem morsePartner_eigen_classify_bounded {w : ℝ} (hw : 0 < w) (b : ℝ) (N : ℕ) :
    ∀ (α E : ℝ), α ≤ (N : ℝ) → E < b → ∀ (u : MorseL2), u ≠ 0 →
      Statements.WeakSchrodingerGraph (morsePartnerPotential α w b) u (E • u) →
      (∃ m : ℕ, (m : ℝ) < α ∧ E = b - (α - (m : ℝ)) ^ 2) ∧
        (∀ v : MorseL2, Statements.WeakSchrodingerGraph (morsePartnerPotential α w b) v (E • v) ↔
          ∃ c : ℝ, v = c • u) := by
  induction N with
  | zero =>
      intro α E hα hE u hu hweak
      have hα₀ : α ≤ 0 := by simpa only [Nat.cast_zero] using hα
      exact ((not_morsePartnerEigen_lt_threshold_of_nonpos hα₀ hw b E hE) ⟨u, hu, hweak⟩).elim
  | succ N ih =>
      intro α E hα hE u hu hweak
      have hpair := (morsePartner_weakGraph_iff_associated α b hw u (E • u)).mp hweak
      obtain ⟨U, hU, _⟩ := hpair
      change morseEnergyBase U = u at hU
      have hGraphU : (morseEnergyBase U, E • morseEnergyBase U) ∈ morseAssociatedGraph α w b := by
        rw [hU]
        exact (morsePartner_weakGraph_iff_associated α b hw u (E • u)).mp hweak
      have hu' : morseEnergyBase U ≠ 0 := hU.symm ▸ hu
      by_cases hD : morseAnnihilationL2 α w U = 0
      · have hα₀ := morseAnnihilationL2_eq_zero_implies_pos hw U hu' hD
        have h := morseAnnihilationL2_eigen_norm_sq U hGraphU
        rw [hD, norm_zero, zero_pow (by decide : 2 ≠ 0)] at h
        have hGapZero := (mul_eq_zero.mp h.symm).resolve_right (sq_pos_of_pos (norm_pos_iff.mpr hu')).ne'
        have hEg : E = b - α ^ 2 := by linarith
        subst E
        refine ⟨⟨0, ?_, ?_⟩, morseGround_eigenspace_span hα₀ hw hu hweak⟩
        · simpa only [Nat.cast_zero] using hα₀
        · rw [Nat.cast_zero, sub_zero]
      · have hα' : α - 1 ≤ (N : ℝ) := by
          rw [Nat.cast_succ] at hα
          linarith
        have hdGraph := morseAnnihilationL2_mem_partnerGraph hw U hGraphU
        have hdWeak := (morsePartner_weakGraph_iff_associated (α - 1) b hw _ _).mpr hdGraph
        obtain ⟨⟨m, hm, hEm⟩, hsimple⟩ := ih (α - 1) E hα' hE _ hD hdWeak
        refine ⟨⟨m + 1, ?_, ?_⟩, ?_⟩
        · rw [Nat.cast_add, Nat.cast_one]
          linarith
        · rw [hEm, Nat.cast_add, Nat.cast_one]
          ring
        · intro v
          constructor
          · intro hv
            obtain ⟨V, hV, _⟩ := (morsePartner_weakGraph_iff_associated α b hw v (E • v)).mp hv
            change morseEnergyBase V = v at hV
            have hGraphV : (morseEnergyBase V, E • morseEnergyBase V) ∈ morseAssociatedGraph α w b := by
              rw [hV]
              exact (morsePartner_weakGraph_iff_associated α b hw v (E • v)).mp hv
            have hvPartner := (morsePartner_weakGraph_iff_associated (α - 1) b hw _ _).mpr
              (morseAnnihilationL2_mem_partnerGraph hw V hGraphV)
            obtain ⟨c, hc⟩ := (hsimple _).mp hvPartner
            let Z := V - c • U
            have hbZ : morseEnergyBase Z = morseEnergyBase V - c • morseEnergyBase U := by
              dsimp [Z]
              rw [map_sub, map_smul]
            have hGraphZ : (morseEnergyBase Z, E • morseEnergyBase Z) ∈ morseAssociatedGraph α w b := by
              rw [hbZ]
              exact morseAssociatedGraph_eigen_sub hGraphV (morseAssociatedGraph_eigen_smul hGraphU c)
            have hz : morseAnnihilationL2 α w Z = 0 := by
              dsimp [Z]
              rw [map_sub, map_smul, hc, sub_self]
            have he := (morseAnnihilationL2_eigen_ne_zero_iff U hGraphU hu').mp hD
            have he₀ : 0 < E - b + α ^ 2 := by linarith
            have hnorm := morseAnnihilationL2_eigen_norm_sq Z hGraphZ
            rw [hz, norm_zero, zero_pow (by decide : 2 ≠ 0)] at hnorm
            have hbaseZ : morseEnergyBase Z = 0 := norm_eq_zero.mp (sq_eq_zero_iff.mp
              ((mul_eq_zero.mp hnorm.symm).resolve_left he₀.ne'))
            rw [hbZ, hU, hV] at hbaseZ
            exact ⟨c, sub_eq_zero.mp hbaseZ⟩
          · rintro ⟨c, rfl⟩
            exact morsePartner_weakEigen_smul hw hweak c

/-- Every actual subthreshold eigenvector has an admissible level, and it
spans the weak eigenspace at that level. -/
theorem morsePartner_eigen_classification {α w b E : ℝ} (hw : 0 < w) (hE : E < b)
    {u : MorseL2} (hu : u ≠ 0)
    (hweak : Statements.WeakSchrodingerGraph (morsePartnerPotential α w b) u (E • u)) :
    (∃ m : ℕ, (m : ℝ) < α ∧ E = b - (α - (m : ℝ)) ^ 2) ∧
      (∀ v : MorseL2, Statements.WeakSchrodingerGraph (morsePartnerPotential α w b) v (E • v) ↔
        ∃ c : ℝ, v = c • u) := by
  obtain ⟨N, hN⟩ := exists_nat_ge α
  exact morsePartner_eigen_classify_bounded hw b N α E hN hE u hu hweak

theorem morsePartner_actualEigenvalue_iff {α w b E : ℝ} (hw : 0 < w) (hE : E < b) :
    Statements.ActualEigenvalue (morsePartnerPotential α w b) E ↔
      ∃ m : ℕ, (m : ℝ) < α ∧ E = b - (α - (m : ℝ)) ^ 2 := by
  constructor
  · rintro ⟨u, hu, hweak⟩
    exact (morsePartner_eigen_classification hw hE hu hweak).1
  · rintro ⟨m, hm, rfl⟩
    exact morsePartner_level_eigen hw b m α hm

/-- The Morse potential in the paper has the actual closed form realization,
the complete simple list below the threshold, and the exact Weyl half-line. -/
theorem morseFullDifferentialSpectrum {j A : ℝ} (hj : 0 < j) (hA : 0 < A) (B : ℝ) :
    Statements.MorseFullDifferentialSpectrum j A B := by
  have hw : 0 < j * sqrt A := mul_pos hj (sqrt_pos.mpr hA)
  have hpot := morsePartnerPotential_paper hA.le j B
  refine ⟨morseActualClosedFormRealization hj hA B, ?_, ?_, ?_⟩
  · intro E hE
    rw [← hpot]
    exact morsePartner_actualEigenvalue_iff hw hE
  · intro E
    exact ⟨morseThreshold_le_of_essentialWeylValue hj hA B E,
      morseEssentialWeylValue_of_threshold_le hj hA B E⟩
  · intro E hE he
    obtain ⟨u, hu, hweak⟩ := he
    refine ⟨u, hu, ?_⟩
    rw [← hpot] at hweak ⊢
    exact (morsePartner_eigen_classification hw hE hu hweak).2

end ContinuousFlexibility.Radial
