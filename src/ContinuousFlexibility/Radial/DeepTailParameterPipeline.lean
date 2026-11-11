import ContinuousFlexibility.Radial.DeepTailJacobiFamilies
import ContinuousFlexibility.Radial.DeepTailPoissonCandidate

/-!
# Continuity of the normalized natural entrance derivative

The common physical edges carry continuously chosen actual Poisson
functions. Their exact flux coefficients determine the uniformly
convergent continued fraction, and hence a continuous normalized entrance
slope. Identification with the original natural line preserves its full
entrance regularity.
-/

noncomputable section

namespace ContinuousFlexibility.Blueprint

open Set
open ContinuousFlexibility.Statements ContinuousFlexibility.Radial

/-- The height-ratio continuity statement follows from the full natural
line theorem after choosing uniform quantitative deep-tail thresholds. -/
theorem r06Parameter_of_r06Full {C η K : ℝ} (hfull : R06Full C η K)
    (hη : η ≤ 1 / 16) (hK : 64 ≤ K) : DeepTailParameterContinuity η K := by
  classical
  intro family hfamily hgeom hjets
  let σ₀ : HeightRatios := ⟨fun _ => 1, fun _ => ⟨le_rfl, by norm_num⟩⟩
  let T₀ := family σ₀
  let F := deepTailFixedGeometryFamily family σ₀
  have hF (σ : HeightRatios) : F σ = family σ :=
    deepTailFixedGeometryFamily_eq family σ₀ (fun σ => hgeom σ σ₀) σ
  have hT (σ : HeightRatios) : DeepTailHypotheses (F σ) := by
    rw [hF]
    exact (hfamily σ).1
  have hηF (σ : HeightRatios) : (F σ).η ≤ η := by
    rw [hF]
    exact (hfamily σ).2.1
  have hKF (σ : HeightRatios) : K ≤ (F σ).K := by
    rw [hF]
    exact (hfamily σ).2.2
  have hsmall (σ : HeightRatios) : (F σ).η ≤ 1 / 16 := (hηF σ).trans hη
  have hlarge (σ : HeightRatios) : 64 ≤ (F σ).K := hK.trans (hKF σ)
  have hp₀ : ContinuousOn (fun z : HeightRatios × ℝ => (family z.1).p z.2)
      {z | z.2 ∈ Ico (family z.1).entrance (family z.1).endpoint} := by
    simpa only [radialJet] using hjets 0
  have hpF : ContinuousOn (fun z : HeightRatios × ℝ => (F z.1).p z.2)
      {z | z.2 ∈ Ico (F z.1).entrance (F z.1).endpoint} := by
    simpa only [hF] using hp₀
  have hn (n : ℕ) : T₀.node n < T₀.node (n + 1) :=
    deepTail_node_strictMono (hfamily σ₀).1 (Nat.lt_succ_self n)
  have hpEntry : Continuous (fun σ => (F σ).p (F σ).entrance) :=
    hpF.comp_continuous (continuous_id.prodMk continuous_const)
      (fun σ => ⟨le_rfl, (hT σ).1⟩)
  have hpEntry_ne (σ : HeightRatios) : (F σ).p (F σ).entrance ≠ 0 :=
    (deepTail_pos (hT σ) _ ⟨le_rfl, (hT σ).1⟩).ne'
  have hexB (n : ℕ) :
      ∃ B : ∀ σ, TailPhysicalPoissonData (F σ).p (T₀.node n) (T₀.node (n + 1))
          (F σ).Λ (F σ).η (hn n).le,
        (∀ right, Continuous (fun σ => (B σ).onEdge right)) ∧
        Continuous (fun σ => (B σ).offDiagonal) ∧
        Continuous (fun σ => (B σ).leftDiagonal) ∧
        Continuous (fun σ => (B σ).rightDiagonal) := by
    have hp := deepTailFamily_density_continuous_on_interval F hpF
      (fun σ => deepTail_Icc_subset (hT σ) (deepTail_entrance_le_node (hT σ) n)
        (deepTail_node_lt_endpoint (hT σ) (n + 1)))
    exact exists_continuous_tailPhysicalPoissonFamily (fun σ => (F σ).p) (hn n)
      (fun σ => (F σ).Λ) (fun σ => (F σ).η) hp
      (fun σ => deepTail_edge_pos (hT σ) n) continuous_const
      (fun σ => (hT σ).2.2.1.le) (θ := (1 / 16 : ℝ)) (by norm_num) (by norm_num)
      hsmall (fun σ => deepTailEdge_diagonal_small (hT σ) n)
  choose B₁ hBon hBc hBl hBr using hexB
  let B (σ : HeightRatios) (n : ℕ) :
      TailPhysicalPoissonData (F σ).p (T₀.node n) (T₀.node (n + 1))
        (F σ).Λ (F σ).η (hn n).le := B₁ n σ
  have hccont (n : ℕ) : Continuous (fun σ => tailPoissonJacobiOffDiagonal (B σ) n) := hBc n
  by_cases hstart : T₀.node 0 = T₀.entrance
  · let b₀ (σ : HeightRatios) := -(B σ 0).leftDiagonal
    let b (σ : HeightRatios) := tailPoissonJacobiDiagonal (B σ) (b₀ σ)
    let c (σ : HeightRatios) := tailPoissonJacobiOffDiagonal (B σ)
    have hb₀ (σ : HeightRatios) : (F σ).Λ * tailMass (F σ) 0 / 4 ≤ b₀ σ :=
      deepTail_Poisson_firstDiagonal_bound (hT σ) (hsmall σ) (hlarge σ) (B σ)
    have hb (σ : HeightRatios) (n : ℕ) : 0 < b σ n :=
      (div_pos (mul_pos (hT σ).2.2.1 (tailMass_pos (hT σ) n)) (by norm_num)).trans_le
        (deepTail_Poisson_jacobiDiagonal_bound (hT σ) (hsmall σ) (hlarge σ) (B σ) (hb₀ σ) n)
    have hε (σ : HeightRatios) (n : ℕ) :
        c σ n ^ 2 / (b σ n * b σ (n + 1)) ∈ Icc 0 (1 / 8 : ℝ) :=
      (deepTail_Poisson_jacobi_smallness (hT σ) (hsmall σ) (hlarge σ) (B σ) (hb₀ σ)).1 n
    have hbcont (n : ℕ) : Continuous (fun σ => b σ n) :=
      continuous_tailPoissonJacobiDiagonal B b₀ (hBl 0).neg hBl hBr n
    have hr : Continuous (fun σ => tailNaturalNodeRatio (b σ) (c σ) (hε σ) 0) :=
      continuous_tailNaturalNodeRatio b c (fun σ n => (hb σ n).ne') hε hbcont hccont 0
    have hslope : Continuous (fun σ =>
        (-(B σ 0).leftDiagonal - c σ 0 * tailNaturalNodeRatio (b σ) (c σ) (hε σ) 0) /
          (F σ).p (F σ).entrance) :=
      ((hBl 0).neg.sub ((hccont 0).mul hr)).div hpEntry hpEntry_ne
    have hex (σ : HeightRatios) : ∃ u : ℝ → ℝ,
        TailNaturalEquation (F σ) u ∧ u (F σ).entrance = 1 ∧
        deriv u (F σ).entrance =
          (-(B σ 0).leftDiagonal - c σ 0 * tailNaturalNodeRatio (b σ) (c σ) (hε σ) 0) /
            (F σ).p (F σ).entrance :=
      exists_tailNatural_normalized_noInitial hfull (hT σ) (hηF σ) (hKF σ)
        (hsmall σ) (hlarge σ) (B σ) hstart (b₀ σ) (hb₀ σ) (hε σ)
    choose u hu hu₀ hdu using hex
    refine ⟨u, ?_, ?_⟩
    · intro σ
      simpa only [hF] using And.intro (hu σ) (hu₀ σ)
    · have hh : Continuous (fun σ => deriv (u σ) (F σ).entrance) :=
        hslope.congr (fun σ => (hdu σ).symm)
      simpa only [hF] using hh
  · have hinitial : T₀.entrance < T₀.node 0 := by
      rcases lt_or_eq_of_le (hfamily σ₀).1.2.1 with hlt | heq
      · exact hlt
      · exact False.elim (hstart heq.symm)
    have hpI := deepTailFamily_density_continuous_on_interval F hpF
      (fun σ => deepTail_Icc_subset (hT σ) le_rfl (deepTail_node_lt_endpoint (hT σ) 0))
    have hpIpos (σ : HeightRatios) : ∀ x ∈ Icc T₀.entrance (T₀.node 0), 0 < (F σ).p x :=
      fun x hx => deepTail_pos (hT σ) x
        (deepTail_Icc_subset (hT σ) le_rfl (deepTail_node_lt_endpoint (hT σ) 0) hx)
    obtain ⟨BI, hBIon, hBIc, hBIl, hBIr⟩ :=
      exists_continuous_tailPhysicalPoissonFamily (fun σ => (F σ).p) hinitial
        (fun σ => (F σ).Λ) (fun σ => (F σ).η) hpI hpIpos continuous_const
        (fun σ => (hT σ).2.2.1.le) (θ := (1 / 16 : ℝ)) (by norm_num) (by norm_num)
        hsmall (fun σ => deepTail_initialEdge_diagonal_small (hT σ) hinitial)
    let b₀ (σ : HeightRatios) := -(BI σ).rightDiagonal - (B σ 0).leftDiagonal
    let b (σ : HeightRatios) := tailPoissonJacobiDiagonal (B σ) (b₀ σ)
    let c (σ : HeightRatios) := tailPoissonJacobiOffDiagonal (B σ)
    have hb₀ (σ : HeightRatios) : (F σ).Λ * tailMass (F σ) 0 / 4 ≤ b₀ σ :=
      deepTail_initialJacobiDiagonal_bound (hT σ) (hsmall σ) (hlarge σ) (B σ) hinitial (BI σ)
    have hb (σ : HeightRatios) (n : ℕ) : 0 < b σ n :=
      (div_pos (mul_pos (hT σ).2.2.1 (tailMass_pos (hT σ) n)) (by norm_num)).trans_le
        (deepTail_Poisson_jacobiDiagonal_bound (hT σ) (hsmall σ) (hlarge σ) (B σ) (hb₀ σ) n)
    have hε (σ : HeightRatios) (n : ℕ) :
        c σ n ^ 2 / (b σ n * b σ (n + 1)) ∈ Icc 0 (1 / 8 : ℝ) :=
      (deepTail_Poisson_jacobi_smallness (hT σ) (hsmall σ) (hlarge σ) (B σ) (hb₀ σ)).1 n
    have hbcont (n : ℕ) : Continuous (fun σ => b σ n) :=
      continuous_tailPoissonJacobiDiagonal B b₀ (hBIr.neg.sub (hBl 0)) hBl hBr n
    have hci (σ : HeightRatios) : 0 < (BI σ).offDiagonal :=
      (BI σ).offDiagonal_pos hinitial
        (continuousOn_tailFamilyDensity (p := fun τ : HeightRatios => (F τ).p)
          (a := T₀.entrance) (b := T₀.node 0) hpI σ)
        (hpIpos σ) (hT σ).2.2.1.le
    have hslope := continuous_tailNaturalInitialSlope b c
      (fun σ => (BI σ).offDiagonal) (fun σ => (BI σ).leftDiagonal)
      (fun σ => (F σ).p (F σ).entrance) hb hci hpEntry_ne hε hbcont hccont hBIc hBIl hpEntry
    have hex (σ : HeightRatios) : ∃ u : ℝ → ℝ,
        TailNaturalEquation (F σ) u ∧ u (F σ).entrance = 1 ∧
        deriv u (F σ).entrance =
          ((BI σ).offDiagonal - (BI σ).leftDiagonal *
            tailNaturalInitialValue (b σ) (c σ) (BI σ).offDiagonal (hε σ)) /
            ((F σ).p (F σ).entrance *
              tailNaturalInitialValue (b σ) (c σ) (BI σ).offDiagonal (hε σ)) :=
      exists_tailNatural_normalized_initial hfull (hT σ) (hηF σ) (hKF σ)
        (hsmall σ) (hlarge σ) (B σ) hinitial (BI σ) (hε σ)
    choose u hu hu₀ hdu using hex
    refine ⟨u, ?_, ?_⟩
    · intro σ
      simpa only [hF] using And.intro (hu σ) (hu₀ σ)
    · have hh : Continuous (fun σ => deriv (u σ) (F σ).entrance) :=
        hslope.congr (fun σ => (hdu σ).symm)
      simpa only [hF] using hh

end ContinuousFlexibility.Blueprint
