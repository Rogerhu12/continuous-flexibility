module

public import ContinuousFlexibility.Analysis.RadialPlateauBounds
public import ContinuousFlexibility.Analysis.MaterialPlateauSize
public import ContinuousFlexibility.Analysis.CylinderUniformNorm
public import ContinuousFlexibility.Analysis.TameLocalCalculus

/-!
# Quantitative physical norms of the actual primitive test

The estimates use the entire expanded support, its actual material
volume, and the exact physical jets. The final direction belongs to the
supplied height model and agrees with the reference primitive as a germ
throughout the complete open component.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Statements

open Set Filter MeasureTheory
open scoped ENNReal BigOperators Topology
open ContinuousFlexibility.Analysis (gradedSeminorm_le_iff pairGrading_apply)

set_option backward.isDefEq.respectTransparency false

theorem referencePlateau_eLpNorm_bound
    {D : ReferenceData} {T : MaterialData}
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T)
    {β : ℝ} (hβ : 0 ≤ β) (n : ℕ) :
    ∃ K A : ℝ, 0 < K ∧ 0 ≤ A ∧ ∀ (j : ℕ) (l r : ℝ),
      D.a < l → l < r → r < D.b → Ioo l r ⊆ D.cells j →
      ∀ a b c : ℕ, a ≤ n → c ≤ n →
        eLpNorm (weightedPhysicalJet T β a b c
          (radialPlateauHeight (referenceRadialPrimitive D)
            l r (endpointPlateauWidth D l r))) 2 materialCylinderMeasure ≤
          ENNReal.ofReal (K * T.H (T.sample j) ^ (-β) * T.E0 (T.sample j) ^ A *
            T.M (T.sample j) ^ (n + 1) * radialE (D.cellIndex j) ^ (2 * n + 2)) := by
  obtain ⟨Kj, A, hKj, hA, hjet⟩ := referencePlateau_common_weightedJet_bound hD hT hβ n
  obtain ⟨Kd, hKd, hwidth⟩ := materialCell_plateau_inverse_width_bound hD
  obtain ⟨Kρ, hKρ, hρ⟩ := materialCell_plateau_rho_bound hT hD
  let V : ℝ := Real.sqrt (2 * (Kρ + 1) * Real.pi)
  have hV : 0 < V := Real.sqrt_pos.mpr (by positivity)
  let K : ℝ := V * Kj * Kd ^ n
  have hK : 0 < K := by dsimp only [K]; positivity
  have hgeom : RadialProfileGeometry D := (Classical.choose_spec hD).1
  have hpos := hT.2.1
  have hinside := hT.2.2.2.2.2.2.2.1
  have hsamp : ∀ j, T.sample j ∈ Ioo D.a D.b := by
    obtain ⟨_, hdata⟩ := hD
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hsamp, _⟩ := hT
    exact fun j => hdata.2.1.2.2.2.1 j (hsamp j)
  refine ⟨K, A, hK, hA, ?_⟩
  intro j l r hl hlr hr hcell a b c ha hc
  let E : ℝ := radialE (D.cellIndex j)
  let R : ℝ := (Kρ + 1) * E ^ 4
  let W : ℝ := T.H (T.sample j) ^ (-β) * T.E0 (T.sample j) ^ A *
    T.M (T.sample j) ^ (n + 1)
  have hE : 0 < E := Real.exp_pos _
  have hR : 0 < R := by dsimp only [R]; positivity
  have hW : 0 ≤ W := by
    have hp := hpos _ (hsamp j)
    dsimp only [W]
    exact mul_nonneg
      (mul_nonneg (Real.rpow_nonneg hp.2.1.le _) (Real.rpow_nonneg hp.2.2.1.le _))
      (pow_nonneg (zero_le_one.trans hp.2.2.2) _)
  have hδ := endpointPlateauWidth_pos hl hr
  have hmember := radialPlateauHeight_member hT β
    (referenceRadialPrimitive_contDiff hgeom) hδ (endpointPlateau_support_subset hl hr)
  have hzero (p : PolarPoint) (hp : R < |p.1|) :
      weightedPhysicalJet T β a b c
        (radialPlateauHeight (referenceRadialPrimitive D)
          l r (endpointPlateauWidth D l r)) p = 0 := by
    apply weightedPhysicalJet_radialPlateauHeight_zero_off_support hT β _ hδ a b c p
    intro ht
    have hh := hρ j l r hl hlr hr hcell (T.radius p.1) ht
    have hx : |p.1| ≤ Kρ * E ^ 4 := by
      simpa only [(hinside p.1).2, E] using hh
    have hlt : Kρ * E ^ 4 < R := by
      dsimp only [R]
      nlinarith only [pow_pos hE 4]
    exact (not_lt_of_ge hx) (hlt.trans hp)
  have hbound (p : PolarPoint) :
      |weightedPhysicalJet T β a b c
        (radialPlateauHeight (referenceRadialPrimitive D)
          l r (endpointPlateauWidth D l r)) p| ≤
        Kj * (endpointPlateauWidth D l r)⁻¹ ^ n * W := by
    simpa only [W, mul_assoc] using hjet j l r hl hlr hr hcell a b c ha hc p
  have hLp := cylinder_eLpNorm_le_of_radial_support
    (hmember.2.2.2.2 a b c).aestronglyMeasurable hR.le
    (mul_nonneg (mul_nonneg hKj.le (pow_nonneg (inv_pos.mpr hδ).le n)) hW)
    hzero hbound
  have hroot : Real.sqrt (2 * R * Real.pi) = V * E ^ 2 := by
    have hsquare : 2 * R * Real.pi = (V * E ^ 2) ^ 2 := by
      dsimp only [R, V]
      rw [mul_pow, Real.sq_sqrt (by positivity : 0 ≤ 2 * (Kρ + 1) * Real.pi)]
      ring
    rw [hsquare, Real.sqrt_sq (mul_nonneg hV.le (sq_nonneg E))]
  have hpow : (endpointPlateauWidth D l r)⁻¹ ^ n ≤ Kd ^ n * E ^ (2 * n) := by
    calc
      _ ≤ (Kd * E ^ 2) ^ n :=
        pow_le_pow_left₀ (inv_pos.mpr hδ).le (hwidth j l r hl hlr hr hcell) n
      _ = _ := by rw [mul_pow, ← pow_mul]
  apply hLp.trans
  apply ENNReal.ofReal_le_ofReal
  rw [hroot]
  calc
    _ ≤ V * E ^ 2 * (Kj * (Kd ^ n * E ^ (2 * n)) * W) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hpow hKj.le) hW)
        (mul_nonneg hV.le (sq_nonneg E))
    _ = _ := by
      dsimp only [K, W, E]
      rw [pow_add]
      ring

/-- One sample-weight bound controls every physical level up to the
chosen order, which is exactly what the projective grading requires. -/
theorem referencePlateau_physicalNorm_bound
    {D : ReferenceData} {T : MaterialData}
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T)
    {β : ℝ} (hβ : 0 ≤ β) (n : ℕ) :
    ∃ K A : ℝ, 0 < K ∧ 0 ≤ A ∧ ∀ (j : ℕ) (l r : ℝ),
      D.a < l → l < r → r < D.b → Ioo l r ⊆ D.cells j →
      ∀ s : ℕ, s ≤ n →
        physicalNorm T β s (radialPlateauHeight (referenceRadialPrimitive D)
          l r (endpointPlateauWidth D l r)) ≤
          K * T.H (T.sample j) ^ (-β) * T.E0 (T.sample j) ^ A *
            T.M (T.sample j) ^ (n + 1) * radialE (D.cellIndex j) ^ (2 * n + 2) := by
  classical
  obtain ⟨Kl, A, hKl, hA, hLp⟩ := referencePlateau_eLpNorm_bound hD hT hβ n
  let B : ℝ := 1 + ∑ s : Fin (n + 1), Real.sqrt (Fintype.card (JetIndex s.val) : ℝ)
  have hB : 0 < B := add_pos_of_pos_of_nonneg zero_lt_one
    (Finset.sum_nonneg (fun s _ => Real.sqrt_nonneg _))
  have hcard {s : ℕ} (hs : s ≤ n) : Real.sqrt (Fintype.card (JetIndex s) : ℝ) ≤ B := by
    let si : Fin (n + 1) := ⟨s, Nat.lt_succ_of_le hs⟩
    exact (Finset.single_le_sum (fun i _ => Real.sqrt_nonneg (Fintype.card (JetIndex i.val) : ℝ))
      (Finset.mem_univ si)).trans (le_add_of_nonneg_left zero_le_one)
  refine ⟨B * Kl, A, mul_pos hB hKl, hA, ?_⟩
  intro j l r hl hlr hr hcell s hs
  have hsamp : T.sample j ∈ Ioo D.a D.b := by
    obtain ⟨_, hdata⟩ := hD
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hsample, _⟩ := hT
    exact hdata.2.1.2.2.2.1 j (hsample j)
  have hp := hT.2.1 _ hsamp
  have hL : 0 ≤ Kl * T.H (T.sample j) ^ (-β) * T.E0 (T.sample j) ^ A *
      T.M (T.sample j) ^ (n + 1) * radialE (D.cellIndex j) ^ (2 * n + 2) := by
    have hE : 0 < radialE (D.cellIndex j) := Real.exp_pos _
    exact mul_nonneg
      (mul_nonneg
        (mul_nonneg (mul_nonneg hKl.le (Real.rpow_nonneg hp.2.1.le _))
          (Real.rpow_nonneg hp.2.2.1.le _))
        (pow_nonneg (zero_le_one.trans hp.2.2.2) _))
      (pow_nonneg hE.le _)
  have hj (i : JetIndex s) := hLp j l r hl hlr hr hcell
    (i.val 0).val (i.val 1).val (i.val 2).val
    ((Nat.le_of_lt_succ (i.val 0).isLt).trans hs)
    ((Nat.le_of_lt_succ (i.val 2).isLt).trans hs)
  calc
    _ ≤ Real.sqrt (Fintype.card (JetIndex s) : ℝ) *
        (Kl * T.H (T.sample j) ^ (-β) * T.E0 (T.sample j) ^ A *
          T.M (T.sample j) ^ (n + 1) * radialE (D.cellIndex j) ^ (2 * n + 2)) :=
      physicalNorm_le_of_common_jet_bound hL hj
    _ ≤ B * (Kl * T.H (T.sample j) ^ (-β) * T.E0 (T.sample j) ^ A *
          T.M (T.sample j) ^ (n + 1) * radialE (D.cellIndex j) ^ (2 * n + 2)) :=
      mul_le_mul_of_nonneg_right (hcard hs) hL
    _ = _ := by ring

/-- The quantitative test is an actual direction in the supplied height
space, not merely a scalar function with formal derivative bounds. -/
theorem exists_referencePlateau_heightPair_norm_bound
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T)
    (hS : IsPhysicalSpaces D T S) (n : ℕ) :
    ∃ K A R : ℝ, 0 < K ∧ 0 ≤ A ∧ 0 ≤ R ∧ ∀ (j : ℕ) (l r : ℝ),
      D.a < l → l < r → r < D.b → Ioo l r ⊆ D.cells j →
      ∃ η : HeightPair S,
        (∀ t ∈ Ioo l r, ∀ θ : ℝ,
          heightPairField S η =ᶠ[𝓝 (t, θ)]
            Radial.radialHeightField (referenceRadialPrimitive D)) ∧
        heightPairGrading S n η ≤
          K * T.H (T.sample j) ^ (-(3 / 4 : ℝ)) * T.E0 (T.sample j) ^ A *
            T.M (T.sample j) ^ (n + 1) * radialE (D.cellIndex j) ^ R := by
  obtain ⟨K, A, hK, hA, hnorm⟩ :=
    referencePlateau_physicalNorm_bound hD hT (by norm_num : (0 : ℝ) ≤ 3 / 4) n
  refine ⟨K, A, (2 * n + 2 : ℕ), hK, hA, Nat.cast_nonneg _, ?_⟩
  intro j l r hl hlr hr hcell
  have hgeom : RadialProfileGeometry D := (Classical.choose_spec hD).1
  obtain ⟨η, hηzero, hη, hgerm⟩ := exists_referencePlateau_heightPair hgeom hT hS hl hr
  refine ⟨η, hgerm, ?_⟩
  have hdecode : (S.height (3 / 4 : ℝ)).decode η.1 =
      radialPlateauHeight (referenceRadialPrimitive D) l r (endpointPlateauWidth D l r) := by
    have heq : heightPairField S η = (S.height (3 / 4 : ℝ)).decode η.1 := by
      funext p
      simp only [heightPairField, hηzero, zero_mul, add_zero]
    exact heq.symm.trans hη
  have hmodel := hS.1 (3 / 4 : ℝ)
  have hcoords := hmodel.2.2.2.2.2.2.2
  have hnonneg : 0 ≤ K * T.H (T.sample j) ^ (-(3 / 4 : ℝ)) * T.E0 (T.sample j) ^ A *
      T.M (T.sample j) ^ (n + 1) * radialE (D.cellIndex j) ^ (2 * n + 2) :=
    (Real.sqrt_nonneg _).trans (hnorm j l r hl hlr hr hcell 0 (Nat.zero_le n))
  have hgrade : (S.height (3 / 4 : ℝ)).grading n η.1 ≤
      K * T.H (T.sample j) ^ (-(3 / 4 : ℝ)) * T.E0 (T.sample j) ^ A *
        T.M (T.sample j) ^ (n + 1) * radialE (D.cellIndex j) ^ (2 * n + 2) := by
    apply (gradedSeminorm_le_iff _ _ n η.1 hnonneg).mpr
    intro i hi
    rw [hcoords η.1 i, hdecode]
    exact hnorm j l r hl hlr hr hcell i hi
  have hzero : realGrading n η.2 = 0 := by
    rw [hηzero]
    exact (realGrading n).map_zero'
  simpa only [heightPairGrading, pairGrading_apply, hzero,
    add_zero, Real.rpow_natCast] using hgrade

end ContinuousFlexibility.Statements
