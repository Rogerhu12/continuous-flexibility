import ContinuousFlexibility.Analysis.N01cFiniteAffineInputs
import ContinuousFlexibility.Analysis.N01cNormalizedSpeedPowerBounds

/-!
# Joint finite-affine smoothness of the actual normalized speed factors

The state exponent and polar inputs are genuine continuous-linear
fields. Their finite-affine restrictions are jointly smooth with the
physical point. The original N01b inequalities keep the two actual
denominators away from zero on the same neighbourhood.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open Set ContinuousFlexibility.Analysis ContinuousFlexibility.Blueprint
open scoped ContDiff

set_option backward.isDefEq.respectTransparency true

theorem contDiffOn_normalizedSpeedFactor_finiteAffine
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {base : ℕ} {ε : ℝ}
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    (hA : N01PartA D T S C) (hB : N01PartB D S C base ε)
    {m : ℕ} (x : AnnularState S × ℝ)
    (L : (Fin m → ℝ) →L[ℝ] (AnnularState S × ℝ)) (i : Fin 2) :
    ContDiffOn ℝ ∞ (fun p : (Fin m → ℝ) × PolarPoint =>
      normalizedSpeedFactor D S C i (x + L p.1) p.2)
      (((fun q => x + L q) ⁻¹' stateNeighborhood S C base ε) ×ˢ annularOpen D) := by
  let Z : (Fin m → ℝ) → AnnularState S × ℝ := fun q => x + L q
  let V : Set ((Fin m → ℝ) × PolarPoint) :=
    (Z ⁻¹' stateNeighborhood S C base ε) ×ˢ annularOpen D
  let V₀ : Set ((Fin m → ℝ) × PolarPoint) := univ ×ˢ annularOpen D
  have hVV : V ⊆ V₀ := fun p hp => ⟨mem_univ _, hp.2⟩
  have hD : RadialProfileGeometry D := hA.1.1.choose_spec.1
  let π : (AnnularState S × ℝ) →L[ℝ] AnnularState S :=
    ContinuousLinearMap.fst ℝ (AnnularState S) ℝ
  let w : (Fin m → ℝ) × PolarPoint → ℝ :=
    fun p => stateProfile D S C (Z p.1).1 p.2.1
  let c : (Fin m → ℝ) × PolarPoint → ℝ := fun p => (Z p.1).2
  let u : Fin 5 → (Fin m → ℝ) × PolarPoint → ℝ :=
    fun j p => stateUPolarInput S j (Z p.1).1 p.2
  have hexp : ContDiffOn ℝ ∞ (fun p : (Fin m → ℝ) × PolarPoint =>
      (Z p.1).1.2.1 * D.chi p.2.1 + stateControlSum C (Z p.1).1 p.2.1) V₀ := by
    refine contDiffOn_finiteAffine_linearField
      (fun y : AnnularState S × ℝ => fun q : PolarPoint =>
        y.1.2.1 * D.chi q.1 + stateControlSum C y.1 q.1)
      (fun q hq => (stateProfileExponentCLM hS hT hA.1.1 hA.2.2.1 q.1 hq.1).comp π)
      ?_ ?_ x L
    · intro q hq y
      rw [ContinuousLinearMap.comp_apply, π, ContinuousLinearMap.fst_apply,
        stateProfileExponentCLM_apply]
    · intro y
      exact ((contDiff_const.mul hA.1.2.2.2.1.1).contDiffOn.add
        (contDiffOn_stateControlSum hA.2.2.1 y.1)).comp contDiff_fst.contDiffOn
          (fun q hq => hq.1)
  have hw : ContDiffOn ℝ ∞ w V :=
    (((hD.2.2.1.1.comp (contDiff_fst.comp contDiff_snd)).contDiffOn).mul hexp.exp).mono hVV
  have hc : ContDiffOn ℝ ∞ c V := by
    have hc₀ : ContDiffOn ℝ ∞ c V₀ := contDiffOn_finiteAffine_linearField
      (fun y : AnnularState S × ℝ => fun _ : PolarPoint => y.2)
      (fun _ _ => ContinuousLinearMap.snd ℝ (AnnularState S) ℝ)
      (fun _ _ _ => by rw [ContinuousLinearMap.snd_apply])
      (fun _ => contDiffOn_const) x L
    exact hc₀.mono hVV
  have hu (j : Fin 5) : ContDiffOn ℝ ∞ (u j) V := by
    have hu₀ : ContDiffOn ℝ ∞ (u j) V₀ := contDiffOn_finiteAffine_linearField
      (fun y : AnnularState S × ℝ => stateUPolarInput S j y.1)
      (fun q hq => (stateUPolarInputCLM hT hS q hq j).comp π)
      (fun q hq y => by
        rw [ContinuousLinearMap.comp_apply, π, ContinuousLinearMap.fst_apply,
          stateUPolarInputCLM_apply hT hS q hq (hD.1.trans hq.1.1).ne'])
      (fun y => contDiffOn_stateUPolarInput hT hS hD.1 y.1 j) x L
    exact hu₀.mono hVV
  let e : (Fin m → ℝ) × PolarPoint → ℝ := fun p => 1 + w p ^ 2
  let d : (Fin m → ℝ) × PolarPoint → ℝ := fun p =>
    1 - 2 * w p * c p * u 0 p - c p ^ 2 * ((u 0 p) ^ 2 + e p * (u 1 p) ^ 2)
  let qn : (Fin m → ℝ) × PolarPoint → ℝ := fun p =>
    1 + c p * ((u 0 p + e p * u 4 p) / w p)
  have he (p) : e p = profileEnergy (stateProfile D S C (Z p.1).1) p.2 := rfl
  have hu0 (p) : u 0 p = heightRadial (stateU S (Z p.1).1) p.2 := rfl
  have hu1 (p) : u 1 p = heightAngular (stateU S (Z p.1).1) p.2 := rfl
  have hu3 (p) : u 3 p = radialPartial (heightAngular (stateU S (Z p.1).1)) p.2 := by
    change stateUPolarInput S 3 (Z p.1).1 p.2 = _
    rw [← show (0 : Fin 2).succ.succ.succ = (3 : Fin 5) from by decide]
    simp only [stateUPolarInput, Fin.cases_succ, Fin.cases_zero]
  have hu4 (p) : u 4 p = angularPartial (heightAngular (stateU S (Z p.1).1)) p.2 := by
    change stateUPolarInput S 4 (Z p.1).1 p.2 = _
    rw [← show (0 : Fin 1).succ.succ.succ.succ = (4 : Fin 5) from by decide]
    simp only [stateUPolarInput, Fin.cases_succ, Fin.cases_zero]
  have hd (p) : d p =
      polarDiscriminant (stateProfile D S C (Z p.1).1) (stateHeight D S C (Z p.1)) p.2 := by
    rw [n01_polarDiscriminant_stateHeight hS hT hA]
    dsimp only [d]
    rw [hu0, hu1, he]
  have hqn (p) (hp : p ∈ V) : qn p =
      heightQ (profileEnergy (stateProfile D S C (Z p.1).1) p.2)
        (heightRadial (stateHeight D S C (Z p.1)) p.2)
        (angularPartial (heightAngular (stateHeight D S C (Z p.1))) p.2) / w p := by
    rw [n01_heightQ_div_profile hS hT hA hB hp.1 hp.2]
    dsimp only [qn]
    rw [hu0, hu4, he]
  have hwp (p) (hp : p ∈ V) : w p ≠ 0 :=
    (n01PartB_denominators_pos hD hS hA.2.1 hB hp.1 hp.2).1.ne'
  have hdp (p) (hp : p ∈ V) : d p ≠ 0 := by
    rw [hd]
    exact (n01PartB_denominators_pos hD hS hA.2.1 hB hp.1 hp.2).2.2.ne'
  have hqp (p) (hp : p ∈ V) : qn p ≠ 0 := by
    rw [hqn p hp]
    exact (div_pos (n01PartB_denominators_pos hD hS hA.2.1 hB hp.1 hp.2).2.1
      (n01PartB_denominators_pos hD hS hA.2.1 hB hp.1 hp.2).1).ne'
  have hec : ContDiffOn ℝ ∞ e V := contDiffOn_const.add (hw.pow 2)
  have hdc : ContDiffOn ℝ ∞ d V :=
    (contDiffOn_const.sub (((contDiffOn_const.mul hw).mul hc).mul (hu 0))).sub
      ((hc.pow 2).mul (((hu 0).pow 2).add (hec.mul ((hu 1).pow 2))))
  have hqc : ContDiffOn ℝ ∞ qn V :=
    contDiffOn_const.add (hc.mul (((hu 0).add (hec.mul (hu 4))).div hw hwp))
  by_cases hi : i = 0
  · have ha : ContDiffOn ℝ ∞
        (fun p => e p * (c p * u 3 p) / (w p * qn p)) V :=
      (hec.mul (hc.mul (hu 3))).div (hw.mul hqc)
        (fun p hp => mul_ne_zero (hwp p hp) (hqp p hp))
    exact ha.congr (fun p hp => by
      simp only [normalizedSpeedFactor, if_pos hi]
      rw [← hqn p hp,
        radialPartial_heightAngular_stateHeight hS hT hA (Z p.1)
          (hD.1.trans hp.2.1.1).ne', ← he p, ← hu3 p])
  · have hb : ContDiffOn ℝ ∞ (fun p => Real.sqrt (d p) / qn p) V :=
      (hdc.sqrt hdp).div hqc hqp
    exact hb.congr (fun p hp => by
      simp only [normalizedSpeedFactor, if_neg hi]
      rw [← hd p, ← hqn p hp])

end ContinuousFlexibility.Statements
