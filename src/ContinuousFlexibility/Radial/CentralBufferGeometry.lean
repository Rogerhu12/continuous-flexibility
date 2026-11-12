import ContinuousFlexibility.Radial.CentralStatementBridges
import ContinuousFlexibility.Statements.RadialTargets

/-!
# Uniform buffers for the genuine central quadratic potential

For j ≥ 2 and T ≥ 8, use cuts ±T, mass j*T/4 and action j*T²/8-6.
The inner walls are exactly ±T/2, and the layer constant is the fixed
number 64. The final constructor retains the specified actual full
inverse; parameter choice and its application to the physical column
are separate from these geometric estimates.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open Real Set Filter MeasureTheory
open scoped Topology ContDiff InnerProductSpace RealInnerProductSpace
open ContinuousFlexibility.Statements

def centralBufferMass (j T : ℝ) : ℝ := j * T / 4

def centralBufferAction (j T : ℝ) : ℝ := j * T ^ 2 / 8 - 6

theorem centralBufferMass_ge_four {j T : ℝ} (hj : 2 ≤ j) (hT : 8 ≤ T) :
    4 ≤ centralBufferMass j T := by
  have hp := mul_le_mul hj hT (by norm_num : (0 : ℝ) ≤ 8) (by linarith : 0 ≤ j)
  unfold centralBufferMass
  nlinarith

theorem centralBufferAction_pos {j T : ℝ} (hj : 2 ≤ j) (hT : 8 ≤ T) :
    0 < centralBufferAction j T := by
  have hT2 : (64 : ℝ) ≤ T ^ 2 := by nlinarith
  have hp := mul_le_mul hj hT2 (by norm_num : (0 : ℝ) ≤ 64) (by linarith : 0 ≤ j)
  unfold centralBufferAction
  nlinarith

theorem centralBuffer_width {j T : ℝ} (hj : 0 < j) (hT : 0 < T) :
    (centralBufferAction j T + 6) / centralBufferMass j T = T / 2 := by
  unfold centralBufferAction centralBufferMass
  field_simp [hj.ne', hT.ne'] <;> ring

theorem centralPotential_quadratic_bounds {j : ℝ} (hj : 2 ≤ j) (x : ℝ) :
    j ^ 2 * (x ^ 2 - 1) ≤ centralPotential j x ∧
      centralPotential j x ≤ j ^ 2 * (x ^ 2 + 1) := by
  have hA : centralOscillatorA ≤ 1 := by
    nlinarith [centralOscillatorA_sq, centralOscillatorA_pos]
  have hR : centralRadiusA ^ 2 ≤ 2 := by
    rw [centralRadiusA_sq]
    linarith
  have hj2 : (4 : ℝ) ≤ j ^ 2 := by nlinarith
  unfold centralPotential
  constructor
  · nlinarith [sq_nonneg centralRadiusA,
      mul_nonneg (sq_nonneg j) (sub_nonneg.mpr hA)]
  · nlinarith [mul_nonneg (sq_nonneg j) centralOscillatorA_pos.le]

theorem centralPotential_exterior_mass_bound {j T x : ℝ}
    (hj : 2 ≤ j) (hT : 8 ≤ T) (hx : x ≤ -T / 2 ∨ T / 2 ≤ x) :
    centralBufferMass j T ^ 2 ≤ centralPotential j x := by
  have hT2 : (64 : ℝ) ≤ T ^ 2 := by nlinarith
  have hx2 : T ^ 2 / 4 ≤ x ^ 2 := by
    rcases hx with hx | hx
    · nlinarith [mul_nonneg (show 0 ≤ -x - T / 2 by linarith)
        (show 0 ≤ -x + T / 2 by linarith)]
    · nlinarith [mul_nonneg (show 0 ≤ x - T / 2 by linarith)
        (show 0 ≤ x + T / 2 by linarith)]
  have hbase : T ^ 2 / 16 ≤ x ^ 2 - 1 := by nlinarith
  calc
    centralBufferMass j T ^ 2 = j ^ 2 * (T ^ 2 / 16) := by
      unfold centralBufferMass
      ring
    _ ≤ j ^ 2 * (x ^ 2 - 1) := mul_le_mul_of_nonneg_left hbase (sq_nonneg j)
    _ ≤ _ := (centralPotential_quadratic_bounds hj x).1

theorem centralPotential_near_mass_bound {j T x a : ℝ}
    (hj : 2 ≤ j) (hT : 8 ≤ T) (ha : |a| ≤ T)
    (hx : |x - a| ≤ 4 / centralBufferMass j T) :
    centralPotential j x ≤ 64 * centralBufferMass j T ^ 2 := by
  have hm4 := centralBufferMass_ge_four hj hT
  have hm : 0 < centralBufferMass j T := by linarith
  have hw : 4 / centralBufferMass j T ≤ 1 :=
    (div_le_iff₀ hm).mpr (by simpa only [one_mul] using hm4)
  have hxabs : |x| ≤ 3 * T / 2 := by
    calc
      |x| = |(x - a) + a| := by congr 1; ring
      _ ≤ |x - a| + |a| := abs_add_le _ _
      _ ≤ 4 / centralBufferMass j T + T := add_le_add hx ha
      _ ≤ 3 * T / 2 := by linarith
  have hx2 : x ^ 2 ≤ (3 * T / 2) ^ 2 := by
    simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg x) hxabs 2
  have hT2 : (64 : ℝ) ≤ T ^ 2 := by nlinarith
  have hbase : x ^ 2 + 1 ≤ 4 * T ^ 2 := by nlinarith
  calc
    centralPotential j x ≤ j ^ 2 * (x ^ 2 + 1) :=
      (centralPotential_quadratic_bounds hj x).2
    _ ≤ j ^ 2 * (4 * T ^ 2) := mul_le_mul_of_nonneg_left hbase (sq_nonneg j)
    _ = 64 * centralBufferMass j T ^ 2 := by unfold centralBufferMass; ring

def centralModelBuffer (j T B₀ : ℝ) (bordered : Bool)
    (g : RadialL2) (f : ℝ → ℝ) : BufferData where
  bordered := bordered
  potential := centralPotential j
  border := g
  l := -T
  h := T
  mass := fun _ => centralBufferMass j T
  action := fun _ => centralBufferAction j T
  B₀ := B₀
  layerBound := 64
  borderFunction := f

theorem centralModelBuffer_innerWall {j T B₀ : ℝ} (bordered : Bool)
    (g : RadialL2) (f : ℝ → ℝ) (hj : 0 < j) (hT : 0 < T) (i : Fin 2) :
    bufferInnerWall (centralModelBuffer j T B₀ bordered g f) i =
      if i = 0 then -T / 2 else T / 2 := by
  unfold bufferInnerWall bufferCut bufferSign
  dsimp only [centralModelBuffer]
  rw [mul_div_assoc, centralBuffer_width hj hT]
  split_ifs <;> ring

/-- All the exact frozen buffer hypotheses, with a given actual full
inverse of the specified central model. -/
theorem centralModelBuffer_hypotheses {j T B₀ : ℝ} (bordered : Bool)
    (g : RadialL2) (f : ℝ → ℝ)
    (hj : 2 ≤ j) (hT : 8 ≤ T) (hB₀ : 0 < B₀)
    (hs : ContDiff ℝ ∞ f) (hc : HasCompactSupport f)
    (hae : (g : ℝ → ℝ) =ᵐ[volume] f)
    (hsupp : Function.support f ⊆ Ioo (-T / 2) (T / 2))
    (H : (RadialL2 × ℝ) →L[ℝ] (RadialL2 × ℝ)) (hHnorm : ‖H‖ ≤ B₀)
    (hHsolve : ∀ F, (bordered = false → F.2 = 0) →
      BorderedFullGraph (centralPotential j) g bordered (H F) F)
    (hHunique : ∀ U F, BorderedFullGraph (centralPotential j) g bordered U F → H F = U) :
    BufferHypotheses (centralModelBuffer j T B₀ bordered g f) := by
  have hjpos : 0 < j := by linarith
  have hTpos : 0 < T := by linarith
  have hm : 0 < centralBufferMass j T := by linarith [centralBufferMass_ge_four hj hT]
  have hext : (g : ℝ → ℝ) =ᵐ[volume.restrict ((Ioo (-T) T)ᶜ)] (fun _ => 0) := by
    filter_upwards [ae_restrict_of_ae hae, ae_restrict_mem measurableSet_Ioo.compl] with x hx hout
    have hz : f x = 0 := by
      by_contra hne
      have hi := hsupp hne
      exact hout ⟨by linarith [hi.1], by linarith [hi.2]⟩
    change g x = 0
    exact hx.trans hz
  refine ⟨by change -T < T; linarith, ?_, hB₀, by change (0 : ℝ) < 64; norm_num,
    ?_, centralActualClosedFormRealization hjpos, hs, hc, hae, ?_, ?_, hext, ?_, ?_, ?_⟩
  · simp only [centralModelBuffer_innerWall bordered g f hjpos hTpos]
    norm_num <;> linarith
  · change ContDiff ℝ ∞ (centralPotential j)
    unfold centralPotential
    fun_prop
  · change Function.support f ⊆ Ioo
      (bufferInnerWall (centralModelBuffer j T B₀ bordered g f) 0)
      (bufferInnerWall (centralModelBuffer j T B₀ bordered g f) 1)
    rw [centralModelBuffer_innerWall bordered g f hjpos hTpos 0,
      centralModelBuffer_innerWall bordered g f hjpos hTpos 1]
    simpa using hsupp
  · intro i
    exact ⟨hm, centralBufferAction_pos hj hT⟩
  · intro i x hx
    by_cases hi : i = 0
    · have hx' : x ≤ -T + (centralBufferAction j T + 6) / centralBufferMass j T := by
        simpa [centralModelBuffer, hi] using hx
      rw [centralBuffer_width hjpos hTpos] at hx'
      exact centralPotential_exterior_mass_bound hj hT (Or.inl (by linarith))
    · have hx' : T - (centralBufferAction j T + 6) / centralBufferMass j T ≤ x := by
        simpa [centralModelBuffer, hi] using hx
      rw [centralBuffer_width hjpos hTpos] at hx'
      exact centralPotential_exterior_mass_bound hj hT (Or.inr (by linarith))
  · intro i x hx
    have hcut : |bufferCut (centralModelBuffer j T B₀ bordered g f) i| ≤ T := by
      by_cases hi : i = 0 <;> simp [bufferCut, centralModelBuffer, hi, abs_of_pos hTpos]
    have hwall : |bufferInnerWall (centralModelBuffer j T B₀ bordered g f) i| ≤ T := by
      rw [centralModelBuffer_innerWall bordered g f hjpos hTpos]
      split_ifs <;> apply abs_le.mpr <;> constructor <;> linarith
    rcases hx with hx | hx
    · exact centralPotential_near_mass_bound hj hT hcut hx
    · exact centralPotential_near_mass_bound hj hT hwall hx
  · exact ⟨H, hHnorm, hHsolve, hHunique⟩

end ContinuousFlexibility.Radial
