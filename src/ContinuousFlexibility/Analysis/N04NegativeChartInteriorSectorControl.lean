import ContinuousFlexibility.Analysis.N04NegativeChartInteriorSpeedBounds
import ContinuousFlexibility.Analysis.SmoothDirectionsAffine

/-! The actual interior speed control on one stable sector neighborhood. -/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set ContinuousFlexibility.Statements ContinuousFlexibility.Blueprint CanonicalGeometry
open scoped ContDiff

private def interiorControl_affine
    {X Y I : Type*}
    [TopologicalSpace X] [AddCommGroup X] [Module ℝ X]
    [IsTopologicalAddGroup X] [ContinuousSMul ℝ X]
    [TopologicalSpace Y] [AddCommGroup Y] [Module ℝ Y]
    [IsTopologicalAddGroup Y] [ContinuousSMul ℝ Y]
    {p : ℕ → Seminorm ℝ X} {q : ℕ → Seminorm ℝ Y}
    {center : Y} {base loss : ℕ} {U : Set X} {V : Set Y}
    {Ω : I → Set PolarPoint} {δ H E : I → PolarPoint → ℝ}
    {f : I → Y → PolarPoint → ℝ} {g : I → X → PolarPoint → ℝ}
    (L : X →L[ℝ] Y) (hU : IsOpen U)
    (hmap : MapsTo (fun x => center + L x) U V)
    (hgrade : ∀ n x, q n (L x) = p n x)
    (F : EndpointPowerControl q center base loss V Ω δ H E f)
    (heq : ∀ i x, g i x = f i (center + L x)) :
    EndpointPowerControl p 0 base loss U Ω δ H E g := by
  have hjet (i : I) (a b : ℕ) (y : PolarPoint) (x : X) :
      mixedDerivative a b (g i x) y = mixedDerivative a b (f i (center + L x)) y :=
    congrArg (fun u : PolarPoint → ℝ => mixedDerivative a b u y) (heq i x)
  let R (i : I) : MixedJetRegularity U (Ω i) (g i) := {
    spatial := fun x hx => ((F.regular i).spatial (center + L x) (hmap hx)).congr
      (fun y _ => congrFun (heq i x) y)
    parameter := fun a b y hy =>
      (((F.regular i).parameter a b y hy).compAffine L center hU hmap).congr
        (fun x _ => (hjet i a b y x).symm) }
  refine ⟨R, ?_⟩
  intro K s
  obtain ⟨C, A, hC, hA, hb⟩ := F.bounds K s
  refine ⟨C, A, hC, hA, ?_⟩
  intro i k hk a b hab y hy J x hx hlow v hv Q hQ hhigh hvhigh
  let JF : SmoothDirections V (fun z => mixedDerivative a b (f i z) y) :=
    (F.regular i).parameter a b y hy
  have he : J.D k x v = JF.D k (center + L x) (fun j => L (v j)) := by
    apply (congrArg (fun A : X [×k]→L[ℝ] ℝ => A v)
      (J.unique ((R i).parameter a b y hy) k x hx)).trans
    change (JF.compAffine L center hU hmap).D k x v = _
    exact JF.compAffine_apply L center hU hmap k x v
  have hstate (n : ℕ) : q n ((center + L x) - center) = p n (x - 0) := by
    rw [add_sub_cancel_left, hgrade, sub_zero]
  have hb' := hb i k hk a b hab y hy JF (center + L x) (hmap hx)
    ((hstate base).trans_le hlow) (fun j => L (v j))
    (fun j => (hgrade base (v j)).trans_le (hv j)) Q hQ
    ((hstate (s + loss)).trans_le hhigh)
    (fun j => (hgrade (s + loss) (v j)).trans_le (hvhigh j))
  exact (congrArg (fun t : ℝ => δ i y ^ a * ‖t‖) he).trans_le hb'

namespace N04RealizationStart

variable (W : N04RealizationStart)

def negativeInteriorPhysicalDomain (ρ : ℕ → ℝ) (i : ℕ × Bool) : Set PolarPoint :=
  W.negativeInwardPoint i.1 i.2 ''
    (Icc (ρ i.1 / 2) (W.negativeOpticalWidth i.1 i.2) ×ˢ univ)

theorem negativeInteriorPhysicalDomain_subset (ρ : ℕ → ℝ) (hρ : ∀ m, 0 < ρ m)
    (i : ℕ × Bool) : W.negativeInteriorPhysicalDomain ρ i ⊆
      Ioo (W.C.left i.1) (W.C.right i.1) ×ˢ (univ : Set ℝ) := by
  rintro _ ⟨p, hp, rfl⟩
  exact ⟨W.negativeInteriorRadius_component ρ hρ i.1 i.2 hp.1, mem_univ _⟩

variable (e : ℕ ≃ N04PieceIndex W.D) (ρ : ℕ → ℝ)
  (hρ : ∀ m, 0 < ρ m ∧ ρ m ≤ W.negativeMaterialCollar m)
  (hρb : ∃ B A : ℝ, 0 < B ∧ 0 ≤ A ∧ ∀ m side,
    (ρ m)⁻¹ ≤ B * W.T.E0 (W.negativeHalfSample e m side) ^ A)

private def negativeInterior_originalSpeedControl
    {base loss : ℕ} {ε : ℝ}
    (G : WholeCharacteristicSpeedPowerControl W.D W.T W.S W.C base loss ε) :
    EndpointPowerControl (pairGrading (stateGrading W.S) realGrading)
      (W.C.referenceState, 0) base loss (stateNeighborhood W.S W.C base ε)
      (W.negativeInteriorPhysicalDomain ρ) (fun _ _ => 1)
      (fun i _ => W.T.H (W.negativeHalfSample e i.1 i.2) ^ (3 / 4 : ℝ))
      (fun i _ => W.T.E0 (W.negativeHalfSample e i.1 i.2))
      (fun _ z => minusCharacteristicSpeed (originalCoefficients W.D W.S W.C z)) := by
  refine ⟨fun i => ⟨fun z hz => ((G.regular i.1).spatial z hz).mono
    (W.negativeInteriorPhysicalDomain_subset ρ (fun m => (hρ m).1) i),
    fun a b q hq => (G.regular i.1).parameter a b q
      (W.negativeInteriorPhysicalDomain_subset ρ (fun m => (hρ m).1) i hq)⟩, ?_⟩
  intro K s
  obtain ⟨C, A, hC, hA, hb⟩ := W.negativeInterior_speed_power_bounds e ρ hρ hρb G K s
  refine ⟨C, A, hC, hA, ?_⟩
  rintro ⟨m, side⟩ k hk a b hab _ ⟨p, hp, rfl⟩ J z hz hlow v hv R hR hhigh hvhigh
  simpa only [one_pow, one_mul] using
    hb m side p hp.1 k hk a b hab J z hz hlow v hv R hR hhigh hvhigh

/-- All values are the original physical speed, on the actual overlap
interior. No open extension of the closed interior set is chosen. -/
def NegativeInteriorSpeedControl (base loss : ℕ) (ε : ℝ) : Type :=
  EndpointPowerControl (parameterGrading W.S) 0 base loss
    (sectorNeighborhood W.S base ε ε) (W.negativeInteriorPhysicalDomain ρ)
    (fun _ _ => 1)
    (fun i _ => W.T.H (W.negativeHalfSample e i.1 i.2) ^ (3 / 4 : ℝ))
    (fun i _ => W.T.E0 (W.negativeHalfSample e i.1 i.2))
    (fun _ z => minusCharacteristicSpeed
      (originalCoefficients W.D W.S W.C (liftSectorParameter W.S W.C z)))

def negativeInterior_sectorSpeedControl
    {base loss : ℕ} {ε : ℝ}
    (G : WholeCharacteristicSpeedPowerControl W.D W.T W.S W.C base loss ε) :
    W.NegativeInteriorSpeedControl e ρ base loss ε :=
  interiorControl_affine (sectorParameterInclusion W.S)
    (sectorNeighborhood_isOpen W.S base ε ε)
    (fun x hx => (liftSectorParameter_eq_affine W.S W.C x) ▸
      liftSectorParameter_mem_stateNeighborhood hx le_rfl)
    (pairGrading_sectorParameterInclusion W.S)
    (W.negativeInterior_originalSpeedControl e ρ hρ hρb G)
    (fun _ x => congrArg
      (fun z => minusCharacteristicSpeed (originalCoefficients W.D W.S W.C z))
      (liftSectorParameter_eq_affine W.S W.C x))

/-- The low base, radius and raw spatial loss precede all state and
spatial orders, and survive every later common neighborhood restriction. -/
include hρ hρb in
theorem negativeInterior_stable_speedControl :
    ∃ base : ℕ, ∃ ε : ℝ, ∃ loss : ℕ,
      W.base ≤ base ∧ 0 < ε ∧ ε ≤ min W.ε (1 / 2 : ℝ) ∧
      ∀ b : ℕ, base ≤ b → ∀ η : ℝ, 0 < η → η ≤ ε →
        Nonempty (W.NegativeInteriorSpeedControl e ρ b loss η) := by
  have h01 := W.through03.1.1
  have hA : N01PartA W.D W.T W.S W.C :=
    ⟨h01.1, h01.2.2.1, h01.2.2.2.1, h01.2.2.2.2.1, h01.2.2.2.2.2.1⟩
  have hB : N01PartB W.D W.S W.C W.base W.ε :=
    ⟨h01.2.2.2.2.2.2.1, h01.2.2.2.2.2.2.2.1,
      h01.2.2.2.2.2.2.2.2.1, h01.2.2.2.2.2.2.2.2.2.1,
      h01.2.2.2.2.2.2.2.2.2.2.1⟩
  obtain ⟨base, ε, loss, hb, hε, hεW, hG⟩ :=
    n01_exists_stable_commonWholeSpeed_powerControl W.hS W.hT hA W.ε_pos hB
      W.primitive (fun r _ => W.floor r)
  refine ⟨base, ε, loss, hb, hε, hεW, fun b hbb η hη hηε => ?_⟩
  obtain ⟨G⟩ := hG b hbb η hη hηε
  exact ⟨W.negativeInterior_sectorSpeedControl e ρ hρ hρb G⟩

end N04RealizationStart
end ContinuousFlexibility.Analysis

/-- info: 'ContinuousFlexibility.Analysis.N04RealizationStart.negativeInterior_stable_speedControl'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ContinuousFlexibility.Analysis.N04RealizationStart.negativeInterior_stable_speedControl
