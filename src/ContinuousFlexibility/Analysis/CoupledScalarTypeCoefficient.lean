import ContinuousFlexibility.Analysis.CoupledWeakHeightInputs

/-!
# The normalized scalar type coefficient at the weak profile weight

The denominator is normalized by the actual positive profile. Exponential
profile factors and the smooth reciprocal extension act on weak decaying
heights. The singular reference factors remain proved radial multipliers.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open ContinuousFlexibility.Analysis

set_option backward.isDefEq.respectTransparency false

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}

def coupledWeakProfileEnergy
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (l u : CoupledWeakHeight S) : CoupledWeakHeight S :=
  u + coupledWeakReferenceWCLM hD hT hS
    (coupledWeakReferenceWCLM hD hT hS
      (coupledWeakHeightUnitalAct hT hS (coupledWeakHeightExp hT hS 2 l) u))

private theorem coupled_exp_twice (x : ℝ) : Real.exp (2 * x) = Real.exp x ^ 2 := by
  rw [two_mul, Real.exp_add, pow_two]

theorem coupledWeakProfileEnergy_decode
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (l u : CoupledWeakHeight S) (p : PolarPoint) :
    (S.height coupledWeakProfileWeight).decode (coupledWeakProfileEnergy hD hT hS l u) p =
      (1 + (D.w p.1 * Real.exp ((S.height coupledWeakProfileWeight).decode l p)) ^ 2) *
        (S.height coupledWeakProfileWeight).decode u p := by
  simp only [coupledWeakProfileEnergy, map_add, Pi.add_apply,
    decode_coupledWeakReferenceWCLM, decode_coupledWeakHeightUnitalAct,
    decode_coupledWeakHeightExp, coupled_exp_twice]
  ring

/-- The decaying part of `Q / w`, with both common-height derivatives included. -/
def coupledWeakQDefect
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (l : CoupledWeakHeight S) (u : HeightPair S) (q : ℝ) : CoupledWeakHeight S :=
  q • coupledWeakReferenceInvWCLM hD hT hS
    (coupledWeakHeightUnitalAct hT hS (coupledWeakHeightExp hT hS (-1) l)
      (coupledWeakCommonRadialCLM hD hT hS u +
        coupledWeakProfileEnergy hD hT hS l (coupledWeakCommonAngularCLM hD hT hS u)))

theorem coupledWeakQDefect_decode
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (l : CoupledWeakHeight S) (u : HeightPair S) (q : ℝ) (p : PolarPoint) :
    (S.height coupledWeakProfileWeight).decode (coupledWeakQDefect hD hT hS l u q) p =
      q * (D.w p.1 * Real.exp ((S.height coupledWeakProfileWeight).decode l p))⁻¹ *
        (radialPartial (heightPairField S u) p +
          (1 + (D.w p.1 * Real.exp ((S.height coupledWeakProfileWeight).decode l p)) ^ 2) *
            angularPartial (heightAngular (heightPairField S u)) p) := by
  simp only [coupledWeakQDefect, map_smul, Pi.smul_apply, smul_eq_mul,
    decode_coupledWeakReferenceInvWCLM, decode_coupledWeakHeightUnitalAct,
    decode_coupledWeakHeightExp, map_add, Pi.add_apply,
    coupledWeakCommonRadialCLM_decode, coupledWeakProfileEnergy_decode,
    coupledWeakCommonAngularCLM_decode, neg_one_mul, Real.exp_neg, mul_inv_rev]
  ring

theorem coupledWeakQDefect_zero_of_q
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (l : CoupledWeakHeight S) (u : HeightPair S) :
    coupledWeakQDefect hD hT hS l u 0 = 0 := by
  exact zero_smul ℝ _

/-- The decaying part of `w₀ B`, for an independently supplied normalized Q defect. -/
def coupledWeakTypeCoefficient
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (l d : CoupledWeakHeight S) : CoupledWeakHeight S :=
  coupledWeakReferenceInvRadiusCLM hD hT hS
    (coupledWeakHeightUnitalMul hT hS (coupledWeakHeightExp hT hS (-1) l)
        (coupledWeakHeightInv hT hS d) +
      coupledWeakReferenceWCLM hD hT hS (coupledWeakReferenceWCLM hD hT hS
        (coupledWeakHeightUnitalMul hT hS (coupledWeakHeightExp hT hS 1 l)
          (coupledWeakHeightInv hT hS d))))

theorem coupledWeakTypeCoefficient_decode
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (l d : CoupledWeakHeight S) (p : PolarPoint)
    (hd : |(S.height coupledWeakProfileWeight).decode d p| ≤ 1 / 2) :
    (S.height coupledWeakProfileWeight).decode (coupledWeakTypeCoefficient hD hT hS l d) p =
      p.1⁻¹ *
        ((Real.exp (-(S.height coupledWeakProfileWeight).decode l p) *
            (1 + (S.height coupledWeakProfileWeight).decode d p)⁻¹ - 1) +
          D.w p.1 ^ 2 * (Real.exp ((S.height coupledWeakProfileWeight).decode l p) *
            (1 + (S.height coupledWeakProfileWeight).decode d p)⁻¹ - 1)) := by
  simp only [coupledWeakTypeCoefficient, decode_coupledWeakReferenceInvRadiusCLM,
    map_add, Pi.add_apply, decode_coupledWeakReferenceWCLM,
    decode_coupledWeakHeightUnitalMul, decode_coupledWeakHeightExp,
    decode_coupledWeakHeightInv hT hS d p hd, neg_one_mul, one_mul]
  ring

section Germs

variable {X : Type*} [TopologicalSpace X] [AddCommGroup X] [Module ℝ X]
  {p : ℕ → Seminorm ℝ X} {x0 : X}
  {l d f : X → CoupledWeakHeight S} {u : X → HeightPair S} {q : X → ℝ}

theorem UniformTameGerm.coupledWeakProfileEnergy
    (hl : UniformTameGerm p (coupledWeakHeightGrading S) x0 l) (hl0 : l x0 = 0)
    (hf : UniformTameGerm p (coupledWeakHeightGrading S) x0 f)
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (hp : Monotone p) (ht : WithSeminorms p) :
    UniformTameGerm p (coupledWeakHeightGrading S) x0
      (fun x => coupledWeakProfileEnergy hD hT hS (l x) (f x)) :=
  hf.add ((((hl.coupledWeakHeightExp hl0 hT hS 2 hp ht).coupledWeakHeightUnitalAct
    hf hT hS hp ht).coupledWeakReferenceW hD hT hS hp ht).coupledWeakReferenceW
      hD hT hS hp ht) hp ht

theorem UniformTameGerm.coupledWeakQDefect
    (hl : UniformTameGerm p (coupledWeakHeightGrading S) x0 l) (hl0 : l x0 = 0)
    (hu : UniformTameGerm p (heightPairGrading S) x0 u)
    (hq : UniformTameGerm p realGrading x0 q)
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (hp : Monotone p) (ht : WithSeminorms p) :
    UniformTameGerm p (coupledWeakHeightGrading S) x0
      (fun x => coupledWeakQDefect hD hT hS (l x) (u x) (q x)) := by
  have ha := hu.postcompose hp ht (coupledWeakCommonRadialCLM hD hT hS)
    (coupledWeakCommonRadialCLM_isTame hD hT hS)
  have he := hu.postcompose hp ht (coupledWeakCommonAngularCLM hD hT hS)
    (coupledWeakCommonAngularCLM_isTame hD hT hS)
  have henergy := hl.coupledWeakProfileEnergy hl0 he hD hT hS hp ht
  have hsum := ha.add henergy hp ht
  have hnorm := ((hl.coupledWeakHeightExp hl0 hT hS (-1) hp ht).coupledWeakHeightUnitalAct
    hsum hT hS hp ht).coupledWeakReferenceInvW hD hT hS hp ht
  exact hq.coupledWeakHeightSMul hnorm hS hp ht

theorem UniformTameGerm.coupledWeakTypeCoefficient
    (hl : UniformTameGerm p (coupledWeakHeightGrading S) x0 l) (hl0 : l x0 = 0)
    (hd : UniformTameGerm p (coupledWeakHeightGrading S) x0 d) (hd0 : d x0 = 0)
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (hp : Monotone p) (ht : WithSeminorms p) :
    UniformTameGerm p (coupledWeakHeightGrading S) x0
      (fun x => coupledWeakTypeCoefficient hD hT hS (l x) (d x)) := by
  have hi := hd.coupledWeakHeightInv hd0 hT hS hp ht
  have hm := (hl.coupledWeakHeightExp hl0 hT hS (-1) hp ht).coupledWeakHeightUnitalMul
    hi hT hS hp ht
  have hp' := (hl.coupledWeakHeightExp hl0 hT hS 1 hp ht).coupledWeakHeightUnitalMul
    hi hT hS hp ht
  exact (hm.add ((hp'.coupledWeakReferenceW hD hT hS hp ht).coupledWeakReferenceW
    hD hT hS hp ht) hp ht).coupledWeakReferenceInvRadius hD hT hS hp ht

end Germs

end ContinuousFlexibility.Statements
