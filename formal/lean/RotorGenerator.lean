import RotorMatching
import Mathlib.Analysis.Normed.Algebra.MatrixExponential

open scoped BigOperators Matrix.Norms.Operator
open IncrementCycles RotorEnclosure

namespace RotorGenerator
noncomputable section

abbrev Mat := Matrix (Fin 6) (Fin 6) ℝ

def jump (a : ℝ) : Mat := fun i j =>
  (if i=j-1 then forward a else 0)+(if i=j+1 then backward a else 0)

def generator (a : ℝ) : Mat := jump a-1

theorem jump_power (a : ℝ) (n : ℕ) (i j : Fin 6) :
    (jump a ^ n) i j = walk a n (j-i) := by
  induction n generalizing j with
  | zero =>
    simp only [pow_zero, Matrix.one_apply,walk,sub_eq_zero]
    simp [eq_comm]
  | succ n ih =>
    simp only [pow_succ,Matrix.mul_apply,jump,mul_add,mul_ite,mul_zero,
      Finset.sum_add_distrib,Finset.sum_ite_eq',Finset.mem_univ,if_true,ih,walk]
    congr 1 <;> congr 1 <;> abel_nf

set_option maxHeartbeats 2000000 in
theorem matrix_exp_jump (u a : ℝ) (i j : Fin 6) :
    (NormedSpace.exp (u • jump a) : Mat) i j = ∑' n, poissonWeight u n * walk a n (j-i) := by
  let f (n : ℕ) : Mat := ((↑n.factorial : ℚ)⁻¹) • (u • jump a)^n
  have hs : Summable f := NormedSpace.expSeries_summable' (𝕂 := ℚ) (u • jump a)
  have hev : Continuous (fun M : Mat => M i j) :=
    (continuous_apply j).comp (continuous_apply i)
  let ev : Mat →+ ℝ := ⟨⟨fun M => M i j, rfl⟩, fun _ _ => rfl⟩
  have h : HasSum (fun n => ev (f n)) (ev (∑' n, f n)) :=
    hs.hasSum.map ev hev
  rw [NormedSpace.exp_eq_tsum_rat]
  change ev (∑' n, f n) = _
  rw [← h.tsum_eq]
  refine tsum_congr fun n => ?_
  dsimp [ev,f]
  rw [smul_pow]
  simp only [Matrix.smul_apply,smul_eq_mul,jump_power,poissonWeight]
  simp only [Rat.smul_def,Rat.cast_inv,Rat.cast_natCast,div_eq_mul_inv]
  ring

theorem matrix_exp_identity (u : ℝ) :
    (NormedSpace.exp (u • (1 : Mat)) : Mat) = Real.exp u • (1 : Mat) := by
  rw [Matrix.smul_one_eq_diagonal,Matrix.exp_diagonal,Matrix.smul_one_eq_diagonal,Real.exp_eq_exp_ℝ,Pi.exp_def]

theorem sampled_ctmc (u a : ℝ) (i j : Fin 6) :
    (NormedSpace.exp (u • generator a) : Mat) i j = kernel u a (j-i) := by
  unfold generator
  rw [smul_sub,sub_eq_add_neg, ← neg_smul,
    Matrix.exp_add_of_commute (_ : Mat) (_ : Mat) (by
      unfold Commute SemiconjBy
      simp only [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one,Matrix.one_mul,smul_smul,mul_comm])]
  rw [matrix_exp_identity]
  simp only [Matrix.mul_smul,Matrix.mul_one,Matrix.smul_apply,smul_eq_mul,matrix_exp_jump,kernel]
  rw [Real.exp_neg,div_eq_mul_inv,mul_comm]

theorem generator_rates (a : ℝ) (i : Fin 6) :
    generator a i (i+1) = (1+a)/2 ∧
    generator a i (i-1) = (1-a)/2 ∧ generator a i i = -1 := by
  have h : ∀ j : Fin 6, j ≠ j+1+1 ∧ j ≠ j-1-1 ∧ j ≠ j+1 ∧ j ≠ j-1 := by decide
  obtain ⟨h2,h2',h1,h1'⟩ := h i
  simp [generator,jump,forward,backward,Matrix.sub_apply,h2,h2',h1,h1']

theorem sampled_stochastic {u a : ℝ} (hu : 0 ≤ u) (ha : -1 ≤ a ∧ a ≤ 1) :
    let P := (NormedSpace.exp (u • generator a) : Mat)
    (∀ i j, 0 ≤ P i j) ∧ (∀ i, ∑ j, P i j = 1) ∧
    (∀ j, ∑ i, (1/6 : ℝ) * P i j = 1/6) := by
  dsimp only
  have ht : (∑ d : Fin 6, kernel u a d) = 1 := by
    simpa [RotorMatching.total,RotorRational.sites,listVal,Fin.sum_univ_succ] using
      RotorMatching.kernel_total_at hu ha
  refine ⟨?_,?_,?_⟩
  · intro i j
    rw [sampled_ctmc]
    unfold kernel
    exact div_nonneg
      (tsum_nonneg (fun n => mul_nonneg (poisson_nonneg hu n) (walk_nonneg_le_one ha n _).1))
      (Real.exp_pos u).le
  · intro i
    simp only [sampled_ctmc]
    have hh : (∑ j, kernel u a (j-i)) = ∑ d, kernel u a d :=
      Equiv.sum_comp (Equiv.subRight i) (kernel u a)
    exact hh.trans ht
  · intro j
    simp only [sampled_ctmc, ← Finset.mul_sum]
    let e : Equiv.Perm (Fin 6) := ⟨fun i => j-i, fun i => j-i,
      fun i => sub_sub_cancel j i, fun i => sub_sub_cancel j i⟩
    have hh : (∑ i, kernel u a (j-i)) = ∑ d, kernel u a d :=
      Equiv.sum_comp e (kernel u a)
    rw [hh,ht,mul_one]

end
end RotorGenerator
