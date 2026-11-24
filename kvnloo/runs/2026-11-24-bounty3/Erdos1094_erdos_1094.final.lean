/-
Copyright 2025 The Formal Conjectures Authors.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/
module

public import FormalConjecturesUtil


/-!
# Erdős Problem 1094

*Reference:* [erdosproblems.com/1094](https://www.erdosproblems.com/1094)
-/

@[expose] public section

namespace Erdos1094

open scoped Nat

/-- A carry in any base-$p$ position gives a factor of $p$. -/
private theorem mod_le_mod_of_not_dvd_choose {n k p i : ℕ}
    (hkn : k ≤ n) (hp : p.Prime) (hi : 1 ≤ i) (hin : i ≤ p.log n)
    (h : ¬p ∣ n.choose k) :
    k % (p ^ i) ≤ n % (p ^ i) := by
  have hzero := Nat.factorization_eq_zero_of_not_dvd h
  rw [Nat.factorization_choose hp hkn (Nat.lt_succ_self _)] at hzero
  have hs := Finset.card_eq_zero.mp hzero
  have hc : ¬p ^ i ≤ k % (p ^ i) + (n - k) % (p ^ i) := by
    intro hc
    have : i ∈ (Finset.Ico 1 (p.log n + 1)).filter
        (fun j => p ^ j ≤ k % (p ^ j) + (n - k) % (p ^ j)) :=
      Finset.mem_filter.mpr ⟨Finset.mem_Ico.mpr ⟨hi, Nat.lt_succ_of_le hin⟩, hc⟩
    rw [hs] at this
    exact Finset.notMem_empty _ this
  calc
    k % (p ^ i) ≤ k % (p ^ i) + (n - k) % (p ^ i) := Nat.le_add_right ..
    _ = n % (p ^ i) := by
      conv_rhs => rw [← Nat.add_sub_of_le hkn, Nat.add_mod, Nat.mod_eq_of_lt (lt_of_not_ge hc)]

private theorem minFac_gt_iff_no_carries {n k B : ℕ} (hk : 0 < k) (hkn : k < n) :
    B < (n.choose k).minFac ↔
      ∀ p : ℕ, p.Prime → p ≤ B → ∀ i, 1 ≤ i → i ≤ p.log n →
        k % (p ^ i) ≤ n % (p ^ i) := by
  constructor
  · intro h p hp hpB i hi hin
    apply mod_le_mod_of_not_dvd_choose hkn.le hp hi hin
    intro hd
    exact (not_le_of_gt h) ((Nat.minFac_le_of_dvd hp.two_le hd).trans hpB)
  · intro h
    have hne : n.choose k ≠ 1 := by
      intro he
      rcases Nat.choose_eq_one_iff.mp he with hz | he <;> omega
    apply (Nat.le_minFac.mpr ?_).resolve_left hne
    intro p hp hd
    by_contra! hpB
    have hfac := (hp.dvd_iff_one_le_factorization (Nat.choose_ne_zero hkn.le)).mp hd
    rw [Nat.factorization_choose hp hkn.le (Nat.lt_succ_self _)] at hfac
    obtain ⟨i, hi⟩ := Finset.card_pos.mp hfac
    obtain ⟨hi, hcarry⟩ := Finset.mem_filter.mp hi
    obtain ⟨hlo, hhi⟩ := Finset.mem_Ico.mp hi
    have hmod := h p hp (Nat.lt_succ_iff.mp hpB) i hlo (Nat.lt_succ_iff.mp hhi)
    have he := Nat.add_mod_eq_ite (m := k) (n := n - k) (k := p ^ i)
    rw [Nat.add_sub_of_le hkn.le, if_pos hcarry] at he
    have hb := Nat.mod_lt (n - k) (pow_pos hp.pos i)
    omega

/-- A multiple of $p^a>k$ among the numerator factors forces a carry. -/
private theorem prime_power_dvd_choose_of_dvd_interval {n k m p a : ℕ}
    (hkpos : 0 < k) (hkn : k ≤ n) (hm : n - k < m) (hmn : m ≤ n)
    (hp : p.Prime) (hk : k < p ^ a) (hd : p ^ a ∣ m) :
    p ∣ n.choose k := by
  by_contra h
  have ha : 1 ≤ a := by
    by_contra! ha
    have : a = 0 := by omega
    subst a
    simp only [pow_zero] at hk
    omega
  have han : a ≤ p.log n :=
    (Nat.le_log_iff_pow_le hp.one_lt (by omega)).2
      ((Nat.le_of_dvd (by omega) hd).trans hmn)
  have hsub : n - m < k := by omega
  have hmod : (n - m) % (p ^ a) = n % (p ^ a) :=
    Nat.modEq_of_dvd' (Nat.sub_le n m) (by rwa [Nat.sub_sub_self hmn])
  have hh := mod_le_mod_of_not_dvd_choose hkn hp ha han h
  rw [← hmod, Nat.mod_eq_of_lt hk, Nat.mod_eq_of_lt (hsub.trans hk)] at hh
  omega

/-- In an exception, the largest multiple of $k$ at most $n$ divides the least common multiple
of $1,\dots,k$. -/
private theorem exception_multiple_dvd_lcm {n k : ℕ} (hk : 0 < k) (hkn : 2 * k ≤ n)
    (h : max (n / k) k < (n.choose k).minFac) :
    k * (n / k) ∣ Nat.lcmUpto k := by
  let m := k * (n / k)
  have he : n % k + m = n := Nat.mod_add_div n k
  have hm : n - k < m := by
    have := Nat.mod_lt n hk
    omega
  have hmn : m ≤ n := by omega
  have hmpos : 0 < m := by omega
  rw [← Nat.factorization_prime_le_iff_dvd hmpos.ne' (Nat.lcmUpto_ne_zero k)]
  intro p hp
  rw [Nat.factorization_lcmUpto _ hp]
  by_contra! ht
  let a := m.factorization p
  have hlarge : k < p ^ a := Nat.lt_pow_of_log_lt hp.one_lt ht
  have hdvd : p ^ a ∣ m := Nat.ordProj_dvd m p
  have hp_dvd : p ∣ m := (dvd_pow_self p (by omega)).trans hdvd
  have hp_le : p ≤ max (n / k) k := by
    rcases hp.dvd_mul.mp hp_dvd with hpk | hpq
    · exact (Nat.le_of_dvd hk hpk).trans (le_max_right ..)
    · have hq : 0 < n / k := Nat.div_pos (by omega) hk
      exact (Nat.le_of_dvd hq hpq).trans (le_max_left ..)
  have hpc := prime_power_dvd_choose_of_dvd_interval hk (by omega) hm hmn hp hlarge hdvd
  exact (not_le_of_gt h) ((Nat.minFac_le_of_dvd hp.two_le hpc).trans hp_le)

private theorem exception_upper_bound {n k : ℕ} (hk : 0 < k) (hkn : 2 * k ≤ n)
    (h : max (n / k) k < (n.choose k).minFac) :
    n < Nat.lcmUpto k + k := by
  have he := Nat.mod_add_div n k
  have hr := Nat.mod_lt n hk
  have hm := Nat.le_of_dvd (Nat.lcmUpto_pos k) (exception_multiple_dvd_lcm hk hkn h)
  omega

private theorem bounded_exception_set_finite (K : ℕ) :
    {(n, k) : ℕ × ℕ | k ≤ K ∧ 0 < k ∧ 2 * k ≤ n ∧
      (n.choose k).minFac > max (n / k) k}.Finite := by
  have hmono : Monotone Nat.lcmUpto := by
    intro i j hij
    apply Nat.le_of_dvd (Nat.lcmUpto_pos j)
    rw [Nat.lcmUpto, Nat.lcmUpto]
    exact Finset.lcm_dvd fun x hx =>
      Finset.dvd_lcm (f := id) (Finset.Icc_subset_Icc_right hij hx)
  apply ((Set.finite_Iio (Nat.lcmUpto K + K)).prod (Set.finite_Iic K)).subset
  rintro ⟨n, k⟩ ⟨hkK, hk, hkn, h⟩
  exact ⟨(exception_upper_bound hk hkn h).trans_le
    (Nat.add_le_add (hmono hkK) hkK), hkK⟩

/-- A numerator factor coprime to the binomial coefficient divides its corresponding
coefficient $k\binom{k-1}{r}$. -/
private theorem dvd_mul_choose_of_interval_coprime {n k r : ℕ} (hr : r < k)
    (hkn : k ≤ n) (hcop : (n - r).Coprime (n.choose k)) :
    n - r ∣ k * (k - 1).choose r := by
  let m := n - r
  let s := k - 1 - r
  let c := k * (k - 1).choose r
  have hm : 0 < m := by dsimp [m]; omega
  have hk : 0 < k := by omega
  have hcr : r ≤ k - 1 := by omega
  have hc : c ≠ 0 := mul_ne_zero hk.ne' (Nat.choose_ne_zero hcr)
  have hks : k = r + s + 1 := by dsimp [s]; omega
  have he : c * r ! * s ! = k ! := by
    dsimp [c]
    rw [Nat.mul_assoc, Nat.mul_assoc, ← Nat.mul_assoc ((k - 1).choose r),
      Nat.choose_mul_factorial_mul_factorial hcr, show k = k - 1 + 1 by omega]
    simp only [Nat.add_sub_cancel, ← Nat.factorial_succ]
  rw [← Nat.factorization_prime_le_iff_dvd hm.ne' hc]
  intro p hp
  let a := m.factorization p
  let b := max a (p.log k) + 1
  have hbk : p.log k < b := (le_max_right ..).trans_lt (Nat.lt_succ_self _)
  have hba : a < b := (le_max_left ..).trans_lt (Nat.lt_succ_self _)
  change a ≤ c.factorization p
  by_cases ha : a = 0
  · simp [ha]
  have hpnc : ¬p ∣ n.choose k := fun hd => (Nat.Prime.not_coprime_iff_dvd.mpr
    ⟨p, hp, (dvd_pow_self p ha).trans (Nat.ordProj_dvd m p), hd⟩) hcop
  have hsum : ∑ i ∈ Finset.Ico 1 b, (r / p ^ i + s / p ^ i + if i ≤ a then 1 else 0)
      ≤ ∑ i ∈ Finset.Ico 1 b, k / p ^ i := by
    apply Finset.sum_le_sum
    intro i hi
    let q := p ^ i
    have hq : 0 < q := pow_pos hp.pos _
    have hremr := Nat.mod_add_div r q
    have hremk := Nat.mod_add_div k q
    have hrems := Nat.mod_add_div s q
    have hmul : q * (r / q + s / q) ≤ k := by
      rw [Nat.mul_add]
      omega
    by_cases hia : i ≤ a
    · have hqd : q ∣ m := (pow_dvd_pow p hia).trans (Nat.ordProj_dvd m p)
      have hqm := Nat.le_of_dvd hm hqd
      have hin : i ≤ p.log n := (Nat.le_log_iff_pow_le hp.one_lt (by omega)).mpr
        (hqm.trans (Nat.sub_le ..))
      have hrmod : n % q = r % q := by
        rw [show n = m + r by dsimp [m]; omega, Nat.add_mod,
          Nat.mod_eq_zero_of_dvd hqd, zero_add, Nat.mod_mod]
      have hh := mod_le_mod_of_not_dvd_choose hkn hp (Finset.mem_Ico.mp hi).1 hin hpnc
      change k % q ≤ n % q at hh
      rw [hrmod] at hh
      simp only [if_pos hia]
      change r / q + s / q + 1 ≤ k / q
      by_contra! hh'
      have hmul' := Nat.mul_le_mul_left q (Nat.lt_succ_iff.mp hh')
      rw [Nat.mul_add] at hmul'
      omega
    · simp only [if_neg hia, add_zero]
      exact (Nat.le_div_iff_mul_le hq).2 (by rwa [Nat.mul_comm])
  have hcount :
      ∑ i ∈ Finset.Ico 1 b, (if i ≤ a then 1 else 0 : ℕ) = a := by
    have hh : (Finset.Ico 1 b).filter (fun i => i ≤ a) = Finset.Icc 1 a := by
      ext i
      simp only [Finset.mem_filter, Finset.mem_Ico, Finset.mem_Icc]
      omega
    calc
      _ = ((Finset.Ico 1 b).filter (fun i => i ≤ a)).card :=
        Finset.sum_boole (R := ℕ) _ _
      _ = a := by simp [hh]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, hcount,
    ← Nat.factorization_factorial hp ((Nat.log_mono_right (by omega : r ≤ k)).trans_lt hbk),
    ← Nat.factorization_factorial hp ((Nat.log_mono_right (by omega : s ≤ k)).trans_lt hbk),
    ← Nat.factorization_factorial hp hbk] at hsum
  have hf := congrArg (fun x : ℕ => x.factorization p) he
  rw [Nat.factorization_mul (mul_ne_zero hc (Nat.factorial_ne_zero r))
    (Nat.factorial_ne_zero s), Nat.factorization_mul hc (Nat.factorial_ne_zero r)] at hf
  simp only [Finsupp.coe_add, Pi.add_apply] at hf
  change a ≤ c.factorization p
  omega

private theorem exception_quotient_dvd {n k : ℕ} (hk : 0 < k) (hkn : 2 * k ≤ n)
    (h : max (n / k) k < (n.choose k).minFac) :
    n / k ∣ (k - 1).choose (n % k) := by
  have he : n - n % k = k * (n / k) := by
    have := Nat.mod_add_div n k
    omega
  have hcop : (n - n % k).Coprime (n.choose k) := by
    rw [he]
    simp only [Nat.coprime_mul_iff_left]
    constructor
    · exact (Nat.coprime_of_lt_minFac hk.ne' ((le_max_right ..).trans_lt h)).symm
    · have hnq : 0 < n / k := Nat.div_pos (by omega) hk
      exact (Nat.coprime_of_lt_minFac hnq.ne' ((le_max_left ..).trans_lt h)).symm
  have h₁ := dvd_mul_choose_of_interval_coprime (Nat.mod_lt n hk) (by omega) hcop
  rw [he, Nat.mul_dvd_mul_iff_left hk] at h₁
  exact h₁

private theorem exception_squarefree {n k : ℕ} (hk : 0 < k) (hkn : 2 * k ≤ n)
    (h : max (n / k) k < (n.choose k).minFac) :
    Squarefree (n.choose k) := by
  have hcn : n.choose k ≠ 0 := Nat.choose_ne_zero (by omega)
  apply Nat.squarefree_of_factorization_le_one hcn
  intro p
  by_cases hp : p.Prime
  · by_cases hd : p ∣ n.choose k
    · have hpmax := h.trans_le (Nat.minFac_le_of_dvd hp.two_le hd)
      have hk' : k < p := (le_max_right ..).trans_lt hpmax
      have hq : n / k < p := (le_max_left ..).trans_lt hpmax
      have hn : n < p * k := (Nat.div_lt_iff_lt_mul hk).mp hq
      apply Nat.factorization_choose_le_one
      rw [pow_two]
      exact hn.trans (Nat.mul_lt_mul_of_pos_left hk' hp.pos)
    · simp [Nat.factorization_eq_zero_of_not_dvd hd]
  · simp [Nat.factorization_eq_zero_of_not_prime _ hp]

private theorem exception_remainder_bounds {n k : ℕ} (hk : 0 < k) (hkn : 2 * k ≤ n)
    (h : max (n / k) k < (n.choose k).minFac) :
    0 < n % k ∧ n % k < k - 1 := by
  have hq : 2 ≤ n / k := (Nat.le_div_iff_mul_le hk).2 hkn
  have hr := Nat.mod_lt n hk
  have hd := exception_quotient_dvd hk hkn h
  constructor
  · by_contra! hz
    rw [Nat.le_zero.mp hz, Nat.choose_zero_right] at hd
    exact (show n / k ≠ 1 by omega) (Nat.dvd_one.mp hd)
  · by_contra! hz
    rw [show n % k = k - 1 by omega, Nat.choose_self] at hd
    exact (show n / k ≠ 1 by omega) (Nat.dvd_one.mp hd)

/-- The exception set is finite if and only if its second coordinates are bounded. -/
private theorem finite_exceptions_iff_bounded :
    {(n, k) : ℕ × ℕ | 0 < k ∧ 2 * k ≤ n ∧
      (n.choose k).minFac > max (n / k) k}.Finite ↔
    ∃ K : ℕ, ∀ n k : ℕ, 0 < k → 2 * k ≤ n →
      (n.choose k).minFac > max (n / k) k → k ≤ K := by
  constructor
  · intro h
    obtain ⟨K, hK⟩ := (h.image Prod.snd).bddAbove
    exact ⟨K, fun n k hk hkn hmin => hK ⟨(n, k), ⟨hk, hkn, hmin⟩, rfl⟩⟩
  · rintro ⟨K, hK⟩
    exact (bounded_exception_set_finite K).subset fun ⟨n, k⟩ ⟨hk, hkn, hmin⟩ =>
      ⟨hK n k hk hkn hmin, hk, hkn, hmin⟩

private theorem small_exceptions {n k : ℕ} (hle : k ≤ 4) :
    (0 < k ∧ 2 * k ≤ n ∧ (n.choose k).minFac > max (n / k) k) ↔
    (n = 7 ∧ k = 3) ∨ (n = 13 ∧ k = 4) ∨ (n = 14 ∧ k = 4) := by
  constructor
  · rintro ⟨hk, hkn, h⟩
    obtain ⟨hr, hr'⟩ := exception_remainder_bounds hk hkn h
    have hdiv := exception_quotient_dvd hk hkn h
    have he := Nat.mod_add_div n k
    have hq : 2 ≤ n / k := (Nat.le_div_iff_mul_le hk).2 hkn
    have hk' : k = 3 ∨ k = 4 := by omega
    rcases hk' with rfl | rfl
    · left
      have hrem : n % 3 = 1 := by omega
      rw [hrem] at hdiv
      have hsmall : n / 3 ∣ 2 := hdiv
      have := Nat.le_of_dvd (by decide : 0 < 2) hsmall
      exact ⟨by omega, rfl⟩
    · right
      have hrem : n % 4 = 1 ∨ n % 4 = 2 := by omega
      have hsmall : n / 4 ∣ 3 := by
        rcases hrem with hm | hm <;> rw [hm] at hdiv <;> exact hdiv
      have hq' : n / 4 = 3 := (Nat.dvd_prime Nat.prime_three).mp hsmall |>.resolve_left (by omega)
      have : n = 13 ∨ n = 14 := by omega
      exact this.imp (fun h => ⟨h, rfl⟩) (fun h => ⟨h, rfl⟩)
  · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩) <;>
      norm_num [Nat.choose_eq_descFactorial_div_factorial, Nat.descFactorial, Nat.factorial]

/--
For all $n\ge 2k$ the least prime factor of $\binom{n}{k}$ is $\le\max(n/k,k)$, with only
finitely many exceptions.
-/
@[category research open, AMS 11]
theorem erdos_1094 :
    {(n, k) : ℕ × ℕ | 0 < k ∧ 2 * k ≤ n ∧ (n.choose k).minFac > max (n / k) k}.Finite := by
  sorry

end Erdos1094
