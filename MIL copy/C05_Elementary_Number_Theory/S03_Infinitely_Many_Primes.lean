import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Tactic
import Mathlib.Util.Delaborators

open BigOperators

namespace C05S03


/-
Infinitely Many Primes
Let us continue our exploration of induction and recursion with another mathematical standard: a proof that there are infinitely many primes.

One way to formulate this is as the statement that for every natural number n, there is a prime number p greater than n.

To prove this, let p be any prime factor of n!+1
. If p is less than or equal to n, it divides n!.
. Since it also divides n!+1, it divides 1, a contradiction.
. Hence p is greater than

To formalize that proof, we need to show that any number greater than or equal to 2 has a prime factor.

To do that, we will need to show that any natural number that is not equal to 0 or 1 is greater-than or equal to 2.
And this brings us to a quirky feature of formalization: it is often trivial statements like this that are among the most annoying to formalize.

Here we consider a few ways to do it.

To start with, we can use the cases tactic and the fact that the successor function respects the ordering on the natural numbers.

-/

theorem two_le {m : ℕ} (h0 : m ≠ 0) (h1 : m ≠ 1) : 2 ≤ m := by
  cases m; contradiction --not zero
  case succ m => --not succ zero (1)
    cases m; contradiction
    repeat apply Nat.succ_le_succ
    apply zero_le

/-
Another strategy is to use the tactic interval_cases, which automatically splits the goal into cases when the variable in question is
contained in an interval of natural numbers or integers.

Remember that you can hover over it to see its documentation.
-/
example {m : ℕ} (h0 : m ≠ 0) (h1 : m ≠ 1) : 2 ≤ m := by
  by_contra h
  push_neg at h
  interval_cases m <;> contradiction --interval cases finds atoms for m < 2 which are 0 and 1; each leading to a contradiction
/-
Recall that the semicolon after interval_cases m means that the next tactic is applied to each of the cases that it generates.

Yet another option is to use the tactic decide, which tries to find a decision procedure to solve the problem.

Lean knows that you can decide the truth value of a statement that begins with a bounded quantifier ∀ x, x < n → ... or ∃ x, x < n ∧ ...
by deciding each of the finitely many instances.
-/



example {m : ℕ} (h0 : m ≠ 0) (h1 : m ≠ 1) : 2 ≤ m := by
  by_contra h
  push_neg at h
  revert h0 h1
  revert h m --decide on ∀ {m : ℕ}, m < 2 → m ≠ 0 → m ≠ 1 → False (needs decideable eq)
  decide

theorem exists_prime_factor {n : Nat} (h : 2 ≤ n) : ∃ p : Nat, p.Prime ∧ p ∣ n := by
  by_cases np : n.Prime
  · use n, np
  induction' n using Nat.strong_induction_on with n ih
  rw [Nat.prime_def_lt] at np
  push_neg at np
  rcases np h with ⟨m, mltn, mdvdn, mne1⟩ --if n is not prime, it has a factor m
  have : m ≠ 0 := by
    intro mz
    rw [mz, zero_dvd_iff] at mdvdn --get n=0, from 0|n
    linarith --get false from n= 0 m = 0 but n < m
  have mgt2 : 2 ≤ m := two_le this mne1 --this factor is larger than 2
  by_cases mp : m.Prime --if the factor is prime we are done
  · use m, mp
  · rcases ih m mltn mgt2 mp with ⟨p, pp, pdvd⟩ --if not, then since its less than n by ih it must have a prime factor p
    use p, pp
    apply pdvd.trans mdvdn --use transitivity to get a prime factor of n

set_option pp.rawOnError true

#check Nat.lt_succ_self
#check Nat.dvd_factorial
#check Nat.Prime.pos
#check Nat.dvd_sub'
#check Nat.le_of_dvd
#check Nat.dvd_one.mp
#check Nat.Prime.ne_one



theorem primes_infinite : ∀ n, ∃ p > n, Nat.Prime p := by
    intro n
    have : 2 ≤ Nat.factorial (n + 1) + 1 := by
      induction' n with j ih
      . simp
      . have: (j+1+1).factorial = (j+1).factorial*(j+1+1) := by simp [Nat.factorial,Nat.mul_comm]
        rw [this,mul_add,mul_one]
        apply le_trans ih
        . simp
    rcases exists_prime_factor this with ⟨p, pp, pdvd⟩ --getting the prime factor out of Nat.factorial (n + 1) + 1
    refine ⟨p, ?_, pp⟩ --use this prime factor of Nat.factorial (n + 1) + 1; leaving the goal of p > n
    show p > n
    by_contra ple
    push_neg at ple
    have : p ∣ Nat.factorial (n + 1) := by
      apply Nat.dvd_factorial
      . exact (Nat.Prime.pos pp)
      . linarith
    have : p ∣ 1 := by
      have t1: 1 = (Nat.factorial (n + 1) + 1) - Nat.factorial (n + 1) := by simp_arith
      rw [t1]
      apply Nat.dvd_sub'
      . exact pdvd
      . exact this
    show False
    have t2: p = 1 := Nat.dvd_one.mp this
    have t3: p ≠ 1 := Nat.Prime.ne_one pp
    contradiction


open Finset

section
variable {α : Type*} [DecidableEq α] (r s t : Finset α)


#check mem_inter

example : r ∩ (s ∪ t) ⊆ r ∩ s ∪ r ∩ t := by
  rw [subset_iff]
  intro x
  rw [mem_inter, mem_union, mem_union, mem_inter, mem_inter]
  tauto

example : r ∩ (s ∪ t) ⊆ r ∩ s ∪ r ∩ t := by
  simp [subset_iff]
  intro x
  tauto

example : r ∩ s ∪ r ∩ t ⊆ r ∩ (s ∪ t) := by
  simp [subset_iff]
  intro x
  tauto

example : r ∩ s ∪ r ∩ t = r ∩ (s ∪ t) := by
  ext x
  simp
  tauto

end

section
variable {α : Type*} [DecidableEq α] (r s t : Finset α)

/-
We have used a new trick: the tauto tactic (and a strengthened version, tauto!, which uses classical logic)
can be used to dispense with propositional tautologies.

See if you can use these methods to prove the two examples below.
-/

example : (r ∪ s) ∩ (r ∪ t) = r ∪ s ∩ t := by
  ext x
  repeat simp [mem_inter,mem_union]
  tauto

#check Finset.div_def

example : (r \ s) \ t = r \ (s ∪ t) := by
  ext x
  repeat simp [div_def]
  tauto

end

example (s : Finset ℕ) (n : ℕ) (h : n ∈ s) : n ∣ ∏ i in s, i :=
  Finset.dvd_prod_of_mem _ h

#check Nat.dvd_one.mp
#check Nat.Prime.dvd_iff_eq
#check Nat.Prime.two_le

theorem _root_.Nat.Prime.eq_of_dvd_of_prime {p q : ℕ}
      (prime_p : Nat.Prime p) (prime_q : Nat.Prime q) (h : p ∣ q) :
    p = q := by
    have t1:_ := Nat.Prime.two_le prime_p
    have t2:_ := Nat.Prime.two_le prime_q
    have t4: p ≠ 1 := by linarith
    have t5: q ≠ 1 := by linarith
    have := (Nat.Prime.dvd_iff_eq prime_q t4).mp h
    simp [this]

#check Finset.prod_insert
-- ∀ n ∈ s, Nat.Prime n
-- a ∉ s → ∏ x ∈ insert a s, f x = f a * ∏ x ∈ s, f x
theorem mem_of_dvd_prod_primes {s : Finset ℕ} {p : ℕ} (prime_p : p.Prime) :
    (∀ n ∈ s, Nat.Prime n) → (p ∣ ∏ n in s, n) → p ∈ s := by
  intro h₀ h₁
  induction' s using Finset.induction_on with a s ans ih
  · simp at h₁
    linarith [prime_p.two_le]
  simp [Finset.prod_insert ans, prime_p.dvd_mul] at h₀ h₁
  rw [mem_insert]
  rcases h₁ with h₁₁|h₁₂
  . apply Or.inl
    . apply _root_.Nat.Prime.eq_of_dvd_of_prime
      . exact prime_p
      . exact h₀.1
      . exact h₁₁
  . apply Or.inr
    apply ih
    . exact h₀.2
    . exact h₁₂


-- theorem mem_of_dvd_prod_primes' {s : Finset ℕ} {p : ℕ} (prime_p : p.Prime) :
--     (∀ n ∈ s, Nat.Prime n) → (p ∣ ∏ n in s, n) → p ∈ s := by
--     intro h₀ h₁
--     /-
--     h₀ : ∀ n ∈ s, Nat.Prime n
--     h₁ : p ∣ ∏ n ∈ s, n
--     ⊢ p ∈ s
--     -/
--     induction' s using Finset.induction_on with a s ans ih
--     /-
--     a : ℕ
--     s : Finset ℕ
--     ans : a ∉ s
--     ih : (∀ n ∈ s, Nat.Prime n) → p ∣ ∏ n ∈ s, n → p ∈ s
--     -/
--     · simp at h₁
--       linarith [prime_p.two_le]
--     . simp [Finset.prod_insert ans] at h₁
--       --  ∀ n ∈ insert a s, Nat.Prime n
--       simp [prime_p.dvd_mul] at h₀ h₁
--       rw [mem_insert]
--       rcases h₁ with h₁₁|h₁₂
--       . apply Or.inl
--         . apply _root_.Nat.Prime.eq_of_dvd_of_prime
--           . exact prime_p
--           . exact h₀.1
--           . exact h₁₁
--       . apply Or.inr
--         apply ih
--         . exact h₀.2
--         . exact h₁₂


example (s : Finset ℕ) (x : ℕ) : x ∈ s.filter Nat.Prime ↔ x ∈ s ∧ x.Prime :=
  mem_filter

#check Finset.one_le_prod'
#check Finset.dvd_prod_of_mem
#check Nat.Prime.one_le
#check Nat.add_le_add
#check Nat.two_pow_succ 0

theorem primes_infinite' : ∀ s : Finset Nat, ∃ p, Nat.Prime p ∧ p ∉ s := by
    intro s --Finset of Nat, a list of Naturals
    by_contra h
    push_neg at h
    set s' := s.filter Nat.Prime with s'_def --the set of primes in s
    have mem_s' : ∀ {n : ℕ}, n ∈ s' ↔ n.Prime := by
      intro n
      simp [s'_def]
      apply h
    have : 2 ≤ (∏ i in s', i) + 1 := by
      have h₁: (1 ≤ ∏ i ∈ s', i) := by
        apply Finset.one_le_prod'
        intro i his
        simp [s'_def] at his
        exact Nat.Prime.one_le (his.2)
      calc 2 ≤ 1+1 := by simp_arith
      _ ≤ (∏ i in s', i) + 1 := Nat.add_le_add h₁ (le_refl 1)
    rcases exists_prime_factor this with ⟨p, pp, pdvd⟩
    have : p ∣ ∏ i in s', i := --since p is prime, it must be in s' and hence divide the product
    by have t₁: p ∈ s' := mem_s'.mpr pp; exact Finset.dvd_prod_of_mem (fun (x:ℕ) ↦ x) t₁
    have : p ∣ 1 := by --since it divides (∏ i in s', i) + 1 and (∏ i in s', i) it must divide 1
      convert Nat.dvd_sub' pdvd this
      simp
    show False
    have c₁: p = 1 := Nat.dvd_one.mp this
    have c₂: p ≥ 2 := Nat.Prime.two_le pp
    linarith

section

theorem bounded_of_ex_finset (Q : ℕ → Prop) :
    (∃ s : Finset ℕ, ∀ k, Q k → k ∈ s) → ∃ n, ∀ k, Q k → k < n := by --if there exists a Finset with all the predicate Q, then there is an n larger that k for any Q k
      rintro ⟨s, hs⟩
      use s.sup id + 1
      intro k Qk --intro for ∀k, Qk ( Q k) need k < n (s.sup id + 1)
      apply Nat.lt_succ_of_le --need id k ≤ s.sup id
      show id k ≤ s.sup id
      apply le_sup (hs k Qk) --k ∈ s (and hence ≤ s.sup id)

theorem ex_finset_of_bounded (Q : ℕ → Prop) [DecidablePred Q] :
    (∃ n, ∀ k, Q k → k ≤ n) → ∃ s : Finset ℕ, ∀ k, Q k ↔ k ∈ s := by
  intro h
  rcases h with ⟨n, hn⟩
  use (range (n + 1)).filter Q
  intro k
  simp [Nat.lt_succ_iff]
  exact hn k

example : 27 % 4 = 3 := by norm_num

example (n : ℕ) : (4 * n + 3) % 4 = 3 := by
  rw [add_comm, Nat.add_mul_mod_self_left]

theorem mod_4_eq_3_or_mod_4_eq_3 {m n : ℕ} (h : m * n % 4 = 3) : m % 4 = 3 ∨ n % 4 = 3 := by
  revert h
  rw [Nat.mul_mod]
  have : m % 4 < 4 := Nat.mod_lt m (by norm_num)
  interval_cases m % 4 <;> simp [-Nat.mul_mod_mod]
  have : n % 4 < 4 := Nat.mod_lt n (by norm_num)
  interval_cases n % 4 <;> simp

theorem two_le_of_mod_4_eq_3 {n : ℕ} (h : n % 4 = 3) : 2 ≤ n := by
  apply two_le <;>
    · intro neq
      rw [neq] at h
      norm_num at h
#check Nat.div_dvd_of_dvd

theorem aux {m n : ℕ} (h₀ : m ∣ n) (h₁ : 2 ≤ m) (h₂ : m < n) : n / m ∣ n ∧ n / m < n := by
  constructor
  . exact Nat.div_dvd_of_dvd h₀
  . have := Nat.div_dvd_of_dvd h₀
    apply Nat.div_lt_self <;> linarith

#check Nat.div_lt_self
theorem exists_prime_factor_mod_4_eq_3 {n : Nat} (h : n % 4 = 3) :
    ∃ p : Nat, p.Prime ∧ p ∣ n ∧ p % 4 = 3 := by
  by_cases np : n.Prime --if n is prime, use n and we are done
  · use n
  --given n is not prime, strong induction on n
  induction' n using Nat.strong_induction_on with n ih
  rw [Nat.prime_def_lt] at np
  push_neg at np
  rcases np (two_le_of_mod_4_eq_3 h) with ⟨m, mltn, mdvdn, mne1⟩
  have mge2 : 2 ≤ m := by
    apply two_le _ mne1
    intro mz
    rw [mz, zero_dvd_iff] at mdvdn
    linarith
  have neq : m * (n / m) = n := Nat.mul_div_cancel' mdvdn
  have : m % 4 = 3 ∨ n / m % 4 = 3 := by
    apply mod_4_eq_3_or_mod_4_eq_3
    rw [neq, h]
  rcases this with h1 | h1
  . by_cases nm: Nat.Prime m
    . use m
    . have := ih m mltn h1 nm
      rcases this with ⟨p,hp⟩
      use p
      have := dvd_trans hp.2.1 mdvdn
      exact ⟨hp.1,this,hp.2.2⟩
  . let k:= n / m
    by_cases npk: Nat.Prime k
    . use k
      constructor
      . exact npk
      constructor
      . simp [k]
        use m
        rw [mul_comm]
        simp [neq]
      . simp [h1]
    . have := ih k (by simp [k];apply Nat.div_lt_self<;>linarith) (by simp [h1]) npk
      rcases this with ⟨p,hp⟩
      use p
      constructor
      . exact hp.1
      . constructor
        . have: k ∣ n := by simp [k]; exact (aux mdvdn mge2 mltn).1
          exact dvd_trans hp.2.1 this
        . exact hp.2.2

example (m n : ℕ) (s : Finset ℕ) (h : m ∈ erase s n) : m ≠ n ∧ m ∈ s := by
  rwa [mem_erase] at h

example (m n : ℕ) (s : Finset ℕ) (h : m ∈ erase s n) : m ≠ n ∧ m ∈ s := by
  simp at h
  assumption
#check Finset.prod_insert
#check Nat.add_mod
#check Nat.mod_mul_mod
#check Nat.mul_left_comm
#check Nat.mod_self
#check Nat.dvd_add_iff_left
#check Nat.mul_mod
#check Nat.mul_mod_left
#check Nat.dvd_add_iff_left --we have k | m + n
#check Nat.Prime.dvd_mul
#check mem_of_dvd_prod_primes -- (∀ n ∈ s, Nat.Prime n) → p ∣ ∏ n ∈ s, n → p ∈ s
--#check Nat.dvd_mod
#check Nat.dvd_sub'
#check Finset.dvd_prod_of_mem
#check Nat.Prime.dvd_mul
theorem primes_mod_4_eq_3_infinite : ∀ n, ∃ p > n, Nat.Prime p ∧ p % 4 = 3 := by
  by_contra h
  push_neg at h
  rcases h with ⟨n, hn⟩
  have : ∃ s : Finset Nat, ∀ p : ℕ, p.Prime ∧ p % 4 = 3 ↔ p ∈ s := by --creating the finset of all such primes
    apply ex_finset_of_bounded
    use n
    contrapose! hn
    rcases hn with ⟨p, ⟨pp, p4⟩, pltn⟩
    exact ⟨p, pltn, pp, p4⟩
  rcases this with ⟨s, hs⟩
  have h₁ : ((4 * ∏ i in erase s 3, i) + 3) % 4 = 3 := by
    induction' (erase s 3) using Finset.induction_on with s h1 h2 ih
    . simp
    . rw [Finset.prod_insert]
      rw [←mul_assoc,mul_comm 4]
      rw [mul_assoc,Nat.add_mod]
      rw [Nat.mul_mod]
      have : s % 4 < 4 := Nat.mod_lt s (by norm_num)
      interval_cases s%4 <;> simp
      exact h2
  rcases exists_prime_factor_mod_4_eq_3 h₁ with ⟨p, pp, pdvd, p4eq⟩
  have ps : p ∈ s := by
    exact (hs p).mp (And.intro pp p4eq)
  have pne3 : p ≠ 3 := by
    intro peq3
    rw [peq3] at pdvd
    have t0:3 ∣ 3 := by simp
    have t1:_ := (Nat.dvd_add_iff_left t0 (n:=3) (m:=4 * ∏ i ∈ s.erase 3, i)).mpr pdvd
    have t2:_ := (Nat.Prime.dvd_mul (Nat.prime_three)).mp t1
    apply t2.elim
    . intro hc; contradiction
    . have t3: ∀n ∈ s.erase 3, Nat.Prime n := by
       intro n nis
       rw [Finset.mem_erase] at nis
       exact ((hs n).mpr nis.2).1
      have t4:_ := mem_of_dvd_prod_primes (Nat.prime_three) t3
      intro k
      have := t4 k
      rw [Finset.mem_erase] at this
      exact this.1 (Eq.refl 3)
  have : p ∣ 4 * ∏ i in erase s 3, i := by
    have hps: p ∈ erase s 3 := by
     rw [Finset.mem_erase]
     exact And.intro pne3 ps
    have t5:_ := Finset.dvd_prod_of_mem (id) (s:=erase s 3) hps (β:=Nat)
    simp at t5
    have t6:_ := (Nat.Prime.dvd_mul pp (m:=4) (n:= ∏ i ∈ s.erase 3, i)).mpr
    exact t6 (Or.inr t5)
  have : p ∣ 3 := by
    have t7:3 = 4 * ∏ i ∈ s.erase 3, i + 3 - 4 * ∏ i ∈ s.erase 3, i := by simp
    rw [t7]
    apply Nat.dvd_sub' (m:=4 * ∏ i ∈ s.erase 3, i + 3) (n:=4 * ∏ i ∈ s.erase 3, i)
    . exact pdvd
    . exact this
  have : p = 3 := by
    apply _root_.Nat.Prime.eq_of_dvd_of_prime
    . exact pp
    . exact Nat.prime_three
    . exact this
  contradiction

#check mem_of_dvd_prod_primes
#check Nat.dvd_sub'
#check _root_.Nat.Prime.eq_of_dvd_of_prime
end
